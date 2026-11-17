//! Explicit, bounded local source loading. Each file retains its own namespace.
use crate::{
    MAX_MODULE_DEPTH, MAX_MODULES, MAX_PROGRAM_BYTES, MAX_SOURCE_BYTES,
    diagnostic::{Diagnostic, SourceFile, Span},
    resolve::{self, Import, Module},
    syntax,
    types::Program,
};
use std::{
    collections::HashMap,
    fs::{self, File},
    io::Read,
    path::{Path, PathBuf},
    sync::Arc,
};

pub(crate) fn compile_file(path: &Path) -> Result<Program, Diagnostic> {
    let mut loader = Loader::default();
    let result = loader.load(path, Span::default());
    let sources = Arc::new(loader.sources);
    result.map_err(|error| error.with_sources(sources.clone()))?;
    let modules = loader.modules.into_iter().map(Option::unwrap).collect();
    resolve::check(modules, sources.clone()).map_err(|error| error.with_sources(sources))
}

#[derive(Default)]
struct Loader {
    paths: HashMap<PathBuf, usize>,
    sources: Vec<SourceFile>,
    modules: Vec<Option<Module>>,
    active: Vec<usize>,
    bytes: usize,
}
impl Loader {
    fn load(&mut self, requested: &Path, import_span: Span) -> Result<usize, Diagnostic> {
        let path = requested
            .canonicalize()
            .map_err(|error| io_error(import_span, requested, error))?;
        if let Some(&id) = self.paths.get(&path) {
            if let Some(start) = self.active.iter().position(|&active| active == id) {
                let chain = self.active[start..]
                    .iter()
                    .copied()
                    .chain([id])
                    .map(|id| self.sources[id].path.display().to_string())
                    .collect::<Vec<_>>()
                    .join(" -> ");
                return Err(Diagnostic::new(
                    import_span,
                    format!("module import cycle: {chain}; remove a cyclic mod declaration"),
                ));
            }
            return Ok(id);
        }
        if self.active.len() >= MAX_MODULE_DEPTH {
            return Err(Diagnostic::resource(
                import_span,
                "module import depth exceeds 32 files",
            ));
        }
        if self.sources.len() >= MAX_MODULES {
            return Err(Diagnostic::resource(
                import_span,
                "program exceeds 128 source modules",
            ));
        }
        let metadata = fs::metadata(&path).map_err(|error| io_error(import_span, &path, error))?;
        if !metadata.is_file() {
            let mut error = Diagnostic::new(
                import_span,
                format!("source {} is not a regular file", path.display()),
            );
            error.infrastructure = true;
            return Err(error);
        }
        let file = File::open(&path).map_err(|error| io_error(import_span, &path, error))?;
        let metadata = file
            .metadata()
            .map_err(|error| io_error(import_span, &path, error))?;
        #[cfg(unix)]
        let identity = {
            use std::os::unix::fs::MetadataExt;
            let identity = (metadata.dev(), metadata.ino());
            if let Some(previous) = self
                .sources
                .iter()
                .find(|source| source.identity == identity)
            {
                return Err(Diagnostic::new(
                    import_span,
                    format!(
                        "ambiguous module identity: {} and {} are hardlinks; use a single canonical source path",
                        previous.path.display(),
                        path.display()
                    ),
                ));
            }
            identity
        };
        let mut bytes = Vec::new();
        file.take(MAX_SOURCE_BYTES as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| io_error(import_span, &path, error))?;
        if bytes.len() > MAX_SOURCE_BYTES {
            return Err(Diagnostic::resource(
                import_span,
                format!("source {} exceeds 1048576 bytes", path.display()),
            ));
        }
        self.bytes += bytes.len();
        if self.bytes > MAX_PROGRAM_BYTES {
            return Err(Diagnostic::resource(
                import_span,
                "program source exceeds 8388608 bytes",
            ));
        }
        let id = self.sources.len();
        let text = match String::from_utf8(bytes) {
            Ok(text) => text,
            Err(error) => {
                let start = error.utf8_error().valid_up_to();
                self.sources.push(SourceFile {
                    path,
                    text: String::from_utf8_lossy(&error.as_bytes()[..start]).into_owned(),
                    #[cfg(unix)]
                    identity,
                });
                return Err(Diagnostic::new(
                    Span {
                        source_id: id,
                        start,
                        end: start,
                    },
                    "input is not valid UTF-8",
                ));
            }
        };
        self.sources.push(SourceFile {
            path: path.clone(),
            text,
            #[cfg(unix)]
            identity,
        });
        self.paths.insert(path.clone(), id);
        self.modules.push(None);
        self.active.push(id);
        let file = syntax::parse(&self.sources[id].text, id)?;
        let mut imports = Vec::new();
        for module in file.modules {
            let target = path
                .parent()
                .expect("canonical file has a parent")
                .join(format!("{}.apl", module.name));
            let target = self.load(&target, module.span)?;
            imports.push(Import {
                name: module.name,
                target,
                public: module.public,
                span: module.span,
            });
        }
        self.modules[id] = Some(Module {
            functions: file.functions,
            imports,
        });
        self.active.pop();
        Ok(id)
    }
}

fn io_error(span: Span, path: &Path, error: std::io::Error) -> Diagnostic {
    let mut diagnostic = Diagnostic::new(
        span,
        format!("cannot read source {}: {error}", path.display()),
    );
    diagnostic.infrastructure = true;
    diagnostic
}
