//! ANL checker, typed core interchange, reference evaluator, and native compiler.
//! Formal proof scope is recorded separately under `formal/`.
pub mod bounded;
pub mod codegen;
pub mod core;
pub mod diagnostic;
pub mod eval;
pub mod memory;
#[cfg(feature = "memory-evidence")]
pub mod memory_evidence;
mod mir;
mod modules;
mod resolve;
mod syntax;
pub mod types;
pub mod verify;

pub const MAX_SOURCE_BYTES: usize = 1_048_576;
pub const MAX_PROGRAM_BYTES: usize = 8_388_608;
pub const MAX_MODULES: usize = 128;
pub const MAX_MODULE_DEPTH: usize = 32;
pub const MAX_TOKENS: usize = 100_000;
pub const MAX_DEPTH: usize = 128;
pub const MAX_EVAL_DEPTH: usize = 256;
pub const DEFAULT_FUEL: u64 = 100_000;
pub const MAX_FUEL: u64 = 1_000_000_000;

pub fn compile(source: &str) -> Result<types::Program, diagnostic::Diagnostic> {
    let file = syntax::parse(source, 0)?;
    if let Some(module) = file.modules.first() {
        return Err(diagnostic::Diagnostic::new(
            module.span,
            "module declarations require compile_file(path); compile(source) does not read the filesystem",
        ));
    }
    resolve::check(
        vec![resolve::Module {
            functions: file.functions,
            imports: Vec::new(),
        }],
        Default::default(),
    )
}

/// Read and check a local source file and its complete, bounded module graph.
/// The invocation path selects `.apl` imports for an explicit legacy `.apl`
/// root, and `.anl` imports otherwise, before symlink resolution.
/// Imports resolve relative to each declaring file's canonical directory.
pub fn compile_file(
    path: impl AsRef<std::path::Path>,
) -> Result<types::Program, diagnostic::Diagnostic> {
    modules::compile_file(path.as_ref())
}
