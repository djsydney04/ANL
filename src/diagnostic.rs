use std::{fmt, path::PathBuf, sync::Arc};

const MAX_DIAGNOSTIC_BYTES: usize = 8192;
fn bounded(mut text: String) -> String {
    if text.len() > MAX_DIAGNOSTIC_BYTES {
        let suffix = " [diagnostic truncated]";
        let mut end = MAX_DIAGNOSTIC_BYTES - suffix.len();
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        text.truncate(end);
        text.push_str(suffix);
    }
    text
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Span {
    /// Index in the program's source map; byte offsets remain local to this file.
    pub source_id: usize,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn join(self, other: Self) -> Self {
        Self {
            source_id: self.source_id,
            start: self.start,
            end: other.end,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceFile {
    pub path: PathBuf,
    pub text: String,
    #[cfg(unix)]
    pub identity: (u64, u64),
}

pub(crate) type Sources = Arc<Vec<SourceFile>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    pub span: Span,
    pub related: Option<(Span, String)>,
    pub resource_limit: bool,
    pub infrastructure: bool,
    pub(crate) sources: Sources,
}

impl Diagnostic {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            message: bounded(message.into()),
            span,
            related: None,
            resource_limit: false,
            infrastructure: false,
            sources: Arc::default(),
        }
    }

    pub fn resource(span: Span, message: impl Into<String>) -> Self {
        Self {
            resource_limit: true,
            ..Self::new(span, message)
        }
    }

    pub fn related(mut self, span: Span, message: impl Into<String>) -> Self {
        self.related = Some((span, bounded(message.into())));
        self
    }

    pub(crate) fn with_sources(mut self, sources: Sources) -> Self {
        self.sources = sources;
        self
    }

    pub fn render(&self, filename: &str, source: &str) -> String {
        fn position(source: &str, offset: usize) -> (usize, usize) {
            let mut offset = offset.min(source.len());
            while !source.is_char_boundary(offset) {
                offset -= 1;
            }
            let prefix = &source[..offset];
            (
                prefix.bytes().filter(|b| *b == b'\n').count() + 1,
                prefix.rsplit('\n').next().unwrap_or("").chars().count() + 1,
            )
        }
        let location = |span: Span| {
            if let Some(file) = self.sources.get(span.source_id) {
                let (line, column) = position(&file.text, span.start);
                format!("{}:{line}:{column}", file.path.display())
            } else {
                let (line, column) = position(source, span.start);
                format!("{filename}:{line}:{column}")
            }
        };
        let kind = if self.resource_limit {
            "resource_limit"
        } else {
            "error"
        };
        let mut text = format!("{}: {kind}: {}", location(self.span), self.message);
        if let Some((span, message)) = &self.related {
            text.push_str(&format!("\n{}: note: {message}", location(*span)));
        }
        bounded(text)
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Diagnostic {}
