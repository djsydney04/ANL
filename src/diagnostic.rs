use std::fmt;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn join(self, other: Self) -> Self {
        Self {
            start: self.start,
            end: other.end,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    pub span: Span,
    pub related: Option<(Span, String)>,
    pub resource_limit: bool,
}

impl Diagnostic {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span,
            related: None,
            resource_limit: false,
        }
    }

    pub fn resource(span: Span, message: impl Into<String>) -> Self {
        Self {
            resource_limit: true,
            ..Self::new(span, message)
        }
    }

    pub fn related(mut self, span: Span, message: impl Into<String>) -> Self {
        self.related = Some((span, message.into()));
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
        let (line, column) = position(source, self.span.start);
        let kind = if self.resource_limit {
            "resource_limit"
        } else {
            "error"
        };
        let mut text = format!("{filename}:{line}:{column}: {kind}: {}", self.message);
        if let Some((span, message)) = &self.related {
            let (line, column) = position(source, span.start);
            text.push_str(&format!("\n{filename}:{line}:{column}: note: {message}"));
        }
        text
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl std::error::Error for Diagnostic {}
