//! Byte-bounded artifact construction. Callers publish only a finished buffer.
use std::{fmt, io};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OutputError {
    ResourceLimit(&'static str),
    Infrastructure(String),
}
impl fmt::Display for OutputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ResourceLimit(reason) => f.write_str(reason),
            Self::Infrastructure(reason) => f.write_str(reason),
        }
    }
}
impl std::error::Error for OutputError {}
impl From<String> for OutputError {
    fn from(value: String) -> Self {
        Self::Infrastructure(value)
    }
}
impl From<&str> for OutputError {
    fn from(value: &str) -> Self {
        Self::Infrastructure(value.into())
    }
}

pub(crate) struct Buffer {
    text: String,
    limit: Option<usize>,
    reason: &'static str,
    exhausted: bool,
}
impl Buffer {
    pub(crate) fn new(limit: Option<usize>, reason: &'static str) -> Self {
        Self {
            text: String::new(),
            limit,
            reason,
            exhausted: false,
        }
    }
    fn append(&mut self, text: &str) -> Result<(), ()> {
        if self.exhausted
            || self
                .text
                .len()
                .checked_add(text.len())
                .is_none_or(|n| self.limit.is_some_and(|limit| n > limit))
        {
            self.exhausted = true;
            return Err(());
        }
        self.text.push_str(text);
        Ok(())
    }
    pub(crate) fn finish(self) -> Result<String, OutputError> {
        if self.exhausted {
            Err(OutputError::ResourceLimit(self.reason))
        } else {
            Ok(self.text)
        }
    }
    pub(crate) fn exhausted(&self) -> bool {
        self.exhausted
    }
}
impl fmt::Write for Buffer {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.append(text).map_err(|_| fmt::Error)
    }
}
impl io::Write for Buffer {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let text = std::str::from_utf8(bytes).map_err(io::Error::other)?;
        self.append(text)
            .map_err(|_| io::Error::other(self.reason))?;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn limits_count_utf8_bytes_and_never_accept_a_partial_chunk() {
        for limit in [4, 5, 6] {
            let mut buffer = Buffer::new(Some(limit), "test cap");
            let result = fmt::Write::write_str(&mut buffer, "é猫");
            if limit < 5 {
                assert!(result.is_err());
                assert_eq!(buffer.text, "");
                assert_eq!(buffer.finish(), Err(OutputError::ResourceLimit("test cap")));
            } else {
                assert!(result.is_ok());
                assert_eq!(buffer.finish().unwrap().len(), 5);
            }
        }
        let mut buffer = Buffer::new(Some(2), "test cap");
        assert!(fmt::Write::write_str(&mut buffer, "é").is_ok());
        assert!(fmt::Write::write_str(&mut buffer, "a").is_err());
        assert!(fmt::Write::write_str(&mut buffer, "").is_err());
        assert_eq!(buffer.text, "é");
    }
}
