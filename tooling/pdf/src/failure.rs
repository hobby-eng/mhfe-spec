use std::fmt;

/// A build refusal carrying its stage and a diagnostic for public document inputs.
#[derive(Debug)]
pub(crate) struct Failure {
    stage: &'static str,
    message: String,
}

impl Failure {
    pub(crate) fn new(stage: &'static str, message: impl Into<String>) -> Self {
        Self {
            stage,
            message: message.into(),
        }
    }
}

impl fmt::Display for Failure {
    fn fmt(&self, output: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(output, "{}: {}", self.stage, self.message)
    }
}

impl std::error::Error for Failure {}

impl From<std::io::Error> for Failure {
    fn from(error: std::io::Error) -> Self {
        Self::new("PDF-IO", error.to_string())
    }
}

impl From<serde_json::Error> for Failure {
    fn from(error: serde_json::Error) -> Self {
        Self::new("PDF-JSON", error.to_string())
    }
}

impl From<regex::Error> for Failure {
    fn from(error: regex::Error) -> Self {
        Self::new("PDF-PATTERN", error.to_string())
    }
}

pub(crate) type Result<T> = std::result::Result<T, Failure>;
