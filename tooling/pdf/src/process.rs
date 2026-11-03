use crate::failure::{Failure, Result};
use crate::install::{Manifest, executable_path};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::{fs, io::Write};

const PROCESS_SECONDS: &str = "600s";
const PROCESS_JOBS: &str = "2";

/// Owns the pinned converter executables and their subprocess boundary.
pub(crate) struct Toolchain {
    pub(crate) pandoc: PathBuf,
    pub(crate) typst: PathBuf,
    pub(crate) font_dir: crate::fonts::Prepared,
    /// The PDF creation date as a Unix timestamp; fixed dates give reproducible bytes.
    pub(crate) created: Option<String>,
}

impl Toolchain {
    pub(crate) fn discover() -> Result<Self> {
        let tools = Self {
            font_dir: crate::fonts::Prepared::new(&crate::fonts::directory()?)?,
            pandoc: executable_path(
                std::env::var_os("MHFE_PANDOC")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| "pandoc".into()),
            )?,
            typst: executable_path(
                std::env::var_os("MHFE_TYPST")
                    .map(PathBuf::from)
                    .unwrap_or_else(|| "typst".into()),
            )?,
            created: None,
        };
        let manifest = Manifest::read()?;
        for tool in manifest.tools {
            let path = match tool.name.as_str() {
                "pandoc" => &tools.pandoc,
                "typst" => &tools.typst,
                _ => return Err(Failure::new("PDF-TOOLS", "Unknown pinned tool")),
            };
            if file_digest(path)? != tool.binary_sha256 {
                return Err(Failure::new(
                    "PDF-TOOLS",
                    format!("{} binary does not match its pinned SHA-256", tool.name),
                ));
            }
            let expected = format!("{} {}", tool.name, tool.version);
            let version = run(path, ["--version"], None, None)?;
            if !String::from_utf8_lossy(&version)
                .lines()
                .next()
                .is_some_and(|line| line == expected || line.starts_with(&format!("{expected} ")))
            {
                return Err(Failure::new(
                    "PDF-TOOLS",
                    format!("Expected {expected}; install the pinned document toolchain"),
                ));
            }
        }
        Ok(tools)
    }

    pub(crate) fn pandoc(&self, args: &[&str], input: &[u8]) -> Result<Vec<u8>> {
        converted(&self.pandoc, args, None, Some(input))
    }

    pub(crate) fn typst(&self, args: &[&OsStr], root: &Path) -> Result<Vec<u8>> {
        let (command, rest) = args
            .split_first()
            .ok_or_else(|| Failure::new("PDF-PROCESS", "Missing Typst command"))?;
        let created = self
            .created
            .as_deref()
            .filter(|_| *command == "compile")
            .map(|date| [OsStr::new("--creation-timestamp"), OsStr::new(date)]);
        let arguments = std::iter::once(*command)
            .chain([
                OsStr::new("--jobs"),
                OsStr::new(PROCESS_JOBS),
                OsStr::new("--font-path"),
                self.font_dir.path().as_os_str(),
            ])
            .chain(created.into_iter().flatten())
            .chain(rest.iter().copied());
        converted(&self.typst, arguments, Some(root), None)
    }
}

pub(crate) fn run<I, S>(
    program: impl AsRef<OsStr>,
    args: I,
    directory: Option<&Path>,
    input: Option<&[u8]>,
) -> Result<Vec<u8>>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    Ok(execute(program, args, directory, input)?.stdout)
}

fn converted<I, S>(
    program: impl AsRef<OsStr>,
    args: I,
    directory: Option<&Path>,
    input: Option<&[u8]>,
) -> Result<Vec<u8>>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let result = execute(program, args, directory, input)?;
    let diagnostic = String::from_utf8_lossy(&result.stderr);
    if diagnostic.to_ascii_lowercase().contains("warning:") || diagnostic.contains("[WARNING]") {
        return Err(Failure::new("PDF-WARNING", diagnostic.to_string()));
    }
    Ok(result.stdout)
}

fn execute<I, S>(
    program: impl AsRef<OsStr>,
    args: I,
    directory: Option<&Path>,
    input: Option<&[u8]>,
) -> Result<Output>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut command = Command::new("timeout");
    command.args(["--signal=TERM", "--kill-after=5s", PROCESS_SECONDS]);
    command
        .arg(program)
        .args(args)
        .env("RAYON_NUM_THREADS", PROCESS_JOBS);
    if let Some(directory) = directory {
        command.current_dir(directory);
    }
    let mut child = command
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    if let Some(input) = input {
        child
            .stdin
            .take()
            .ok_or_else(|| Failure::new("PDF-PROCESS", "Subprocess input pipe is unavailable"))?
            .write_all(input)?;
    }
    let result = child.wait_with_output()?;
    if !result.status.success() {
        let diagnostic: String = String::from_utf8_lossy(&result.stderr)
            .chars()
            .take(8000)
            .collect();
        return Err(Failure::new(
            "PDF-PROCESS",
            format!("Subprocess {} failed: {diagnostic}", result.status),
        ));
    }
    Ok(result)
}

pub(crate) fn text(bytes: Vec<u8>) -> Result<String> {
    String::from_utf8(bytes)
        .map_err(|_| Failure::new("PDF-UTF8", "A converter returned invalid UTF-8"))
}

pub(crate) fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

pub(crate) fn file_digest(path: &Path) -> Result<String> {
    Ok(digest(&fs::read(path)?))
}

pub(crate) fn json_file(path: &Path, value: &impl Serialize) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value)?;
    bytes.push(b'\n');
    fs::write(path, bytes)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scopes_fatal_warnings_to_converters_not_successful_download_retries() {
        let command = ["-c", "printf 'Warning: transient retry\\n' >&2; printf ok"];
        assert_eq!(run("bash", command, None, None).unwrap(), b"ok");
        let error = converted("bash", command, None, None).unwrap_err();
        assert!(error.to_string().starts_with("PDF-WARNING:"));
        let pandoc = ["-c", "printf '[WARNING] bad formula\\n' >&2; printf ok"];
        assert!(converted("bash", pandoc, None, None).is_err());
    }
}
