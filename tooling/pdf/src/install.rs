use crate::failure::{Failure, Result};
use crate::process::{digest, file_digest, run};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Deserialize, Serialize)]
pub(crate) struct Manifest {
    pub(crate) platform: String,
    pub(crate) tools: Vec<ToolPin>,
}

#[derive(Deserialize, Serialize)]
pub(crate) struct ToolPin {
    pub(crate) name: String,
    pub(crate) version: String,
    archive_url: String,
    archive_sha256: String,
    pub(crate) binary_sha256: String,
    member: String,
}

impl Manifest {
    pub(crate) fn read() -> Result<Self> {
        Ok(serde_json::from_str(include_str!("../toolchain.json"))?)
    }

    pub(crate) fn install(&self, directory: &Path) -> Result<()> {
        if self.platform != "linux-x86_64"
            || std::env::consts::OS != "linux"
            || std::env::consts::ARCH != "x86_64"
        {
            return Err(Failure::new(
                "PDF-INSTALL",
                "The pinned tools currently support Linux x86-64",
            ));
        }
        fs::create_dir_all(directory)?;
        for tool in &self.tools {
            tool.install(directory)?;
        }
        Ok(())
    }
}

impl ToolPin {
    fn install(&self, directory: &Path) -> Result<()> {
        let target = directory.join(&self.name);
        if target.exists() {
            if file_digest(&target)? == self.binary_sha256 {
                return Ok(());
            }
            return Err(Failure::new(
                "PDF-INSTALL",
                format!(
                    "Existing {} does not match its pin; choose a separate tool directory",
                    self.name
                ),
            ));
        }
        let archive = directory.join(format!("{}-{}.tar", self.name, self.version));
        run(
            "curl",
            [
                "--fail",
                "--location",
                "--retry",
                "2",
                "--connect-timeout",
                "15",
                "--max-time",
                "180",
                "--output",
                archive
                    .to_str()
                    .ok_or_else(|| Failure::new("PDF-INSTALL", "Tool path is not UTF-8"))?,
                &self.archive_url,
            ],
            None,
            None,
        )?;
        if file_digest(&archive)? != self.archive_sha256 {
            return Err(Failure::new(
                "PDF-INSTALL",
                "Downloaded tool archive failed its checksum",
            ));
        }
        let bytes = run(
            "tar",
            [
                std::ffi::OsStr::new("-xOf"),
                archive.as_os_str(),
                std::ffi::OsStr::new(&self.member),
            ],
            None,
            None,
        )?;
        if digest(&bytes) != self.binary_sha256 {
            return Err(Failure::new(
                "PDF-INSTALL",
                "Extracted tool binary failed its checksum",
            ));
        }
        fs::write(&target, bytes)?;
        executable(&target)?;
        Ok(())
    }
}

#[cfg(unix)]
fn executable(path: &Path) -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(path, fs::Permissions::from_mode(0o755))?;
    Ok(())
}

#[cfg(not(unix))]
fn executable(_path: &Path) -> Result<()> {
    Err(Failure::new(
        "PDF-INSTALL",
        "This installer requires Unix file permissions",
    ))
}

pub(crate) fn executable_path(program: PathBuf) -> Result<PathBuf> {
    if program.components().count() > 1 || program.is_absolute() {
        return Ok(program.canonicalize()?);
    }
    let path =
        std::env::var_os("PATH").ok_or_else(|| Failure::new("PDF-TOOLS", "PATH is unavailable"))?;
    std::env::split_paths(&path)
        .map(|entry| entry.join(&program))
        .find(|candidate| candidate.is_file())
        .ok_or_else(|| {
            Failure::new(
                "PDF-TOOLS",
                format!("{} is not installed", program.display()),
            )
        })?
        .canonicalize()
        .map_err(Into::into)
}
