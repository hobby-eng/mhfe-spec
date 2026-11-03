use crate::failure::{Failure, Result};
use crate::process::{file_digest, run};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Deserialize, Serialize)]
pub(crate) struct Manifest {
    family: String,
    archive_url: String,
    archive_sha256: String,
    faces: Vec<Face>,
}

#[derive(Deserialize, Serialize)]
struct Face {
    file: String,
    alias: String,
    sha256: String,
}

impl Manifest {
    pub(crate) fn read() -> Result<Self> {
        Ok(serde_json::from_str(include_str!("../fonts.json"))?)
    }

    pub(crate) fn validate(&self, directory: &Path) -> Result<BTreeMap<String, String>> {
        let mut hashes = BTreeMap::new();
        for face in &self.faces {
            let path = [directory.join(&face.file), directory.join(&face.alias)]
                .into_iter().find(|path| path.is_file())
                .ok_or_else(|| Failure::new("PDF-FONTS", "Times New Roman needs all four pinned faces; run install-fonts or set MHFE_PDF_FONT_DIR"))?;
            let actual = file_digest(&path)?;
            if actual != face.sha256 {
                return Err(Failure::new(
                    "PDF-FONTS",
                    "Times New Roman face does not match its pinned SHA-256",
                ));
            }
            hashes.insert(face.file.clone(), actual);
        }
        Ok(hashes)
    }

    pub(crate) fn paths(&self, directory: &Path) -> Result<Vec<PathBuf>> {
        self.validate(directory)?;
        self.faces
            .iter()
            .map(|face| {
                [directory.join(&face.file), directory.join(&face.alias)]
                    .into_iter()
                    .find(|path| path.is_file())
                    .ok_or_else(|| {
                        Failure::new("PDF-FONTS", "Pinned font disappeared before loading")
                    })
            })
            .collect()
    }

    pub(crate) fn install(&self, directory: &Path) -> Result<()> {
        if self.validate(directory).is_ok() {
            return Ok(());
        }
        fs::create_dir_all(directory)?;
        if self
            .faces
            .iter()
            .any(|face| directory.join(&face.file).exists() || directory.join(&face.alias).exists())
        {
            return Err(Failure::new(
                "PDF-FONTS",
                "Choose an empty font directory instead of replacing existing fonts",
            ));
        }
        let archive = directory.join("times32.exe");
        run(
            "curl",
            [
                std::ffi::OsStr::new("--fail"),
                std::ffi::OsStr::new("--location"),
                std::ffi::OsStr::new("--silent"),
                std::ffi::OsStr::new("--show-error"),
                std::ffi::OsStr::new("--retry"),
                std::ffi::OsStr::new("2"),
                std::ffi::OsStr::new("--connect-timeout"),
                std::ffi::OsStr::new("15"),
                std::ffi::OsStr::new("--max-time"),
                std::ffi::OsStr::new("180"),
                std::ffi::OsStr::new("--output"),
                archive.as_os_str(),
                self.archive_url.as_ref(),
            ],
            None,
            None,
        )?;
        if file_digest(&archive)? != self.archive_sha256 {
            return Err(Failure::new(
                "PDF-FONTS",
                "Original font archive failed its checksum",
            ));
        }
        // Read the original self-extracting cabinet as data; never execute it.
        run(
            "cabextract",
            [
                std::ffi::OsStr::new("-q"),
                std::ffi::OsStr::new("-L"),
                std::ffi::OsStr::new("-F"),
                std::ffi::OsStr::new("times*.ttf"),
                std::ffi::OsStr::new("-d"),
                directory.as_os_str(),
                archive.as_os_str(),
            ],
            None,
            None,
        )?;
        self.validate(directory)?;
        Ok(())
    }
}

pub(crate) fn directory() -> Result<PathBuf> {
    let directory = std::env::var_os("MHFE_PDF_FONT_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/usr/share/fonts/truetype/msttcorefonts"));
    Manifest::read()?.validate(&directory)?;
    Ok(directory)
}

/// Owns an isolated working directory containing only the four verified faces.
pub(crate) struct Prepared {
    path: PathBuf,
}

impl Prepared {
    pub(crate) fn new(source: &Path) -> Result<Self> {
        let manifest = Manifest::read()?;
        let sources = manifest.paths(source)?;
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|_| Failure::new("PDF-FONTS", "Invalid clock for font staging"))?
            .as_nanos();
        let path =
            std::env::temp_dir().join(format!("mhfe-pdf-fonts-{}-{stamp}", std::process::id()));
        fs::create_dir(&path)?;
        let prepared = Self { path };
        for (face, source) in manifest.faces.iter().zip(sources) {
            fs::copy(source, prepared.path.join(&face.file))?;
        }
        manifest.validate(&prepared.path)?;
        Ok(prepared)
    }

    pub(crate) fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for Prepared {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
