use std::fs;
use std::io;
use std::path::{Path, PathBuf};

// This module is shared by the build script and the executable. Comparing exact
// bytes avoids assigning fresh source hashes to an older, stale builder binary.
pub(crate) fn files(root: &Path) -> io::Result<Vec<PathBuf>> {
    let mut files = ["Cargo.toml", "Cargo.lock", "rust-toolchain.toml"]
        .iter()
        .map(|file| root.join(file))
        .collect::<Vec<_>>();
    walk(&root.join("tooling/pdf"), &mut files)?;
    files.sort();
    Ok(files)
}

fn walk(directory: &Path, files: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(directory)? {
        let entry = entry?;
        if matches!(entry.file_name().to_str(), Some("target" | "node_modules")) {
            continue;
        }
        let kind = entry.file_type()?;
        if kind.is_dir() {
            walk(&entry.path(), files)?;
        } else if kind.is_file() {
            files.push(entry.path());
        } else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Renderer inputs cannot be symlinks",
            ));
        }
    }
    Ok(())
}

pub(crate) fn bytes(root: &Path) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    for path in files(root)? {
        let relative = path
            .strip_prefix(root)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))?;
        let name = relative.to_string_lossy();
        let content = fs::read(&path)?;
        bytes.extend_from_slice(name.as_bytes());
        bytes.push(0);
        bytes.extend_from_slice(&(content.len() as u64).to_le_bytes());
        bytes.extend_from_slice(&content);
    }
    Ok(bytes)
}
