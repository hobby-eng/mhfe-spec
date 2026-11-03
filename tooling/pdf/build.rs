mod snapshot;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manifest = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR")?);
    let root = manifest
        .parent()
        .and_then(std::path::Path::parent)
        .ok_or("The PDF crate must be inside tooling/pdf")?;
    println!("cargo:rerun-if-changed={}", manifest.display());
    for file in snapshot::files(root)? {
        println!("cargo:rerun-if-changed={}", file.display());
    }
    let output = std::path::PathBuf::from(std::env::var("OUT_DIR")?).join("renderer-source.bin");
    std::fs::write(output, snapshot::bytes(root)?)?;
    Ok(())
}
