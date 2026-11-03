mod ascii;
mod build;
mod document;
mod failure;
mod fonts;
mod install;
mod layout;
mod layout_regression;
mod legacy_oracle;
mod math_content;
mod math_layout;
mod math_layout_regression;
mod notation;
mod pagination;
mod pdf;
mod process;
mod raster;
mod regression;
mod semantics;
#[path = "../snapshot.rs"]
mod snapshot;
mod source;
mod table;
mod typeset;

fn main() {
    if let Err(error) = run() {
        eprintln!("MHFE PDF · failed: {error}");
        std::process::exit(1);
    }
}

fn run() -> failure::Result<()> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let root = std::env::current_dir()?.canonicalize()?;
    match args.as_slice() {
        [command, directory] if command == "install-fonts" => {
            fonts::Manifest::read()?.install(std::path::Path::new(directory))?
        }
        [command] if command == "pdf-check" => {
            let directory = build::PdfBuild::new(root)?.check()?;
            println!(
                "MHFE PDF · regression checks passed; evidence in {}",
                directory.display()
            );
        }
        [command] if command == "pdf" => {
            let output = process::run(
                "bash",
                [root.join("scripts/build-pdfs.sh")],
                Some(&root),
                None,
            )?;
            print!("{}", process::text(output)?);
        }
        [command, directory] if command == "install-tools" => {
            install::Manifest::read()?.install(std::path::Path::new(directory))?
        }
        [command, local] if command == "pdf" && local == "--local" => {
            let directory = build::PdfBuild::new(root)?.run()?;
            println!("MHFE PDF · passed; evidence in {}", directory.display());
        }
        [command, file] if command == "pdf-probe" => {
            let source = probe_path(&root, file)?;
            let directory = build::PdfBuild::new(root.clone())?.probe(&source, false)?;
            println!("MHFE PDF · probe in {}", directory.display());
        }
        [command, file, flag] if command == "pdf-probe" && flag == "--images" => {
            let source = probe_path(&root, file)?;
            let directory = build::PdfBuild::new(root.clone())?.probe(&source, true)?;
            println!("MHFE PDF · probe in {}", directory.display());
        }
        _ => {
            return Err(failure::Failure::new(
                "PDF-USAGE",
                "Usage: cargo xtask pdf [--local] | pdf-check | pdf-probe <public-document> [--images] | install-tools <directory> | install-fonts <directory>",
            ));
        }
    }
    Ok(())
}

fn probe_path(root: &std::path::Path, file: &str) -> failure::Result<std::path::PathBuf> {
    let path = root.join(file).canonicalize()?;
    if !path.starts_with(root) || path.extension().is_none_or(|extension| extension != "md") {
        return Err(failure::Failure::new(
            "PDF-PATH",
            "A probe must use a public Markdown document inside this repository",
        ));
    }
    Ok(path)
}
