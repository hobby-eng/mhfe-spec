use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::pdf::PdfCheck;
use crate::process::{Toolchain, digest, file_digest, json_file, run, text};
use crate::typeset::Typesetter;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

/// Stages complete verified document sets before exposing successful outputs.
pub(crate) struct PdfBuild {
    root: PathBuf,
    tools: Toolchain,
    output: PathBuf,
}

impl PdfBuild {
    pub(crate) fn new(root: PathBuf) -> Result<Self> {
        let compiled = include_bytes!(concat!(env!("OUT_DIR"), "/renderer-source.bin"));
        if crate::snapshot::bytes(&root)? != compiled {
            return Err(Failure::new(
                "PDF-BUILDER",
                "The builder binary is stale; rebuild it from these exact renderer inputs",
            ));
        }
        let mut tools = Toolchain::discover()?;
        tools.created = Some(source_date(&root)?);
        let output = root.join("output/documents");
        fs::create_dir_all(&output)?;
        Ok(Self {
            root,
            tools,
            output,
        })
    }

    pub(crate) fn probe(&self, source: &Path, images: bool) -> Result<PathBuf> {
        let directory = self.directory()?;
        let commit = self.commit()?;
        self.document(source, "probe", &directory, &commit, images)?;
        Ok(directory)
    }

    pub(crate) fn check(&self) -> Result<PathBuf> {
        let directory = self.directory()?;
        let checks = crate::regression::run(&self.root, &self.tools, &directory)?;
        json_file(&directory.join("regressions.json"), &checks)?;
        Ok(directory)
    }

    pub(crate) fn run(&self) -> Result<PathBuf> {
        let directory = self.directory()?;
        let inputs = self.inputs()?;
        let commit = self.commit()?;
        let mut report = json!({"status":"running","commit":commit,"inputs":inputs,"tools":crate::install::Manifest::read()?,"fonts":crate::fonts::Manifest::read()?,"source_date_epoch":self.tools.created,"builder":"Rust, Pandoc and Typst","builder_sha256":file_digest(&std::env::current_exe()?)?,"poppler":poppler_evidence()?,"documents":[],"notes":["Source hashes also bind builds of uncommitted files.","PDF text and raster checks use independent Poppler tools.","Automated checks do not prove the mathematics or replace visual inspection."]});
        let result = (|| -> Result<()> {
            report["regressions"] =
                crate::regression::run(&self.root, &self.tools, &directory)?.into();
            for (file, name) in [
                ("README.md", "mhfe-specification"),
                ("docs/DESIGN-NOTES.md", "mhfe-supplement"),
            ] {
                println!("MHFE PDF · typesetting {file}");
                let document =
                    self.document(&self.root.join(file), name, &directory, &commit, true)?;
                report["documents"]
                    .as_array_mut()
                    .ok_or_else(|| Failure::new("PDF-REPORT", "Invalid document report"))?
                    .push(document);
            }
            crate::fonts::Manifest::read()?.validate(self.tools.font_dir.path())?;
            if inputs != self.inputs()? {
                return Err(Failure::new(
                    "PDF-SNAPSHOT",
                    "Build inputs changed during conversion",
                ));
            }
            report["status"] = "pass".into();
            json_file(&directory.join("verification.json"), &report)?;
            // All source, layout, text and raster checks finish before any deliverable
            // is promoted. A validation refusal leaves the previous successful files alone.
            let mut sums = String::new();
            for name in ["mhfe-specification.pdf", "mhfe-supplement.pdf"] {
                fs::copy(directory.join(name), self.output.join(name))?;
                sums.push_str(&format!(
                    "{}  {name}\n",
                    file_digest(&directory.join(name))?
                ));
            }
            fs::write(self.output.join("SHA256SUMS"), sums)?;
            json_file(&self.output.join("verification.json"), &report)?;
            Ok(())
        })();
        if let Err(error) = &result {
            report["status"] = "fail".into();
            report["error"] = error.to_string().into();
        }
        json_file(&directory.join("verification.json"), &report)?;
        result?;
        Ok(directory)
    }

    fn document(
        &self,
        path: &Path,
        name: &str,
        directory: &Path,
        commit: &str,
        images: bool,
    ) -> Result<Value> {
        let source = fs::read_to_string(path)?;
        let document = Document::parse(&self.root, path, commit, &source, &self.tools)?;
        json_file(
            &directory.join(format!("{name}-inventory.json")),
            &json!({"source":path.strip_prefix(&self.root).unwrap_or(path),"source_sha256":document.source_sha256,"blocks":document.blocks,"math":document.expressions}),
        )?;
        let typesetter = Typesetter::new(&self.tools, &self.root);
        typesetter.source(&document, name, directory)?;
        // Render before retaining the large layout/metadata DOM in this process.
        if images {
            typesetter.native_images(name, directory)?;
        }
        let metadata = typesetter.compile(name, directory)?;
        crate::semantics::verify(&document, &metadata, &self.tools, directory, name)?;
        let pdf = PdfCheck::read(&directory.join(format!("{name}.pdf")), directory, name)?;
        let result = pdf.validate(&document, &metadata, directory, name, images)?;
        println!(
            "MHFE PDF · checked {} expressions and {} pages",
            document.expressions.len(),
            result.pages
        );
        Ok(
            json!({"file":format!("{name}.pdf"),"source":path.strip_prefix(&self.root).unwrap_or(path),"source_sha256":document.source_sha256,"sha256":file_digest(&directory.join(format!("{name}.pdf")))?,"source_blocks":document.blocks.len(),"math":document.expressions,"verification":result}),
        )
    }

    fn directory(&self) -> Result<PathBuf> {
        let time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| Failure::new("PDF-CLOCK", "System clock precedes the Unix epoch"))?
            .as_nanos();
        let directory = self
            .output
            .join(format!("build-{time}-{}", std::process::id()));
        fs::create_dir(&directory)?;
        Ok(directory)
    }

    fn commit(&self) -> Result<String> {
        if let Ok(commit) = std::env::var("MHFE_SOURCE_COMMIT") {
            if !matches!(commit.len(), 40 | 64) || !commit.bytes().all(|c| c.is_ascii_hexdigit()) {
                return Err(Failure::new(
                    "PDF-SNAPSHOT",
                    "Invalid source commit identifier",
                ));
            }
            return Ok(commit);
        }
        Ok(
            text(run("git", ["rev-parse", "HEAD"], Some(&self.root), None)?)?
                .trim()
                .into(),
        )
    }

    fn inputs(&self) -> Result<BTreeMap<String, String>> {
        let mut files = vec![
            self.root.join("README.md"),
            self.root.join("docs/DESIGN-NOTES.md"),
            self.root.join("scripts/build-pdfs.sh"),
            self.root.join(".dockerignore"),
            self.root.join("Cargo.toml"),
            self.root.join("Cargo.lock"),
            self.root.join("rust-toolchain.toml"),
        ];
        for directory in ["tooling/pdf", "assets"] {
            Self::walk_files(&self.root.join(directory), &mut files)?;
        }
        let mut values = BTreeMap::new();
        for file in files {
            let name = file
                .strip_prefix(&self.root)
                .map_err(|_| Failure::new("PDF-SNAPSHOT", "Build input leaves the repository"))?
                .to_string_lossy()
                .into_owned();
            values.insert(name, digest(&fs::read(file)?));
        }
        Ok(values)
    }

    fn walk_files(path: &Path, files: &mut Vec<PathBuf>) -> Result<()> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            if matches!(entry.file_name().to_str(), Some("target" | "node_modules")) {
                continue;
            }
            let kind = entry.file_type()?;
            if kind.is_dir() {
                Self::walk_files(&entry.path(), files)?;
            } else if kind.is_file() {
                files.push(entry.path());
            } else {
                return Err(Failure::new(
                    "PDF-SNAPSHOT",
                    "Symlinks are not allowed among renderer inputs",
                ));
            }
        }
        Ok(())
    }
}

fn poppler_evidence() -> Result<Value> {
    let version = text(run("bash", ["-c", "pdftotext -v 2>&1"], None, None)?)?;
    let mut executables = BTreeMap::new();
    for name in ["pdfinfo", "pdftotext", "pdftoppm"] {
        let path = crate::install::executable_path(name.into())?;
        executables.insert(name, file_digest(&path)?);
    }
    Ok(json!({"version":version.lines().next().unwrap_or_default(),"executables":executables}))
}

/// Fixes the PDF creation date, using the commit time unless `SOURCE_DATE_EPOCH` is set.
/// Reproducible bytes require this date and the source commit to stay fixed too.
fn source_date(root: &Path) -> Result<String> {
    let date = match std::env::var("SOURCE_DATE_EPOCH") {
        Ok(date) => date,
        Err(_) => text(run(
            "git",
            ["log", "-1", "--format=%ct", "HEAD"],
            Some(root),
            None,
        )?)?
        .trim()
        .into(),
    };
    if date.is_empty() || date.len() > 12 || !date.bytes().all(|c| c.is_ascii_digit()) {
        return Err(Failure::new("PDF-SNAPSHOT", "Invalid source date"));
    }
    Ok(date)
}
