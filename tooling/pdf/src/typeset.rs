use crate::document::Document;
use crate::failure::{Failure, Result};
use crate::process::{Toolchain, json_file, text};
use serde_json::Value;
use std::ffi::OsStr;
use std::fs;
use std::path::Path;

/// Produces source-bound Typst, retaining every translated mathematical expression.
pub(crate) struct Typesetter<'a> {
    tools: &'a Toolchain,
    root: &'a Path,
}

impl<'a> Typesetter<'a> {
    pub(crate) fn new(tools: &'a Toolchain, root: &'a Path) -> Self {
        Self { tools, root }
    }

    pub(crate) fn source(&self, document: &Document, name: &str, directory: &Path) -> Result<()> {
        let json = serde_json::to_vec(&document.ast)?;
        fs::write(directory.join(format!("{name}.json")), &json)?;
        let mut body = text(self.tools.pandoc(
            &[
                "--from",
                "json",
                "--to",
                "typst",
                "--fail-if-warnings",
                "--wrap",
                "preserve",
            ],
            &json,
        )?)?;
        body = self.operators(document, body)?;
        let identity = format!("Source SHA-256: {}", document.source_sha256);
        let identity = serde_json::to_string(&identity)?;
        let source = format!(
            "{}\n#text(size: 7.5pt, fill: luma(90))[#{}]\n#v(5pt)\n{}",
            include_str!("../document.typ"),
            identity,
            body
        );
        fs::write(directory.join(format!("{name}.typ")), source)?;
        Ok(())
    }

    fn operators(&self, document: &Document, mut body: String) -> Result<String> {
        for expression in &document.expressions {
            let start_marker = format!("#mhfe-math(\"{}\",", expression.id);
            let end_marker = format!("]#mhfe-math-end(\"{}\")", expression.id);
            let start = body.find(&start_marker).ok_or_else(|| {
                Failure::new("PDF-COVERAGE", "Pandoc lost a mathematical start marker")
            })?;
            let end = start
                + body[start..].find(&end_marker).ok_or_else(|| {
                    Failure::new("PDF-COVERAGE", "Pandoc lost a mathematical end marker")
                })?;
            let mut fragment = body[start..end].to_owned();
            for (alias, name) in &expression.operators {
                let quoted = serde_json::to_string(alias)?;
                let actual = fragment.matches(&quoted).count();
                if actual != 1 {
                    return Err(Failure::new(
                        "PDF-OPERATOR",
                        format!("Lost or duplicated translated operator {}", expression.id),
                    ));
                }
                fragment = fragment.replace(
                    &quoted,
                    &if name == "‖" {
                        "class(\"binary\", bar.v.double)".into()
                    } else {
                        format!("op({}, limits: #false)", serde_json::to_string(name)?)
                    },
                );
            }
            fragment =
                crate::math_layout::structure(&expression.source, &fragment, expression.display)?;
            for (alias, fence) in &expression.fences {
                let quoted = serde_json::to_string(alias)?;
                if fragment.matches(&quoted).count() != 1 {
                    return Err(Failure::new(
                        "PDF-MATH-LAYOUT",
                        "Lost or duplicated fence alias",
                    ));
                }
                fragment = fragment.replace(&quoted, &fence.typst());
            }
            body.replace_range(start..end, &fragment);
        }
        Ok(body)
    }

    pub(crate) fn compile(&self, name: &str, directory: &Path) -> Result<Vec<Value>> {
        let source = directory.join(format!("{name}.typ"));
        let pdf = directory.join(format!("{name}.pdf"));
        self.tools.typst(
            &[
                OsStr::new("compile"),
                OsStr::new("--ignore-system-fonts"),
                OsStr::new("--root"),
                self.root.as_os_str(),
                source.as_os_str(),
                pdf.as_os_str(),
            ],
            self.root,
        )?;
        let metadata = self.tools.typst(
            &[
                OsStr::new("eval"),
                OsStr::new("--ignore-system-fonts"),
                OsStr::new("--root"),
                self.root.as_os_str(),
                OsStr::new("query(metadata).map(it => it.value)"),
                OsStr::new("--in"),
                source.as_os_str(),
            ],
            self.root,
        )?;
        let metadata: Vec<Value> = serde_json::from_slice(&metadata)?;
        json_file(&directory.join(format!("{name}-layout.json")), &metadata)?;
        Ok(metadata)
    }

    pub(crate) fn native_images(&self, name: &str, directory: &Path) -> Result<()> {
        let source = directory.join(format!("{name}.typ"));
        let pattern = directory.join(format!("{name}-native-{{p}}.png"));
        self.tools.typst(
            &[
                OsStr::new("compile"),
                OsStr::new("--ignore-system-fonts"),
                OsStr::new("--root"),
                self.root.as_os_str(),
                OsStr::new("--format"),
                OsStr::new("png"),
                OsStr::new("--ppi"),
                OsStr::new("96"),
                source.as_os_str(),
                pattern.as_os_str(),
            ],
            self.root,
        )?;
        Ok(())
    }
}
