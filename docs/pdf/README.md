# Document PDFs

- [Specification](mhfe-specification.pdf), built from the repository's [README](../../README.md).
- [Supplement](mhfe-supplement.pdf), built from [DESIGN-NOTES.md](../DESIGN-NOTES.md).
- [SHA-256 checksums](SHA256SUMS) for both files.

These PDFs can be read offline in an ordinary PDF viewer. Each includes its source document's
SHA-256 hash; the Markdown files remain the editable sources. A PDF describes the source bytes used
for its build, which may include changes not yet committed at that time.

To rebuild from the repository root, with Docker installed:

```sh
bash scripts/build-pdfs.sh
```

The build writes checked outputs to `output/documents/`. See
[the build instructions](../PDF-BUILD.md) for formula notation, validation and how to update these
copies. The Rust builder uses Pandoc and Typst, retaining converted expressions and verification evidence
in ignored `output/documents/`.
