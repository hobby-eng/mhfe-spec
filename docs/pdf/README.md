# Document PDFs

- [Specification](mhfe-specification.pdf), built from the repository's [README](../../README.md).
- [Supplement](mhfe-supplement.pdf), built from [DESIGN-NOTES.md](../DESIGN-NOTES.md).
- [SHA-256 checksums](SHA256SUMS) for both files.

These PDFs can be read offline in an ordinary PDF viewer. Each includes its source document's
SHA-256 hash; the Markdown files remain the editable sources. A PDF describes the source bytes used
for its build, which may include changes not yet committed at that time.

To rebuild from the repository root, with Node.js 26.10.0 and Docker installed:

```sh
node scripts/build-pdfs.mjs
```

The build writes checked outputs to `output/documents/`. See
[the build instructions](../PDF-BUILD.md) for formula notation, validation and how to update these
copies. The conversion uses LaTeX expressions for formulas; it produces PDFs, not a standalone
`.tex` document.
