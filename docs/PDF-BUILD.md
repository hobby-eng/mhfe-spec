# Building and checking the PDFs

`README.md` and `docs/DESIGN-NOTES.md` are the editable sources of the specification and supplement.
The build reads them directly, converts the Markdown and mathematics with Pandoc, and typesets the
PDFs with Typst. The Rust `xtask` owns conversion, validation and output publication. It needs
neither Node.js, a browser engine nor a TeX installation. Typst is a separate typesetting system;
LaTeX remains the input notation for explicit formulas in Markdown.

## Build

With Docker installed, choose an external cache for the pinned fonts and run from the repository
root (an existing workspace or Linux font installation is also recognized automatically):

```sh
export MHFE_PDF_FONT_DIR=/absolute/path/to/external-font-cache
bash scripts/build-pdfs.sh
```

The first run downloads the pinned container images, Rust dependencies and document tools while
building the image. Rendering runs with the network disabled, a read-only source mount and root
filesystem, no capabilities, and limits of two CPUs, 2 GiB of memory and 128 processes. Only ignored
`output/` and a bounded temporary filesystem are writable. No source file is rewritten.

If outbound HTTPS fails only on Docker's bridge network, set `MHFE_PDF_BUILD_NETWORK=host`
for image construction. The default is Docker's isolated build network; this override affects
installation only. The separate rendering container always uses `--network none`.

A directory containing the two already installed public executables can be supplied with
`MHFE_PDF_TOOLS_DIR=/absolute/path/to/document-tools`. The wrapper uses that directory as a named
build context instead of downloading the tools again. On the owner's workspace it also recognizes
`../workingspace/pdf-tools/typst-0.15.1-pandoc-3.13/`. This cache stays outside Git; executable hashes
are checked before rendering. CI without a cache uses the download stage.

The successful outputs are:

- `output/documents/mhfe-specification.pdf`;
- `output/documents/mhfe-supplement.pdf`;
- `output/documents/SHA256SUMS`;
- `output/documents/verification.json`.

Each attempt has its own directory below `output/documents/`, including failures. It retains source
inventories, the Pandoc AST, generated Typst, native layout and math trees, a separate MathML
comparison, extracted PDF text and page images from Typst and Poppler, with difference images.
Validation finishes for both documents before successful deliverables replace the previous set.
An unsuccessful validation leaves those previous deliverables alone. Do not publish files from a
failed attempt.

The manual and release workflow in `.github/workflows/documents.yml` uses the same wrapper and
uploads the outputs. A push or pull request does not start this full document build.

## Pinned tools and local use

`rust-toolchain.toml`, `Cargo.lock`, the image digests in `tooling/pdf/Dockerfile` and archive and
binary hashes in `tooling/pdf/toolchain.json` record the build inputs. The current document tools
are Pandoc 3.13 and Typst 0.15.1 on Linux x86-64. Body text uses Times New Roman, 12 pt, justified,
with wider side margins and more space between lines and paragraphs. Headings, code and table
cells keep their own alignment. The four
Times New Roman faces and their original cabinet archive are pinned in `tooling/pdf/fonts.json`.
The font files stay outside Git and outside the rendering image. The wrapper mounts them read-only
for rendering. The builder stages only the four verified faces in a temporary directory, which
is removed when it exits; Typst ignores other system font locations. Math uses bundled New Computer
Modern Math, which supplies the mathematical glyphs and metrics that Times New Roman lacks. The runtime
image includes Poppler for independent PDF inspection. Its Debian packages are not a snapshot of
the distribution, but Poppler only checks the PDFs and does not produce them. The PDF creation date
is the commit time of `HEAD`, passed as `SOURCE_DATE_EPOCH`. Repeated builds give identical PDF
bytes when the source files, source commit, `SOURCE_DATE_EPOCH`, builder, tools and fonts are the
same. The commit also determines repository links embedded in the PDF. The report binds the
actual source and builder bytes used and records the commit, source date, Poppler version and
executable hashes. The wrapper passes the source commit and its time from host Git; the rendering
image does not need Git. A local build accepts an explicit `SOURCE_DATE_EPOCH`; without it, the
builder uses the time of `HEAD`.

Typst is also limited to two compilation jobs. Full-width paragraphs use the fixed A4 text width;
indented paragraphs and table cells obtain their actual container width during layout. This avoids
performing a dynamic width query for every full-width source block.

Headings have space above and below and stay with the following content. Each table and code
block, including the BIP preamble, stays on one page; an oversized block is refused instead of
being split or clipped. Existing prose-heavy tables have column proportions keyed by their
headers and mathematical labels in `tooling/pdf/src/table.rs`. Other tables use content measurements rather than the
width of Markdown separators. The contents use tighter line spacing, start on a fresh page when
needed and are followed by a page break. Major supplement parts also begin on fresh pages.

For Times New Roman, the wrapper recognizes the workspace cache
`../workingspace/pdf-fonts/times-new-roman-2.82/` or the installed Linux `msttcorefonts` directory.
Set `MHFE_PDF_FONT_DIR` to choose another external directory. If that directory is empty, a separate
installation container downloads the original font cabinet, checks its SHA-256, extracts only the
four faces and verifies their hashes. It never executes the cabinet. CI uses the runner's temporary
directory. This installation step may use the network; rendering remains network-disabled.
Existing files with different hashes are refused rather than overwritten. The build report records
the font pins and validates the faces again before publishing outputs.

For a local build, install the pinned tools in a tool directory outside the repository:

```sh
cargo xtask install-tools /absolute/path/to/document-tools
export MHFE_PANDOC=/absolute/path/to/document-tools/pandoc
export MHFE_TYPST=/absolute/path/to/document-tools/typst
export MHFE_PDF_FONT_DIR=/absolute/path/to/times-new-roman-fonts
cargo xtask install-fonts "$MHFE_PDF_FONT_DIR"
cargo xtask pdf-check
bash scripts/build-pdfs.sh --local
```

The installer checks archive hashes before extracting the named binaries, then checks binary
hashes. Rendering checks those binary hashes again before executing them. An existing tool with
different bytes is refused. Put Poppler's `pdfinfo`, `pdftotext` and `pdftoppm`, GNU `timeout`, and
Git on `PATH`. Local rendering has no container isolation; use it only on these public documents.
The Docker wrapper needs no host Rust installation. `cargo xtask pdf` calls the wrapper when Rust
is already available. `cargo xtask pdf-probe path/to/public.md --images` checks a public Markdown
file inside this checkout without replacing the successful document set.

## Source notation

Ordinary code spans remain code unless the notation classifier recognizes mathematical content.
The shared ASCII/Unicode parser handles powers, indices, primes, grouped expressions, Greek
letters, comparisons, concatenation and logical operators. `ascii:` in a code span or a fence
labelled `ascii-math` explicitly selects it. A fence labelled `math` selects LaTeX. Mathematical
unlabelled and `text` fences use the same parser; identifiers, commands and file paths stay literal.
The retained inventory records the original expression, canonical LaTeX and conversion identity.

Explicit inline formulas can use GitHub's protected form `$` followed by a backtick, the LaTeX
expression, a backtick and `$`. Simple `$...$` and `$$...$$` formulas are supported too. Escape a
literal dollar outside code as `\$`. Use `\mathop{\mathrm{name}}\nolimits` for a named operator in
explicit source mathematics: GitHub rejects `\operatorname`. Use `\lt` for less-than, since a raw
`<` followed by a letter can be read as markup. Unprotected formulas with Markdown-sensitive
escapes or line breaks are refused. These checks cover known incompatibilities; they do not
emulate GitHub's complete renderer.

Unsupported LaTeX, malformed expressions, missing delimiters, stateful macros and resource
commands stop the build. Wide inline expressions may become unnumbered equations, split at
outer relations or between outer function arguments; their rows are set like TeX's `multline`,
the first flush left and the last flush right. A paragraph may wrap an inline equation only after
a relation or binary operator outside all brackets, norms and absolute-value bars, as TeX does. The
parts in between are indivisible, so a wrap cannot split probability brackets. Equations narrower
than an eighth of their line, including attached sentence punctuation, stay whole. The parts are joined by Typst's spacing after the operator,
thick after a relation and medium after a binary operator, which disappears at a line end; a
regression case checks that the parts keep the width of each whole equation. Each resulting
segment and row must fit its actual paragraph, list or table-cell width; an expression
with no supported safe break is refused. Sentence punctuation stays with the equation. These
choices do not change the source notation or shrink the body font. Custom operator names are
quoted during conversion so names such as
`SHA-256` remain operators. The adapter also preserves primes attached to subscripted symbols,
including `Θ₀′`, and explicit equation tags. `Pr` uses a lower-right game index in both inline and
display math. The source is never rewritten to achieve these presentation choices.

The adapter preserves the gaps between equation pairs in `aligned`, and the individual `l`, `c`
and `r` alignments, internal vertical rules and `\hline` separators of a flat display `array`. Unsupported
array specifications are refused. Concatenation has binary-operator spacing; explicit norm
delimiters retain their delimiter role.
Nested directional modulus pairs (`\lvert` and `\rvert`) receive explicit delimiter classes so
their opening and closing roles survive Pandoc. Their glyphs, explicit sizes and attached indices
are retained; the canonical LaTeX and Markdown remain unchanged.

Links within a document resolve to its headings. Relative repository links point to the recorded
commit on GitHub. Local PNG and JPEG images are embedded; remote badges become text labels, and
no remote image is fetched during rendering. Raw Typst and raw TeX document commands in source
Markdown are disabled. Source HTML is limited to the forms used by these documents.

## Checks and their limits

The full build runs the unit-tested parser and real-document regression cases before conversion.
Run the fast Rust tests and static checks separately with:

```sh
cargo test --locked
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
dprint check
```

Conversion and PDF checks cover:

- every source block and expression, its order and required occurrence count;
- mathematical glyph order and counts, subscript and superscript attachments, fractions and brace
  annotations against a separately generated MathML representation;
- inline versus display mode, including aligned equations and their printed tags;
- all 2,708 current canonical expressions against retained glyph strings from the predecessor
  parser and KaTeX 0.19.0, independently of Pandoc;
- complete source prose, PDF character counts and glyph bounds through Poppler;
- complete tables and code blocks on one page, and text fitting its own table cell;
- visible heading gaps measured from PDF glyph bounds and headings kept with following content;
- compact contents kept together when they fit a page, starting on a fresh page when longer,
  with the first body heading at the top of the next page;
- independent Typst and Poppler page renders, both globally and around individual formulas, with local differences measured against ink
  as well as page area.

Regression cases deliberately remove math metadata, substitute a mathematical sign, narrow a
cell, damage a PDF, split tables and the BIP preamble, remove heading gaps and move contents or
the following body incorrectly. Mathematical-layout cases also remove array rules, remove the
gutter between equation pairs, undo binary spacing, insert a break inside probability brackets,
change the spacing between the parts of an inline equation and keep that spacing at an inline wrap
after a relation.
They check PDF glyph positions and the actual rasterized rules, rather than only comparing two
renders of the same source. Unit tests also remove a small local formula
from a raster where the overall page difference stays small. Refusals must occur at the expected
check. A retained corpus of 1,040 inline conversions checks compatibility with the previous
converter; it is a test oracle, not the production parser.

The independent glyph fixture, its normalization rules and its provenance are described in
[`tooling/pdf/tests/README.md`](../tooling/pdf/tests/README.md). It is data, with no Node.js or
KaTeX dependency in the build. An intentional change to canonical mathematics requires a new
independently checked reference; a newly generated Typst string is not a valid replacement oracle.

These checks detect conversion and layout defects. MathML and Typst generation share Pandoc, so
agreement is not an independent proof of all parsing behaviour. Glyph and attachment checks do
not establish mathematical truth, and raster comparison does not replace looking at the pages.
Review both PDFs visually after a build, especially dense formulas, tables and contents pages.

## Update the tracked PDFs

After all checks and visual review succeed:

```sh
cp output/documents/mhfe-specification.pdf docs/pdf/mhfe-specification.pdf
cp output/documents/mhfe-supplement.pdf docs/pdf/mhfe-supplement.pdf
cp output/documents/SHA256SUMS docs/pdf/SHA256SUMS
(cd docs/pdf && sha256sum --check SHA256SUMS)
```

Keep the source edits, build changes and refreshed PDFs in the same reviewed change. See
[`docs/pdf/README.md`](pdf/README.md). Historical audit harnesses describe their original build
and remain unchanged; they are not dependencies of the current renderer.
