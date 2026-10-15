# Building and checking the PDFs

The specification and supplement have one source each: `README.md` and `docs/DESIGN-NOTES.md`. The
PDF build reads these files directly. It does not maintain a second article. The same notation
converter runs on every input, including mathematical code spans and display blocks. The separate
ePrint article is not an input to this build.

The input format is Markdown (`.md`). The build converts mathematical notation to LaTeX expressions,
renders them with KaTeX in HTML, and prints the document to PDF. It does not export a standalone
LaTeX document (`.tex`) or require a TeX installation. Generated LaTeX expressions are retained in
`verification.json`; the HTML and PDFs contain the typeset formulas.

Ready-to-read copies are in [Document PDFs](pdf/README.md). The sections below explain how to
rebuild them and which notation the converter accepts.

## Build

With Node.js 26.10.0 and Docker installed, run from the repository root:

```sh
node scripts/build-pdfs.mjs
```

The first run builds the tool image and downloads its pinned Node dependencies and Chromium.
Rendering then runs with the network disabled, a read-only source mount, two CPUs and a 2 GiB memory
limit. It does not run MHFE, Argon2 or the cryptographic vectors.

A successful run writes these files to the ignored `output/documents/` directory:

- `mhfe-specification.pdf` and `mhfe-supplement.pdf`;
- `SHA256SUMS`, covering the two PDFs;
- `verification.json`, recording source and builder hashes, tool versions, expression inventories,
  table column widths and per-page check results.

Each attempt also keeps its HTML, before/after page images, image differences and detailed result
under `output/documents/build-*/`. A validation failure exits nonzero and copies no new PDFs to the
top level; any previous successful output remains there with its original hashes and report. Use the
latest attempt's result, not merely the existence of an older PDF, to judge a build.

The GitHub workflow **Verified document PDFs** runs manually or after a release is published. It
retains the PDFs as workflow artifacts. For a release, a separate job attaches them only after the
checks pass. It does not replace an existing release asset silently. No PDF build runs on an
ordinary push. Workflow evidence expires after seven days; verified deliverables after thirty days.
Release assets remain attached to their release.

## Updating the copies in Git

At the owner's request, `docs/pdf/` holds the two checked PDFs and their `SHA256SUMS`, so a checkout
includes readable documents without a build. This is an explicit exception to the workspace's rule
against tracking generated exports. Intermediate HTML, page images and verification reports remain
in ignored `output/`.

After a successful build and visual inspection, copy its outputs from the repository root:

```sh
cp output/documents/mhfe-specification.pdf output/documents/mhfe-supplement.pdf output/documents/SHA256SUMS docs/pdf/
(cd docs/pdf && sha256sum -c SHA256SUMS)
```

Update both PDFs and the checksum file together when their Markdown sources or layout change. The
build and GitHub workflow do not update or commit these copies automatically. Commit and push still
require the owner's request.

## Writing mathematics

Use dollar-and-backtick delimiters for inline mathematics and a fenced block labelled `math` for
display mathematics. They protect LaTeX from Markdown's own escape and emphasis handling on GitHub:

````text
The game is $`\Gamma_0`$ and the bound is $`2^{-128}`$.

```math
\Pr[X=x] = \frac{1}{2^{128}}.
```
````

For a custom function name use `\mathop{\mathrm{top}}\nolimits`, or
`\mathop{\text{SHA-256}}\nolimits` for a name containing literal hyphens. GitHub rejects
`\operatorname` even though KaTeX accepts it. Use `\lt` for less-than: GitHub can misread a literal
`<` followed by a letter as markup, even inside a math fence. The build rejects both cases in
explicit source mathematics, and rejects unprotected dollar-delimited expressions containing line
breaks or Markdown-sensitive escapes. Simple dollar-delimited formulas remain supported. These are
checks for known GitHub incompatibilities, not a complete emulation of its renderer; review GitHub's
preview after changing the supported notation. The build itself stays offline.

The builder supports the mathematical LaTeX commands implemented by its pinned KaTeX version. It is
not a full TeX document compiler. An unsupported command, malformed expression, missing delimiter or
strict-mode error stops the build. Resource commands, HTML injection and stateful macros are
refused. Escape a literal dollar sign as `\$` outside code.

The builder also transcribes the specification's ASCII/Unicode mathematical notation into LaTeX.
This is a shared parser, not a replacement table for particular formulas. It handles powers,
indices, primes, postfix stars, grouped expressions, Greek letters, comparisons, concatenation and
logical operators, in inline code and in mathematical `text` or unlabelled fences. A fence labelled
`ascii-math` explicitly selects this notation; an inline code span can start with `ascii:`. For
example:

````text
The coefficient is `ascii:d_(n-1)`.

```ascii-math
m(x) = d_0 * x^(n-1) + d_1 * x^(n-2) + ... + d_(n-1)
g(x) = (x + alpha^1) * (x + alpha^2) * ... * (x + alpha^k)
```
````

`x^(n-1)` and `d_(n-1)` use the whole grouped expression as the exponent or index. An ambiguous
indexed expression such as `R_0^(1)` is refused: write `R_0^1` for a power or `R_0^{(1)}` for a
sample label whose parentheses must remain visible. `p*` is a postfix star; `5*d_2` is
multiplication. Division keeps its explicit slash: the converter does not infer an unstated fraction
grouping. Use LaTeX `\frac{...}{...}` for a stacked fraction. Long mixed definitions and algorithms
use explicit LaTeX with line breaks in the source, so the builder need not guess how explanatory
words or control flow bind to an expression.

Quoted strings retain their quotes and characters in mathematical expressions; explanatory prose
uses explicit LaTeX `\text{...}`. Literal protocol names, byte strings, paths and program
identifiers remain code. A span beginning with `literal:` or a fence labelled `literal` explicitly
preserves code that looks mathematical. Programming-language fences also remain literal. An
unfamiliar multi-letter indexed name requires an explicit `ascii:` or `literal:` choice. Unbalanced
groups, repeated or empty scripts, unsupported characters and commands fail rather than falling back
to raw code. Diagnostics identify the input file and the inline block's starting line. Plain prose
is not interpreted as algebra; only game labels such as Γ0 are automatically given their
mathematical subscripts.

The report retains the original notation, consumed tokens, syntax tree and generated LaTeX for
inline conversions, and the original lines, tokens and LaTeX for block conversions. Every source
character must be consumed. The builder never edits the Markdown while producing a PDF.

## What the checks establish

Tables size their columns from the content: short numeric columns leave more room for formulas and
explanations. The builder keeps the document's font size and checks every cell after pagination.
Text and mathematical glyphs must fit their own cells, not merely the page. A table that cannot fit
at the normal size fails the build and needs an explicit layout or source change; it is not silently
clipped or reduced to unreadable text.

1. **Before layout:** the Markdown parser inventories every formula and its conversion, if any.
   Fixed expected results and independent MathML checks cover powers, compound indices and
   operators. KaTeX parses each formula with `throwOnError`, strict error handling and untrusted
   input. Local images and mathematical fonts are embedded; remote badges become linked text labels.
   Other remote images are refused.
2. **After pagination:** every source text block must survive, including split blocks and repeated
   table headings, and the order of source blocks must agree. Each formula must occur once with its
   original LaTeX annotation, except for table headings repeated on subsequent pages. Internal
   anchors must resolve. Formula, table, image and code geometry is checked against the page,
   including individual mathematical text runs inside a fitting box. Table content is also checked
   against its cell boundaries.
3. **After PDF creation:** PDF.js independently reads every page and its text and renders it with a
   second engine. Page counts, dimensions and normalized character counts must match the layout.
   Invalid replacement glyphs fail. Page images and formula regions are compared with the browser
   images; substantial differences fail. All comparison images are retained for inspection.
4. **The checker itself:** every build first runs positive and deliberately damaged fixtures for
   invalid ASCII notation and LaTeX, lost source blocks and formulas, overflowing glyphs, clipping,
   substituted glyphs and truncated PDFs. Table fixtures cover unequal columns, repeated headings
   and deliberate overlaps between neighbouring cells. GitHub fixtures check the rejected macro,
   protected delimiters, less-than subscripts and preservation of escapes. The build also refuses
   sources that change while it is running.

The image comparison allows rasterizer antialiasing differences. It is supplemented by exact
normalized character counts, so a small missing character is not accepted merely because it occupies
few pixels. Counts alone do not establish reading order, and matching a picture does not establish
the mathematical meaning of an expression. Both engines can faithfully render a mistake already
present in the source.

Inspect the resulting pages before publishing a changed layout or mathematical notation. Check long
formulas, superscripts, subscripts, tables and page breaks in particular. The automated report does
not claim that this human review occurred or that the proofs are correct.

The image starts from a digest-pinned base and uses a frozen dependency lockfile. Operating-system
packages are installed from the base distribution's repositories. This is a controlled build
environment, not a claim of byte-for-byte reproducible PDFs.

## Development

The published toolchain manifest and lockfile are in `tooling/pdf/`; they are separate from the
local-only root Prettier configuration. To use an existing isolated installation of those exact
dependencies and its matching Playwright browser:

```sh
MHFE_PDF_DEPENDENCIES=/path/to/pdf-toolchain node scripts/build-pdfs.mjs --local
MHFE_PDF_DEPENDENCIES=/path/to/pdf-toolchain node scripts/pdf/test.mjs
```

The normal Docker command is preferred for shared results. On the owner's machine dependencies
belong under the workspace's `workingspace/`, not in a project or a new global installation.
Development runs record the actual Node and browser versions in their report.
