# PDF conversion references

`legacy-notation.json` retains 1,040 conversions from the predecessor notation parser.
`independent-math-glyphs.json` retains all 2,708 expressions of the current specification and
supplement, parsed by that predecessor and rendered to MathML by KaTeX 0.19.0. These are data
references; the Rust builder neither runs nor depends on Node.js or KaTeX.

The fixture retains the hashes of the historical generator and its inputs as provenance data;
the generator is not part of this repository. A build refuses any changed or added canonical
expression until the fixture covers it. The probe command writes the expression inventory of each
document without this check:

```sh
cargo xtask pdf-probe README.md
cargo xtask pdf-probe docs/DESIGN-NOTES.md
```

For an intentional formula change, obtain a new reference from an independent parser and renderer
outside this repository. The retained reference used the predecessor parser from commit `aa5438a`
and KaTeX 0.19.0. Compare new and changed glyph strings with the source, retain the generating
tools' hashes and review the fixture diff before accepting it. The normal build only reads the
JSON reference.

Each glyph entry is bound to its document, expression ID, canonical LaTeX SHA-256 and display flag.
The build requires complete coverage and the same ordered glyph string. Whitespace, invisible
spacing characters, Unicode mathematical alphabet styles, minus and prime variants, asterisk and
vertical-bar variants are normalized. The retained reference also records the observed presentation
differences: three dots for an ellipsis, the backslash for the set-difference sign and the short
mapping arrow for the long one. Brace curves and equation numbers are checked separately by the
existing decoration and equation-tag checks, so they are absent from this glyph string.

This reference checks conversion, not mathematical truth or page geometry. Update it only after
independently checking an intentional change to the canonical expressions. Do not regenerate it
from the current Pandoc or Typst output: that would remove its independent reference value.

`math-layout.md` uses public source examples and synthetic formulas to exercise ruled arrays,
individual column alignment, aligned equation pairs, concatenation, protected probability brackets,
sentence punctuation and nested lists. The regression suite checks PDF glyph positions and
rasterized separator rules. It deliberately removes the rules or gutters, undoes binary spacing,
and inserts a break inside probability brackets. Separate cases require a specific diagnostic for
an indivisible wide probability, function argument or nested norm.
Another case places a short probability near the end of a paragraph line and checks both the
inline output, whose brackets stay on one line, and a damaged version that allows line breaks only
inside the brackets. A further case wraps an inline equation after its outer relation: the relation
must end the line at the right margin and the right side must start the next line at the left
margin. Its damaged version keeps the spacing after the relation at the line end. The inline
equations at the end of `math-layout.md` are compiled with `mhfe-check-parts` enabled, which
requires their parts and spacing to reproduce the width of each whole equation; a damaged
relation spacing must be refused. The full documents leave this check off, since measuring every
part would exceed the memory limit of the rendering container.
Two further cases place an explicitly enlarged norm and a modulus containing a norm near a line
end. Their opening and closing fences must stay on one line. Deliberately ignoring the scale
wrapper or confusing the two fence types must reproduce the split and fail the geometry check.
Nested moduli with identical fences, including explicitly sized and indexed variants, have their
own cases. Ignoring their opening roles must reproduce the same internal break. A unit test checks
that the adapter preserves these roles and index suffixes while leaving single pairs unchanged.
The combined error-term table has a separate case: its parenthesized formula must fit the
assigned column, and restoring the narrower column must produce the expected width refusal.
