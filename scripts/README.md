# Specification checks

Run these checks from the repository root with Python 3. Only the standard library is needed. Use
public test data exclusively.

```sh
python3 scripts/check-spec.py documents /path/to/bip39/src/language/english.rs
python3 scripts/check-spec.py analysis /path/to/bip39/src/language/english.rs vectors/suite3/zero-12.json
```

The wordlist argument is the Rust source containing the 2,048 quoted English BIP39 words, as in the
`bip39` crate. The analysis command requires the public suite 3 `zero-12.json` fixture with PIM 0
and memory level 0. It uses the recorded Argon2 outputs and does not recompute them.

The document check covers the preamble, links, reference list and word-prefix rules. The analysis
check covers the conditional secret-PIM model, the leaked-salt filter and equal packed states from
different source lengths.

The runner executes the frozen [AUD-003 harnesses](../docs/audits/AUD-003-harnesses/) and returns a
non-zero exit status if any check fails or the harness produces no valid result list. Use this
runner for new checks: the archived scripts print failures but do not reliably signal them through
their exit status. Their original bytes and recorded hashes remain unchanged.

The requirement check confirms that every sentence of the specification with MUST, SHOULD, REQUIRED,
RECOMMENDED or SHALL in capitals, with or without NOT, ends with exactly one requirement identifier
and that no other sentence has one. It also confirms that no heading, table or block quote states a
requirement, that the identifiers are unique and carry their section's topic code, and that the
appendix lists exactly the identifiers in use. With `--self-test` it also runs on altered copies of
the specification, each breaking one rule, and requires each to fail exactly the check for that
rule:

```sh
python3 scripts/check-requirements.py --self-test
```

The profile-vector check confirms that the JSON files in `vectors/profiles/` match their
`SHA256SUMS` and hold the values of the Markdown tables, and recomputes the wallet-check digests and
the password check words. It needs the BIP39 wordlist as above and the EFF large wordlist, for
example the copy vendored by mhfe:

```sh
python3 scripts/check-profile-vectors.py /path/to/bip39/src/language/english.rs /path/to/eff_large_wordlist.txt
```

These checks supplement review; they do not prove security or verify every claim in the documents.

## Document PDFs

With Node.js 26.10.0 and Docker installed, run from the repository root:

```sh
node scripts/build-pdfs.mjs
```

The script reads `README.md` and `docs/DESIGN-NOTES.md`, converts their mathematical notation to
LaTeX expressions, and produces PDFs with typeset formulas in `output/documents/`. It uses KaTeX and
Chromium; no TeX installation is needed, and a standalone `.tex` file is not produced. The build
checks formula syntax, source coverage, page layout and the finished PDFs, and retains images for
visual inspection.

See [Building and checking the PDFs](../docs/PDF-BUILD.md) for supported notation, workflow
behaviour, checks and updating the [PDF copies in Git](../docs/pdf/README.md).
