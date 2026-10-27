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

## Independent implementations and emergency recovery

`independent-suite3.py` and `independent-suite4.py` implement suites 3 and 4 from this specification
alone, in Python, without code from mhfe-core or mhfe: Argon2id comes from OpenSSL through the
`cryptography` package and the Unicode 18.0.0 character database from `unicodedata2`. They check the
published vectors and the results of other implementations. Install their pinned packages first:

```sh
python3 -m pip install --require-hashes -r scripts/independent-suite3-requirements.txt
python3 scripts/independent-suite3.py vector --trust-argon2-keys vectors/suite3/zero-12.json
python3 scripts/independent-suite3.py passwords vectors/suite3/validation-cases.json
python3 scripts/independent-suite4.py validation vectors/suite4/validation-cases.json
```

Without `--trust-argon2-keys`, `vector` repeats every Argon2id call of a vector file.

**Emergency use.** When no compatible program is available, the same scripts can recover a real
container, or create one. They ask for the phrase and the password at the terminal and show them as
typed, like the result. A container of 24 words is a suite 3 container, and one of 12 to 21 words a
suite 4 container. The arguments come in this order: for suite 3 the stated length of the original
phrase, 0 if it is unknown, then the PIM and the memory level used at creation; for suite 4 only the
PIM and the memory level. Omitted values are 0, the defaults. For example, `decrypt 12 0 0` recovers
a suite 3 container of a 12-word original phrase made with the default settings, and `decrypt 0 1 0`
one of unknown length made with PIM 1:

```sh
python3 scripts/independent-suite3.py decrypt [WORDS] [PIM] [MEM]
python3 scripts/independent-suite4.py decrypt [PIM] [MEM]
python3 scripts/independent-suite3.py encrypt [PIM] [MEM]
python3 scripts/independent-suite4.py encrypt [PIM] [MEM]
```

`encrypt` asks for the original seed phrase and twice for the password, checks the container by
recovering it once and shows it with the suite identifier and the settings to record. Suite 3 takes
an original phrase of 12 to 24 words and always gives 24 words; suite 4 takes 12 to 21 words and
keeps the length.

Words may be typed in any letter case and by their first four letters. A reading marked verified
passed the suite 3 check of a short original phrase; any other reading is confirmed only by
comparing a known receiving address of the wallet. The emergency commands do not evaluate the
optional 16-bit wallet check of `MHFE-WALLET-CHECK-SEED-1`, and suite 3 names any further short
length whose check the recovered state also passes. Run the scripts on a trusted offline computer
only, with nobody watching the screen: Python does not erase the secrets from memory. From version
0.7.0 on they are part of every release archive of this repository, so that recovery does not depend
on the repositories of the implementations.

`bip39-english.txt` is BIP 39's English word list, taken from the `bip39` crate 3.0.0 (CC0-1.0); the
scripts check its SHA-256, `2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda`. The
two scripts come from mhfe at commit `8be344293a184a91f7d7a2260c5fdcceb229ec3d`, under the MIT
License in [`LICENSE-MIT`](LICENSE-MIT), with the emergency commands added.

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
