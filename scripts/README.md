# Specification checks

Run these checks from the repository root with Python 3. Only the standard library is needed. Use
public test data exclusively.

```sh
python3 scripts/check-spec.py documents /path/to/bip39/src/language/english.rs
python3 scripts/check-spec.py analysis /path/to/bip39/src/language/english.rs ../mhfe/tests/fixtures/suite3-vectors/zero-12.json
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

These checks supplement review; they do not prove security or verify every claim in the documents.
