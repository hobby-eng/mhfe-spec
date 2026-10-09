# AUD-006 harness

These scripts belong to the AUD-006 release audit of the specification on commit
`2cd5e4c96a2bf2cc177f8b99b81fa7427bdf1b86` plus the uncommitted tree of 2026-10-09. They rerun the
automatic checks of that audit and rebuild its report. They do not run full-size Argon2id.

Inputs:

- the BIP39 English wordlist as a Rust source file, for example `bip39-3.0.0/src/language/english.rs`
  from the Cargo registry;
- `tests/fixtures/suite3-vectors/zero-12.json` from the reference implementation `mhfe`;
- Python 3 with `jsonschema`, Node.js with the repository's local Prettier, and `git`;
- for the report, the adjacent `multi-chain-wallet-tools` checkout, which holds the procedure files.

Run from the repository root:

```sh
python3 -B docs/audits/AUD-006-harnesses/run.py <english.rs> <zero-12.json>
python3 -B docs/audits/AUD-006-harnesses/build_report.py
```

`run.py` runs the specification checks (`documents` and `analysis`), the AUD-005 record validator,
the Prettier check, the three `SHA256SUMS` manifests, `git diff --check` and a check of every
relative Markdown link and anchor outside the archive and the drafts, skipping link syntax quoted in
code. It writes one log and one command record per check to the ignored
`docs/audits/AUD-006-evidence/`, prints one line per check and exits 0 only if every check passes.
The expected output is `exit 0` for every check and `link-check: 0 broken`.

`build_report.py` writes `docs/audits/audit-06-2026-10-09.md` and `.json` from `findings.py` and the
local evidence; it needs the evidence of a `run.py` run and the local baseline manifest
`source-manifest.sha256`. Home-directory paths are written as `/home/user`.
