# AUD-003 harness scripts

These are the audit-only scripts of [AUD-003](../audit-03-2026-09-30.md), the review of the
specification text at commit `4b41a74e5de8f1d24d4018d31cc0fe50c0997334`, and of its addendum of
2026-09-30, which re-checked the corrected text. They produced the command logs the report cites.
Those logs are kept locally by the maintainer and are not published; the report states the commands,
counts and results.

The scripts are kept byte for byte as they ran. They use only public data: the official BIP39
English wordlist and the published test vectors.

| Script                  | What it checks                                                                                                  |
| ----------------------- | --------------------------------------------------------------------------------------------------------------- |
| `notation_check.py`     | Recomputes every salt, mask, state, container word and recovery result of the vectors from the README formulas |
| `document_checks.py`    | BIP 3 preamble, relative links and anchors, the reference list and its use, BIP39 four-letter prefixes          |
| `numbers.py`            | The numbers stated in the README at the reviewed commit                                                         |
| `supplement_numbers.py` | The figures of the supplement's Part I tables at the reviewed commit                                            |
| `security_table.py`     | The Security Considerations table as edited on 2026-09-30                                                       |
| `addendum_checks.py`    | The secret-PIM model against exhaustive search, the `11 - i` salt filter, and equal containers from two lengths |
| `run.py`                | Runs one command and writes `<name>.log` and `<name>.command.json` (command, UTC times, exit code, SHA-256)     |

## Inputs

- The official BIP39 English wordlist as the Rust source of the `bip39` crate, for example
  `$CARGO_HOME/registry/src/index.crates.io-*/bip39-3.0.0/src/language/english.rs`. The scripts
  check its SHA-256 against the official list.
- For `notation_check.py`: a folder that holds only the 17 positive suite 3 traces, and the suite 2
  vectors in `vectors/`. `vectors/suite3/` also holds `negative-cases.json` and
  `validation-cases.json`, which have other schemas, so link the 17 traces into a temporary folder
  first.

## How to run them

From the repository root, with Python 3 (the `--argon2` option also needs Python `cryptography`
and about 6 GiB of free memory):

```sh
W=/path/to/bip39-3.0.0/src/language/english.rs
T=$(mktemp -d); for f in vectors/suite3/*.json; do
  case "$(basename "$f")" in negative-cases.json|validation-cases.json) ;; *) ln -s "$PWD/$f" "$T/" ;; esac
done
python3 -B docs/audits/AUD-003-harnesses/notation_check.py "$W" "$T" vectors
python3 -B docs/audits/AUD-003-harnesses/notation_check.py "$W" "$T" vectors --argon2
python3 -B docs/audits/AUD-003-harnesses/document_checks.py "$W"
python3 -B docs/audits/AUD-003-harnesses/addendum_checks.py "$W" vectors/suite3/zero-12.json
python3 -B docs/audits/AUD-003-harnesses/security_table.py
```

Expected: `suite 3 positive vectors 17/17, suite 2 vectors 9/9`, four matching Argon2id calls with
`--argon2`, `0 FAIL` from the document and addendum checks, and `all rows agree` from the table.
`numbers.py` and `supplement_numbers.py` check the text of the reviewed commit, so some of their
lines refer to statements that have since changed.

These archived scripts print `FAIL` lines but may still exit with code 0. For a check that fails
properly, use [`scripts/check-spec.py`](../../../scripts/check-spec.py), which runs the document and
addendum checks and exits non-zero on any failure. `run.py` writes its records into the folder above
its own; to keep them out of git, copy it into the ignored `docs/audits/AUD-003-evidence/harnesses/`
before using it.
