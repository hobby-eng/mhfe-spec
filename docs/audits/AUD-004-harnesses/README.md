# AUD-004 harness scripts

These are the audit-only scripts of [AUD-004](../audit-04-2026-09-30.md), the specification-only
audit by Codex at commit `240dab04de227938914de0a350f26a46cb0391cc` with its working-tree edits,
and of its remediation of 2026-09-30. They produced the records the report cites. Those records
are kept locally by the maintainer and are not published; the report states the commands and
results.

The scripts are kept byte for byte as they ran. They use only public synthetic inputs and the
repository's documents; none of them runs Argon2 or an MHFE implementation.

| Script                    | What it does                                                                                              |
| ------------------------- | --------------------------------------------------------------------------------------------------------- |
| `protocol-algebra.mjs`    | Checks the Feistel and packing rules algebraically with a mock round function (not MHFE's)               |
| `protocol-unicode.mjs`    | Checks the password rules against the Unicode data of the Node runtime                                    |
| `appendix-analytical.mjs` | Recomputes the supplement's attack-cost and cycle-walking figures                                         |
| `document_links.py`       | Links and citation numbering in `README.md` and `docs/DESIGN-NOTES.md`                                    |
| `remediation_checks.py`   | Links of the edited documents and that the protocol definitions stayed unchanged                         |
| `validate_report.py`      | Validates the paired Markdown and JSON records against the schema and the retained evidence              |
| `record_command.py`       | Runs one command and writes its log and command record into the evidence folder                          |
| `build_report.py`, `append_remediation.py`, `remediation_snapshot.py`, `final_integrity.py` | Build the report records, the remediation diff and the final hashes; they rewrite audit files, so do not run them over the published report |

## How to run them

The `.mjs` checks are self-contained. From the repository root, with Node.js 26:

```sh
node docs/audits/AUD-004-harnesses/protocol-algebra.mjs
node docs/audits/AUD-004-harnesses/protocol-unicode.mjs
node docs/audits/AUD-004-harnesses/appendix-analytical.mjs
```

Each should exit with code 0. The Python scripts find the repository root and the evidence folder
from their own location, `docs/audits/AUD-004-evidence/harnesses/`, where they ran. To rerun them,
copy them back there first; that folder is ignored by git:

```sh
mkdir -p docs/audits/AUD-004-evidence/harnesses
cp docs/audits/AUD-004-harnesses/*.py docs/audits/AUD-004-evidence/harnesses/
python3 -B docs/audits/AUD-004-evidence/harnesses/document_links.py
python3 -B docs/audits/AUD-004-evidence/harnesses/remediation_checks.py
```

`validate_report.py` also needs the local evidence of the audit, which is not published.
