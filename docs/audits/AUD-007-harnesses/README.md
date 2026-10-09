# AUD-007 harness scripts

These scripts belong to the 2026-10-09 specification/supplement audit of commit
`2cd5e4c96a2bf2cc177f8b99b81fa7427bdf1b86` plus its recorded working tree. The initial and verified
final manifests are separate in the paired report. They are not a full-cost Argon2 replay or a
whole-program release test.

Run from the authoritative `mhfe_spec` checkout. The adjacent `mhfe` checkout and the workspace's
documented Cargo registry supply public vector fixtures, the BIP39 English list and the EFF list. No
private wallet data is needed. Python writes local evidence only under the ignored
`docs/audits/AUD-007-evidence/` directory. The scripts do not install dependencies.

| Script               | What it checks                                                                                                                          | Expected result                                                                                                        |
| -------------------- | --------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------- |
| `run.py`             | Initial snapshot, document/analysis checks, formatting, historical record validation, corpus checksums and recorded-key notation replay | Documents 15/15, analysis 64/64, 39 checksum entries and 17 suite-3 plus 9 archived suite-2 positive transcripts       |
| `documents_probe.py` | Bibliography identities against HEAD, first-citation order across specification then supplement, and local file/anchor links            | 64 references in order 1–64 and no broken links                                                                        |
| `profiles_probe.py`  | Independent BIP39 anchor, source-check hashes, pinned EFF data, password erasures and GF(2048) parity arithmetic                        | Two full source digests, three negative cases, four password vectors, 24 erasure repairs, four generators and 16 cards |
| `costs_probe.py`     | Documented arithmetic and synthetic Feistel skipped-round identities                                                                    | 50 arithmetic assertions and 60 algebra cases                                                                          |
| `vectors_probe.py`   | Suite-4 recorded-key round transcripts, validation tables, current suite-3 expectations and independent repair decoding                 | 10 positive transcripts, 240 round records, 67 early-validation cases and three repair examples                        |
| `validate_report.py` | Canonical schema, paired record IDs/statuses, all 32 coverage tasks, privacy and final source/harness hashes                            | A passed validation summary                                                                                            |

```sh
python3 -B docs/audits/AUD-007-harnesses/run.py checks
python3 -B docs/audits/AUD-007-harnesses/documents_probe.py
python3 -B docs/audits/AUD-007-harnesses/profiles_probe.py
python3 -B docs/audits/AUD-007-harnesses/costs_probe.py
python3 -B docs/audits/AUD-007-harnesses/vectors_probe.py
python3 -B docs/audits/AUD-007-harnesses/validate_report.py
```

The report validator uses the already available `jsonschema` package and the canonical schema in the
adjacent wallet-tools checkout. It checks the report's pinned bytes; after a deliberate source
change it must fail until a separately documented follow-up updates the bindings.

`run.py capture` creates an initial snapshot only when none exists. It refuses to overwrite an
existing snapshot. `run.py integrity` compares against that initial snapshot and exits nonzero after
any source change, including an authorized correction. This preserves the audit boundary; it does
not mean the corrected final snapshot failed its checks.

Recorded-key replay does not independently verify Argon2 outputs. Full-cost vector runs were
excluded by the owner. Three suite-4 wrong-password/settings outputs are structurally inspected, not
freshly decrypted. Synthetic skipped-round tests establish algebraic identities, not a lower bound
on every possible attack.

The focused CLI regressions are in the implementation's `scripts/verify-hidden-input.py`. With its
native debug binary built using the documented toolchain, the two relevant groups can be run as
follows from the `mhfe` checkout:

```sh
python3 -B -c 'import runpy; m = runpy.run_path("scripts/verify-hidden-input.py"); m["check_container_repair"](); m["check_repair_command"]()'
```

Both groups should pass, including detailed repair changes on stderr and the repaired container on
stdout. The report records the separate three rekey rule tests and BIP32 fingerprint known answer;
it does not claim a full-cost interactive rekey session.
