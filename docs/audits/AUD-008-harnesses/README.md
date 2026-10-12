# AUD-008 harness

This folder belongs to the Codex Security specification review of current source based on commit
`c462e47d4abff8d69b75f5303051c4acd63344c1`. It does not change the protocol or rerun full-cost
Argon2.

`record.py` runs a supplied offline command from the repository root and records its exact
arguments, UTC start/end, exit code and output SHA-256 in the ignored `AUD-008-evidence/` folder. It
returns the command's exit code. Inputs must be public vectors or public wordlists. Existing
immutable harnesses are reused by the commands in the audit report; their historical evidence must
not be overwritten.

For example, from the repository root:

```sh
python3 -B docs/audits/AUD-008-harnesses/record.py documents -- python3 -B scripts/check-spec.py documents /path/to/bip39/src/language/english.rs
```

Expected: the individual checks and no `FAIL`, exit zero. A reported failed assertion or a nonzero
child exit propagates as a failed check. The analysis runner checks the result list even when a
historical harness originally returned zero on failure. The audit report lists actual results and
the limitations of every reused probe.

`transcripts.py` reuses the frozen independent notation checker to replay the 17 current Suite 3 and
nine archived Suite 2 positive transcripts with recorded Argon2 keys. `history.py` requires the
already available `jsonschema` package and validates the seven historical audit envelopes and their
paired identifiers; it does not rerun their old checks. `build_report.py` reads the retained review
payloads, current command records and shared procedure, validates the new audit envelope, and writes
the Markdown/JSON companion. Pass the retained Codex Security scan directory to it.

```sh
python3 -B docs/audits/AUD-008-harnesses/transcripts.py /path/to/bip39/src/language/english.rs
python3 -B docs/audits/AUD-008-harnesses/history.py
python3 -B docs/audits/AUD-008-harnesses/build_report.py /path/to/retained/scan
```

Expected: `passed` from both checks and `written` from the builder, exit zero; an assertion failure
or a schema violation returns nonzero. The builder uses the supplied scan's retained independent
review payloads; it does not create a new scan or regenerate the plugin's canonical report.
