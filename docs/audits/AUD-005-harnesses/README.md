# AUD-005 record metadata harness

This harness belongs to the document-only AUD-005 review of specification commit
`8e65639917e8c88aeaf43ff9d5c99d3c42ba9c13`. It captures fingerprints of `README.md` and
`docs/DESIGN-NOTES.md` and checks the audit records. It does not execute MHFE, interpret vectors,
normalize passwords, benchmark, build, or test an application.

Inputs: this original checkout at the reviewed commit with unchanged reviewed documents; the
workspace and repository `AGENTS.md`; the four procedure files listed in `record.py` from the
adjacent `multi-chain-wallet-tools` checkout; the local `wallet-full-audit` skill; and, for
validation, the paired `docs/audits/audit-05-2026-09-30.md`/`.json` report and its local evidence.
Python 3 and the existing `jsonschema` package are required. No dependency installation is needed
in the reviewed environment.

Run from the `mhfe_spec` repository root:

```sh
python3 docs/audits/AUD-005-harnesses/record.py capture
python3 docs/audits/AUD-005-harnesses/record.py validate
```

Capture writes `snapshot.json`, `procedure-hashes.json`, and `environment.log`. Validation checks
the JSON schema with duplicate keys rejected, finding/remediation agreement with the Markdown,
all 32 coverage IDs, unchanged source/procedure bytes, report file links, and ignored/unstaged
evidence. Each invocation writes its actual command times, exit code and log hash, then refreshes
the local evidence manifest. Output says `passed` with exit 0 or describes a failure with exit 1.
The evidence is kept in ignored `docs/audits/AUD-005-evidence/`; it must not be committed.

These checks validate the audit record, not the truth of its cryptographic conclusions. The manual
review workpapers document the reasoning. Do not rerun capture over retained evidence after changing
the reviewed inputs: keep the original review identity and use a new audit for another snapshot.

The authorized AUD-005 remediation addendum keeps the original snapshot and fingerprints. For that
follow-up, run only `validate`: it compares current document bytes with the addendum's fingerprints
and writes a separate `remediation-validation` command/log pair. This supports the requested Git
amend without claiming that the amended HEAD is the original reviewed commit. The JSON addendum
also retains a reverse patch for recovering the baseline README from the corrected document.

When `AUD-005-publication.json` is present, `validate` checks its link to the remediation
fingerprints, current document fingerprints, published file hashes and reverse-patch applicability
with `git apply --check`. This reads the vector files only to hash their bytes; it does not recompute
their outputs. The command/log pair is named `publication-validation`. The publication reverse
patch was produced with `git diff -R` and reconstructs the remediation document snapshot; the
report's earlier reverse patch then reconstructs the original audit snapshot. The original audit
scope, findings and fingerprints remain unchanged.

A document may be edited again after the publication record was written. Such an edit is listed in
`subsequentEdits` of `AUD-005-publication.json` with the new hash and a reverse patch to the bytes
first published with the record, and `publishedFiles` then holds the new hash. `validate` checks
each entry, recovers the first published bytes from it and runs the fingerprint and baseline-patch
checks on those bytes, so the audited documents stay recoverable after an amend.

A procedure file can also change after the audit; the workspace `AGENTS.md`, for example, is not
under version control. Such a change is listed in `procedureChanges` of `AUD-005-publication.json`
with the audited hash, the current hash and a reverse patch to the audited bytes. `validate` accepts
a changed procedure file only through such an entry whose patch recovers exactly the audited hash,
checks the report against the audited schema and guide, and names the recovered files in
`procedureChangesRecovered`. The hashes recorded by the audit are never replaced, and an unlisted
change still fails.
