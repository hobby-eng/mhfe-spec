# AUD-009 harnesses

These checks support the full-scope specification, supplement and PDF-conversion audit of
`330cd0baec17e444a443ec65ad723a43343e748d`. They do not change the protocol, documents,
published PDFs or vectors and do not execute Argon2. Use public fixtures only.

Run from the existing repository root. Node.js 26.10.0 and the exact PDF dependencies in
`tooling/pdf/package.json` must already be installed in the workspace's isolated PDF toolchain.
No command below installs dependencies or creates another project checkout.

## Command recording

`record.py` uses Python's standard library to capture a child command's original output, UTC
execution times, exit code and output SHA-256 in the ignored `AUD-009-evidence/` directory. It
returns the child's exit code. The report lists the actual commands and any required environment
settings; inherited environment is not exhaustively copied into command records.

```sh
python3 docs/audits/AUD-009-harnesses/record.py documents python3 scripts/check-spec.py documents /path/to/bip39/src/language/english.rs
python3 docs/audits/AUD-009-harnesses/record.py analysis python3 scripts/check-spec.py analysis /path/to/bip39/src/language/english.rs ../mhfe/tests/fixtures/suite3-vectors/zero-12.json
```

Expected on the audited snapshot: 15 document checks and 64 analysis checks pass, respectively,
with exit code zero. These counts do not include a proof verifier or an Argon2 replay.

## Independent conversion expectations

`parser-probes.mjs` calls the production Markdown entry point and checks fixed expectations for
grouped multiplication, quoted characters, malformed script arguments, script-order ambiguity
and algorithm names. Correct spaced multiplication, explicit labels and refusal of an unclosed
group are controls.

```sh
MHFE_PDF_DEPENDENCIES=../workingspace/pdf-toolchain node docs/audits/AUD-009-harnesses/parser-probes.mjs
```

Replace the dependency path if the existing isolated installation has another location. On the
audited snapshot the command intentionally exits **1**: five assertions expose four independent
converter defects, while two control assertions pass. A correction should make all seven pass;
the harness does not weaken expectations to accept the current conversions. The paired report
distinguishes currently affected notation from inputs absent from the published documents.

## Reduced mathematical models

The two independent Python enumeration scripts retain the sources of the mathematical
reviewer's original inline experiments (only a final empty line was removed from `math-models.py`
for publication; original and follow-up hashes are recorded separately). Python's standard library and exact rational arithmetic
provide an implementation independent of the JavaScript PDF converter. They use tiny synthetic
domains, not private data or reduced production cryptographic parameters.

```sh
python3 -B docs/audits/AUD-009-harnesses/math-models.py
python3 -B docs/audits/AUD-009-harnesses/math-k5.py
```

Expected: exit zero. The first checks G1/K1 joint laws, prefix/suffix counts, fractional weights,
top2 sets, the s1 charge, rejected-point erasure, selection rules and narrow-filter arithmetic.
The second checks 1,536 adaptive K5 cases. A passing finite model is supporting evidence for the
corresponding step, not a proof of Theorems 3-5. The original command records preserve unavailable
timestamps as null; the later evidence-retention time is not substituted for execution time.

## Report consistency

```sh
node docs/audits/AUD-009-harnesses/validate.mjs
```

Expected after the paired audit records exist: exit zero and a local
`report-validation.json`. This checks the keywords used by the pinned canonical JSON schema,
paired finding IDs, all 32 coverage tasks, report privacy and unchanged reviewed source hashes.
The audit-index addition is the only allowed change among the baseline tracked files. This
small validator is not a general JSON Schema implementation or a mathematical proof checker.

The report also records an independent validation using the already available Python
`jsonschema` package; no new package was installed. Historical audit scripts remain unchanged,
and their old results are not relabelled as new executions.

## Authorized remediation follow-up

The original baseline failures above are retained. After the AUD-009 fixes, all seven unchanged
conversion probes must pass (exit zero); the production notation tests additionally check literal
MathML, multiplication and malformed-input variants. The canonical Docker PDF build runs these
tests together with its layout and artifact checks.

```sh
python3 -B docs/audits/AUD-009-harnesses/rejection-model.py
node docs/audits/AUD-009-harnesses/validate.mjs --remediation
```

The first command checks 24 finite exact-rational examples of the conditional-sampling coupling,
including singleton distributions and zero allowed mass. It is not a proof checker. The second
checks the follow-up source hashes and dispositions while retaining the baseline identities.
Baseline validation still fails if reviewed sources changed. Both validation modes require the
original local-only `AUD-009-evidence/snapshot.json`; that snapshot is not published. Schema and
report checks can also be performed independently from the committed JSON and shared schema.
The follow-up records distinguish original harness hashes from later validator/README changes.
