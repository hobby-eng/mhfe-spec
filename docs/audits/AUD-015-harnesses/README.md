# AUD-015 remediation-verification tools

These tools belong to [AUD-015](../AUD-015-2026-11-13.md), the focused follow-up to AUD-014's
three findings. The proof still targets specification `98620cce3d75a011e751cb2d3c1c315b7c23669d`
and clean `mhfe_core` `df7ea54c37d90eb8737bc1d62c62760b5d4f64d7`. The reviewed specification
checkout is `3d880786b90daafaa6aa9d99e4c65b378711c418`. Exact current tool/document/proof hashes
are in the JSON input manifest. The existing proof artifact is machine-local at
`tmp/code-proof-mhfe-core-2026-11-12/`; it is not distributed in this audit repository.

`check.py` copies only three tool scripts into a tiny synthetic fixture, never a Rust/Lean project
checkout. It uses the measured resource guard and recorder from AUD-014/AUD-011, existing Linux
user systemd scopes and `unshare -rn`. No network, install, real secrets or original-source write
is needed. Genuine Aeneas reads original LLBC/manual inputs via symlinks and generates into the
fixture. Output goes to ignored local evidence; scratch stays under workspace `tmp/`.

From the workspace root, choose a **new** scratch directory for each invocation:

```bash
python3 mhfe_spec/docs/audits/AUD-015-harnesses/check.py regression tmp/code-proof-mhfe-core-2026-11-12 tmp/new-aud015-regression mhfe_spec/docs/audits/AUD-015-evidence
python3 mhfe_spec/docs/audits/AUD-015-harnesses/check.py regression-no-file-guard tmp/code-proof-mhfe-core-2026-11-12 tmp/new-aud015-survivor mhfe_spec/docs/audits/AUD-015-evidence
python3 mhfe_spec/docs/audits/AUD-015-harnesses/check.py real tmp/code-proof-mhfe-core-2026-11-12 tmp/new-aud015-real mhfe_spec/docs/audits/AUD-015-evidence --label real-wrapper-current
python3 mhfe_spec/docs/audits/AUD-015-harnesses/check.py install-error tmp/code-proof-mhfe-core-2026-11-12 tmp/new-aud015-install mhfe_spec/docs/audits/AUD-015-evidence
```

- `regression` runs all13 supplied cases against the actual corrected scripts, expecting exit0.
- `regression-no-file-guard` removes only the explicit output-presence guard in the fixture copy.
  All13 cases still pass; missing output is rejected downstream. This verifies the named survivor,
  not the author's complete nine-mutant campaign.
- `real` runs the complete corrected wrapper with the installed pinned Aeneas and expects Types,
  Funs, Code, replaced blocks and manifest hashes to match. It records LLBC's hash and requires it
  to remain unchanged during the run. Use a distinct label/evidence directory to preserve an old run.
- `install-error` first records a valid synthetic output, then replaces the fixture's Code target
  with a directory and requests an updated recording. The wrapper correctly exits1, but its
  unchanged-files diagnostic is false: Funs changes and the old manifest remains. The harness
  itself returns0 only when that concrete Low witness is reproduced. It never compiles the fixture
  as the actual135-theorem proof package.

`write_report.py` assembles the MD/JSON pair from retained local evidence and the two independent
notes under `tmp/code-proof-audit-followup-2026-11-13/`, applying publication-only path redaction.
It is not a proof checker and must not overwrite a completed report's final-review record.
`validate.py` checks schema, privacy, original-ID verification, new finding parity, source/log
hashes, actual outcomes and32 canonical IDs. It requires the retained ignored evidence and
canonical procedure copies from AUD-011. Python validation dependencies are hash-pinned through
`requirements.txt`; the existing environment was reused without installation.

No fresh source/kernel replay is claimed here: all35 recorded Lean inputs remain identical to
AUD-014. The current cached Lake check uses AUD-014's `check_lean.py lake` phase. Full Rust/native/
browser/WASM/vector/release checks are outside this focused follow-up. Raw logs and generated
fixtures are local evidence and must not be committed.
