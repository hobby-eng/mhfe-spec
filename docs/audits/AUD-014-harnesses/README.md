# AUD-014 proof-audit harnesses

These tools belong to [AUD-014](../AUD-014-2026-11-13.md). They check the existing
`tmp/code-proof-mhfe-core-2026-11-12/` artifact against authoritative `mhfe_core`
`df7ea54c37d90eb8737bc1d62c62760b5d4f64d7` and specification
`98620cce3d75a011e751cb2d3c1c315b7c23669d`. The artifact is machine-local and is not distributed
with this report. Exact input, dependency and tool hashes are in the report/JSON. Run from the
workspace root using the original existing checkouts; these tools do not clone projects or install
tools/dependencies. Only public/synthetic values are used.

## Inputs and outputs

- `check_lean.py` builds the actual root's28-module local import graph into a separate freshlib,
  excludes the original project's old build directory from LEAN_PATH, replays the exact modules
  through Lean's kernel, runs the declaration-origin axiom gate and three negative controls,
  checks two engine-contract witnesses, and checks ordinary cached Lake usability. It reads
  installed Lean4.35.0 and the existing project's pinned dependency artifacts. It imports the
  retained `AUD-012-harnesses/SequentialReplay.lean` adapter, and uses `AUD-011-harnesses/record.py`.
- `Inventory.lean` checks every declaration defined by an active module, including private/global
  generated code and models. It rejects any local axiom, sorry or native-decision axiom.
  `ContractWitnesses.lean` establishes that the native placeholder can meet EngineComputes while
  failing EngineOk. These are claims about that model, not native Argon2 execution.
- `regenerate.py` repeats the pinned Charon invocation from the original extraction log with locked,
  offline Cargo and a new ignored output directory, then runs pinned Aeneas from retained or fresh
  LLBC. It records actual child status and requires both generated Funs/Types hashes to match the
  original proof inputs. It never invokes the author's destructive regeneration scripts against
  the original artifact.
- `pipeline_probe.py` copies only the actual two regeneration/splice scripts into a tiny synthetic
  fixture. A fake translator writes partial output and exits7. The actual wrapper returns0 and
  actual splice creates Code/manifest, reproducing AUD-014-BLD001. No project tree is copied and
  the fixture is not compiled as the complete135-theorem package.
- `provenance.py` reads the author's literal rewrite/link recipe without executing its harness
  writer, verifies all source links and recorded hashes, applies the six prescribed replacements
  in memory and reconstructs all of Code in the manifest order. It writes only audit evidence.
- `environment.py` hashes installed tools, records versions/current Git identities and rechecks116
  frozen inputs plus22 imported model sources against the retained AUD-012 snapshot.
- `write_report.py` assembles MD/JSON from retained local execution evidence and the independent
  specialist notes under `tmp/code-proof-audit-2026-11-13/`, applying publication-only path privacy
  redaction. It is report assembly, not a proof checker. It overwrites a draft report, so do not run
  it after adding the final independent-review record unless intentionally rebuilding that draft.
- `validate.py` checks canonical schema, duplicate-free JSON, findings/status/MD parity, privacy,
  CHECK coverage, source/log hashes and the actual successful/control results. It needs the local
  ignored evidence and retained canonical procedure files. Python dependencies are hash-pinned
  through `requirements.txt`; this audit reused the existing validation environment.

Output goes to ignored `docs/audits/AUD-014-evidence/` and synthetic scratch under `tmp/`.
Original raw logs remain local; report privacy redaction does not modify them. Output/evidence is
not source and must not be committed. Existing original proof/Rust/spec sources remain unchanged.

## Rerun

The existing environment requires Linux user systemd scopes and unprivileged `unshare -rn` for
network-free extraction/build. The audit resource runner measures machine-wide available physical
memory, reserves at least5%, limits each own scope with MemorySwapMax=0, derives job budgets and
samples sustained jobs every five seconds. It applies the thermal rule only to the named board.
Do not weaken protocol parameters to fit a check.

For a new execution, choose a new ignored evidence folder and seed its `snapshot.json` from the
published JSON's `snapshot.inputManifest` before using resume. Existing evidence is retained rather
than deleted. Use the known matching artifact/tool/dependency inputs; these scripts do not bootstrap
a missing proof project. Example commands, with the audit's retained paths:

```bash
python3 mhfe_spec/docs/audits/AUD-014-harnesses/check_lean.py compile tmp/code-proof-mhfe-core-2026-11-12/lean workingspace/lean/lean-4.35.0-linux mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/check_lean.py kernel tmp/code-proof-mhfe-core-2026-11-12/lean workingspace/lean/lean-4.35.0-linux mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/check_lean.py inventory tmp/code-proof-mhfe-core-2026-11-12/lean workingspace/lean/lean-4.35.0-linux mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/check_lean.py controls tmp/code-proof-mhfe-core-2026-11-12/lean workingspace/lean/lean-4.35.0-linux mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/check_lean.py witnesses tmp/code-proof-mhfe-core-2026-11-12/lean workingspace/lean/lean-4.35.0-linux mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/check_lean.py lake tmp/code-proof-mhfe-core-2026-11-12/lean workingspace/lean/lean-4.35.0-linux mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/regenerate.py aeneas tmp/code-proof-mhfe-core-2026-11-12 mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/regenerate.py charon tmp/code-proof-mhfe-core-2026-11-12 mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/regenerate.py fresh-aeneas tmp/code-proof-mhfe-core-2026-11-12 mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/pipeline_probe.py tmp/code-proof-mhfe-core-2026-11-12 tmp/code-proof-audit-new-probe mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/provenance.py tmp/code-proof-mhfe-core-2026-11-12 mhfe_core mhfe_spec/docs/audits/AUD-014-evidence
python3 mhfe_spec/docs/audits/AUD-014-harnesses/validate.py
```

Compile/kernel/inventory/witnesses/real regeneration return0. The135 named-theorem axiom classes
are113 with all three standard axioms,14 with propext/Quot.sound and8 with propext alone. The full
origin inventory has2539 declarations and1416 theorem constants. Each negative control child exits1
with its expected rejection marker; the control runner returns0 when all three are rejected. The
failure probe itself returns0 when it reproduces wrapper0 after translator7. A cached ordinary
Lake build's3466-job result is not evidence of rebuilding every upstream dependency from source.

The report preserves the initial resource-interrupted Cipher check and inventory-driver parse
failure separately from successful corrected runs. `validate.py` selects Cipher's successful
resume record and verifies all28 final results. It does not erase historical failed attempts.
