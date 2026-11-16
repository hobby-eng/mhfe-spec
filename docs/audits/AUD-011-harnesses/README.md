# AUD-011 proof-audit harnesses

These tools belong to the EasyCrypt proof audit of specification commit
`98620cce3d75a011e751cb2d3c1c315b7c23669d`, completed on 2026-11-12. They do not
verify the Rust or browser application. No source is copied or modified by the checking tools.

The original proof package was outside this Git tree, in the workspace's ignored
`tmp/easycrypt-mhfe-2026-11-09/`. The report contains its complete source hashes. A public rerun
needs the corresponding EasyCrypt source package; this repository does not yet contain it.
Set `MHFE_EC_ROOT` to that package. Run the commands below from the specification repository.
Python 3 standard library, Linux, `sha256sum`, EasyCrypt and its configured provers are required.
Report validation additionally uses the already installed `jsonschema` package. The adjacent
`requirements.txt` reuses the previous audit's hash-pinned inspection environment; no installation
or dependency change was made by the audit.

## Static inventory and the shell-status reproduction

```sh
python3 docs/audits/AUD-011-harnesses/static.py \
  "$MHFE_EC_ROOT" docs/audits/AUD-011-evidence
```

Expected exit: 0. Output describes 18 files, 19,223 lines, 799 named lemma declarations, 109
explicit direct axiom declarations, 73 section hypotheses, no active bypass directive and
18 matching source checksums. The synthetic README-loop failure returns 0; the corrected
version returns 1. The harness itself fails unless those diagnostic observations hold.
The 104 named equivalence declarations are separately counted in the report; the static lemma
count intentionally excludes them and excludes generated/realized proof obligations.

`record.py EVIDENCE NAME COMMAND ...` runs an argument vector without a shell, preserves its exit
status, and writes the original log plus UTC command metadata and the log's SHA-256. An expected
negative compiler control therefore has a nonzero command status; do not relabel it as a passed
proof.

## Strict source checking

`compile.py SOURCE EVIDENCE RESOURCE_RUNNER NAMES...` checks each named `.ec` directly, without
copying sources. It refuses any existing source-directory `.eco` rather than deleting user files.
This is essential: `-no-eco` prevents writing a cache but can reuse an existing valid cache.
Every root must be checked, since loading a required theory is not the same as proving it again.

The original `RESOURCE_RUNNER` was the pre-existing machine-local
`../tmp/easycrypt-toolchain-2026-11-08/ec-run.py`, documented in that toolchain folder. It is an
external input to this harness, not a public file in this repository. It selects the configured
EasyCrypt switch through `EC_SWITCH`, `EC_PROVERS_BIN` and `EC_WHY3_CONF`, creates a dynamically
budgeted systemd user scope with no swap, and watches global memory/temperature. `compile.py`
raises its emergency memory floor to at least 5% of physical RAM and records five-second samples.
For a rerun, supply that runner or an equivalently reviewed compatible runner; the exact original
commands and runner identity are local evidence. No runner installation is performed here.

```sh
python3 docs/audits/AUD-011-harnesses/compile.py \
  "$MHFE_EC_ROOT/src" docs/audits/AUD-011-evidence-rerun "$MHFE_EC_RUNNER" \
  Model Suite3 Chain Collision KnownPair Delta2 Theorem4 K5 OneContainer Deniability \
  Instances Passphrase Generation Selection Theta2 Theorem5 W5W6 W7
```

Expected exit: 0 only when all 18 checks exit 0. The original audit checked Model separately and
the remaining 17 together; the report lists each unique source once. Output/logs may contain
warnings. `--include DIR` adds a read-only include directory for small independent controls.

## Cache diagnostic

This intentionally creates a weak cache for a **new synthetic false statement**, then runs strict
`-no-eco`, retains the own cache under an inactive suffix, and repeats the strict check. It never
uses a real proof source or treats the weak run as accepted proof evidence. `NEW_SCRATCH` must
not already exist. A Linux systemd user session with `MemoryMax` support is required.

```sh
python3 docs/audits/AUD-011-harnesses/cache_probe.py \
  "$MHFE_EASYCRYPT" "$MHFE_WHY3_CONFIG" "$NEW_SCRATCH" \
  docs/audits/AUD-011-evidence-cache-rerun
```

At the audited EasyCrypt revision, expected phase statuses are 0, 0, 1 and harness exit is 0.
The strict cached phase has an empty log. This demonstrates the verifier freshness defect; it
does not invalidate the actual cache-free development. A later EasyCrypt fix may change the
expected observation, in which case this historical diagnostic exits nonzero.

## Report and validation

`REPORT_TEMPLATE.md` is the proof-specific report introduction and execution template, adapted
with the owner's permission. It is not a change to the shared coding guide or audit standard.
`write_report.py` assembles the English Markdown/JSON pair only after all recorded compiles and
controls have the expected statuses and source hashes remain unchanged. It requires the local
snapshot, procedure files and reviewed correspondence notes in the original ignored workspace
audit folder; those notes are embedded in the report so the report stands alone. It anonymizes
home paths before writing published records. This generator is historical audit infrastructure,
not an automatic author of new audit conclusions.

`validate.py` checks schema, duplicate keys, IDs, source/report links, privacy, retained log hashes
and report-source consistency. Local evidence is ignored by Git and must not be committed.
The report is not a claim that the checker, its solvers or concrete primitives were audited.
