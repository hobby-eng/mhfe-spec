# AUD-012 Lean proof-audit tools

These harnesses check the current publication port against specification commit
`98620cce3d75a011e751cb2d3c1c315b7c23669d`. They operate on existing sources in place and put
derived artifacts/logs in ignored evidence. They do not copy a source tree, install tools,
fetch dependencies, edit proofs or publish anything.

The original source input is the machine-local workspace artifact
`tmp/lean-review-2026-11-11/port-v4.35/`, outside this Git repository. A rerun needs that source
package at the hashes in the report, Lean 4.35.0 and the locked dependency builds. Set
`MHFE_LEAN_PROJECT` and `MHFE_LEAN_TOOLCHAIN` to their locations. A Linux systemd user session
supporting bounded scopes is required. Python uses its standard library except report validation,
which reuses the existing hash-pinned `jsonschema` environment in `requirements.txt`.

Run from the specification repository, using a new evidence directory for a new audit:

```sh
python3 docs/audits/AUD-012-harnesses/check_lean.py compile \
  "$MHFE_LEAN_PROJECT" "$MHFE_LEAN_TOOLCHAIN" docs/audits/AUD-012-evidence
python3 docs/audits/AUD-012-harnesses/check_lean.py kernel \
  "$MHFE_LEAN_PROJECT" "$MHFE_LEAN_TOOLCHAIN" docs/audits/AUD-012-evidence
python3 docs/audits/AUD-012-harnesses/check_lean.py probes \
  "$MHFE_LEAN_PROJECT" "$MHFE_LEAN_TOOLCHAIN" docs/audits/AUD-012-evidence
python3 docs/audits/AUD-012-harnesses/check_lean.py lake \
  "$MHFE_LEAN_PROJECT" "$MHFE_LEAN_TOOLCHAIN" docs/audits/AUD-012-evidence
```

Expected source/kernel results: 40 modules each return 0 (39 chapters plus package entry).
Every source is compiled directly into fresh artifacts; the old local build directory is excluded
from LEAN_PATH. Kernel replay must follow a completed matching source phase. Do not combine
artifacts from another source snapshot with a new report. The ordinary Lake build is incremental
usability evidence and does not replace the direct source phase.
The `kernel` phase calls the official `replayFromImports` function from `LeanChecker` through
`SequentialReplay.lean`, sequentially for exact module names. This avoids CLI prefix matching
and redundant scans. In the original run it reused six completed individual CLI successes and
checked the remaining 34 modules, including the deliberately interrupted module again. The raw
termination status remains in evidence. Success markers and the coverage manifest must match
the exact requested list; this is the same kernel function, not a custom proof checker.

`probes/` contains intentionally invalid additions to a separate importing module: an unused
axiom, `sorry`, and native evaluation. Each command must return 1 with a recognized actual axiom
gate diagnostic; the `probes` harness returns 0 only if all three refusals occur. These are
diagnostic inputs, not admitted proof source. Never add them to the mathematical package.

Per-command UTC metadata and unmodified logs use the retained generic
`../AUD-011-harnesses/record.py`. Physical memory is sampled before each bounded job and every
five seconds; worker counts derive from the admitted budget. The current host has no swap and
is not the model requiring the workspace's special thermal policy. `check_lean.py` contains that
model-specific guard, but is an audit runner rather than a general machine scheduler.
`cache_headroom.py` was used during the original source phase after measured library-cache
pressure appeared. It only raises this audit's cache-dominated scope limits when their measured
current charges plus available physical memory still leave the system reserve and 256 MiB;
adjustments are retained in `memory-adjustments.jsonl`. It stops when the outer
`fresh-source-check.command.json` record appears. Run it alongside a recorded source phase only,
not as an unattended controller for arbitrary user scopes.

`REPORT_TEMPLATE.md`, `findings.json` and `write_report.py` preserve the owner-authorized
proof-specific report shape. The generator requires all source/kernel/probe statuses and the
full standard-axiom inventory before writing its assessment. It also requires the local reviewed
correspondence notes, embedded in the report for self-contained reading. It anonymizes owner home
paths before writing the Markdown/JSON pair. It is not a substitute for a new semantic audit.

`validate.py` verifies schema, paired finding IDs, privacy, source and log identities, module
counts and source-line bounds. No evidence directory is committed. The report's original
mathematical scope and explicit unexecuted checks remain binding on any interpretation of it.
