# AUD-016 trial-count audit tools

These tools belong to [AUD-016](../AUD-016-2026-11-14.md). They check the current machine-local
Lean and EasyCrypt security developments against specification
`3d880786b90daafaa6aa9d99e4c65b378711c418`. The artifacts are not distributed with the report:
`tmp/lean-review-2026-11-11/port-v4.35/` and `tmp/easycrypt-mhfe-2026-11-09/`. The report/JSON
bind their85 exact input files. No project clone, source copy, dependency installation or
specification edit is performed by these tools.

- `snapshot.py` freezes proof/spec/document inputs and refuses to overwrite a prior snapshot.
- `check.py lean` compiles all41 chapters plus the root into a new ignored freshlib, excluding
  the old local build path. It schedules at most two dependency-ready modules. External pinned
  libraries remain reused. `kernel` replays the exact42 fresh modules through Lean's installed
  kernel API using the retained AUD-012 adapter.
- `Inventory.lean` selects declarations by source-module origin, including global names that the
  package's namespace inventory omits. It checks6193 declarations/4004 theorem constants against
  the same three allowed standard axioms and rejects local axioms. The package's separate original
  checkpoint line remains6185/4003; the difference is seven metaprogram declarations and the
  global mathematical lemma PMF.filter.congr_simp.
- `check.py lean-controls` requires actual rejection of an unused local axiom, sorry and
  native_decide, with matching diagnostic markers. Each child exits1; the control runner exits0.
- `check.py ec` checks all23 original roots in strict no-eco mode, refuses caches and weak/admitted
  source, and uses installed EasyCrypt main ce19cb6/Why3 main configuration. It resumes only
  successful roots after checking all input hashes, retains failed summaries and uses distinct
  retry record names. `ec-controls` runs the existing four-case checker self-test with genuine
  false/true theorem and weak-cache cases.
- Execution reuses the measured AUD-014 resource guard and AUD-011 command recorder. Linux user
  systemd scopes, a5% machine-wide reserve, swap-free own jobs and five-second resource samples
  apply. `--shares` divides available admission headroom among concurrent jobs. After Lean finished,
  the EC run used `--shares 1`, giving more CPU/memory without changing proof/timeouts.
- `write_report.py` assembles the pair from retained evidence and three source-first notes in
  `tmp/trial-count-audit-2026-11-14/`. It applies publication-only home-path redaction; raw logs stay
  intact. Do not overwrite a completed report's final-review record by rerunning the draft writer.
- `validate.py` checks canonical schema, privacy, finding parity,85 input hashes,42 source/kernel
  results,23 final EC successes and retained failure evidence, inventories, controls and32 CHECK IDs.
  Python validation dependencies are hash-pinned through `requirements.txt`; no install was needed.
- [PROPOSED-WORDING.md](PROPOSED-WORDING.md) contains un-applied text proposals and their precise scope.

Run from the existing workspace root with installed pinned tools. For a new run select a new
ignored evidence directory and seed its snapshot from the JSON's `snapshot.inputManifest`, or run
the snapshot tool when intentionally capturing a new input. Do not overwrite this audit's evidence.
The retained execution paths were:

```bash
python3 mhfe_spec/docs/audits/AUD-016-harnesses/snapshot.py
python3 mhfe_spec/docs/audits/AUD-016-harnesses/check.py lean mhfe_spec/docs/audits/AUD-016-evidence
python3 mhfe_spec/docs/audits/AUD-016-harnesses/check.py kernel mhfe_spec/docs/audits/AUD-016-evidence
python3 mhfe_spec/docs/audits/AUD-016-harnesses/check.py inventory mhfe_spec/docs/audits/AUD-016-evidence
python3 mhfe_spec/docs/audits/AUD-016-harnesses/check.py lean-controls mhfe_spec/docs/audits/AUD-016-evidence
python3 mhfe_spec/docs/audits/AUD-016-harnesses/check.py ec mhfe_spec/docs/audits/AUD-016-evidence --shares 1
python3 mhfe_spec/docs/audits/AUD-016-harnesses/check.py ec-controls mhfe_spec/docs/audits/AUD-016-evidence
python3 mhfe_spec/docs/audits/AUD-016-harnesses/validate.py
```

Expected final runners return0. Initial KnownPair.ec strict failures under the smaller shared
budget are retained separately; no source/proof assertion/timeout was relaxed. Only local ignored
evidence and synthetic controls are written. No native code, browser, cryptographic vector or release
test is implied. Proposed wording does not establish physical timing behavior, workers/general-n
or capped generation exposing trials. Generated evidence is not to be committed.
