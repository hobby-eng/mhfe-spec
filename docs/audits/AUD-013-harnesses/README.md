# AUD-013 comparison and later EasyCrypt verification tools

These tools support AUD-013 against specification commit
`98620cce3d75a011e751cb2d3c1c315b7c23669d`. They check existing artifact trees in place;
they do not create project copies, edit proofs, install dependencies or publish anything.
All derived files belong in ignored local evidence. The Markdown report embeds the semantic
reviews and their limitations; running these scripts alone does not repeat that review.

Inputs are the original frozen Lean snapshot, current 4.35 port, original declaration tools and
retained TSVs, existing Claude comparison/port account, current EasyCrypt package and installed
toolchains at the report's hashes. They are machine-local artifacts outside this Git tree.
A rerun needs those packages; the audit report is not a source distribution of them.
Set `MHFE_LEAN_REVIEW` to the directory containing snapshot, port-v4.35, tools and out-v4.35.

From the specification repository, the lightweight port-tool rerun is:

```sh
python3 docs/audits/AUD-013-harnesses/port_tools.py \
  "$MHFE_LEAN_REVIEW" docs/audits/AUD-013-evidence/port-tools-final
```

It executes the unmodified original textual extractor/comparator, verifies byte-identical
retained TSVs, exercises twelve public synthetic snippet pairs, and records GNU chapter diff
statistics. Every subprocess has UTC metadata, status and raw output hash. A diff status1 means
text differs, as expected; other failures are rejected. The snippets are not Lean proofs.
Expected original counts: same2582, changed13, removed3, added30. Expected current GNU chapter
diff: 661 additions,384 deletions,37 changed/new chapter files. Inputs at other hashes require
a new audit and new expected evidence, rather than relaxing these assertions.

Current EasyCrypt source checks reuse AUD-011's strict, cache-refusing harness. Set
`MHFE_EC_SOURCE` to src/, and `MHFE_EC_RUNNER` to the existing bounded ec-run.py toolchain
runner (an explicit input, not downloaded). Select its installed switch/provers/configuration
explicitly; the original default runner selects release r2026.10.
`environment.py WORKSPACE OUTPUT.json` records both installed compiler commits/binary hashes,
Why3 configurations and prover versions/hashes; it performs no installation or network access.

```sh
EC_SWITCH=mhfe-easycrypt-main \
EC_PROVERS_BIN="$MHFE_MAIN_PROVERS" EC_WHY3_CONF="$MHFE_MAIN_WHY3" \
python3 docs/audits/AUD-011-harnesses/compile.py \
  "$MHFE_EC_SOURCE" docs/audits/AUD-013-evidence/current-main-proofs \
  "$MHFE_EC_RUNNER" Selection Theorem5 W5W6 W7
```

Expected: all four modules exit0, no source caches, no weak/admit bypass. These are changed and
dependent modules, not a new full18-source replay. The report records a separate successful
release-r2026.10 run. Do not merge their statuses into eight distinct theorem-module results.

`easycrypt_adapter.py` exposes a selected installed binary to the package's four-case
check-selftest.sh while preserving its intentional cache options. It uses AUD-012's existing
bounded resource guard and AUD-011's command recorder. A Linux systemd user session is required.
Set these environment variables before calling the package's self-test:

- `MHFE_AUDIT_EC_BINARY`: exact EasyCrypt executable;
- `MHFE_AUDIT_WHY3_CONFIG`: selected Why3 configuration;
- `MHFE_AUDIT_PROVERS_BIN`: directory of the matching provers;
- `MHFE_AUDIT_EVIDENCE`: ignored directory for individual compiler records;
- `EASYCRYPT`: absolute path to this adapter;
- `TMPDIR`: a scratch directory under the workspace tmp/ tree.

Expected case statuses are1 (compiler failure),2 (cache refused),1 (false theorem),0 (true theorem),
with overall self-test exit0. Weak cache creation is deliberately confined to synthetic inputs;
it is never accepted mathematical evidence. The initial audit-adapter failure is retained in the
report. The corrected adapter permits intentional cache creation; it does not weaken check.sh.

`REPORT_TEMPLATE.md`, findings.json and write_report.py assemble the proof-specific report.
Generation requires matching source hashes, in-memory recovery of both old source hashes after
removing only new blocks, completed four-module checks on both toolchains, both successful
self-tests, exact reproduced header counts and unchanged validated baseline report identities.
The local semantic notes are embedded for a self-contained report; they are required inputs
to generation, not supplied by a parser run. Owners' home paths are anonymized before publishing.

`validate.py` checks duplicate-free JSON/schema, immutable finding parity, privacy, all current
input/log hashes, the later previous-finding verification entries, all32canonical CHECK IDs and
retained TSV equality. JSON validation reuses the existing hash-pinned jsonschema environment:

```sh
python3 docs/audits/AUD-013-harnesses/write_report.py
python3 docs/audits/AUD-013-harnesses/validate.py
```

No clean installation, external Lean checker, full upstream library/solver audit, implementation
suite or release is implied. The baseline AUD-011 and AUD-012 records remain separate snapshots.
