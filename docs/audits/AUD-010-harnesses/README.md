# AUD-010 harnesses

These scripts support the pre-release audit of specification 0.7.0 at commit
`13215935bcdd320539a93e678cec374ba556528f`. They use public fixtures only. They do not publish,
tag, commit, change protocol sources, or create another project checkout.

From the repository root, record a check with:

```sh
python3 docs/audits/AUD-010-harnesses/record.py documents -- python3 scripts/check-spec.py documents /path/to/bip39/src/language/english.rs
```

The command exits with the checked command's status. It retains the complete output, exact command,
UTC timestamps, environment overrides, exit code and SHA-256 in the local, Git-ignored
`docs/audits/AUD-010-evidence/` folder. Reusing an evidence name is refused. Use the Cargo-registry
wordlist and Python dependency locations documented in `AGENTS.md` and `scripts/README.md`.

The audit report distinguishes fresh execution, retained evidence, source review and mathematical
reasoning. Passing these scripts is not formal verification of the cryptographic proofs.

The owner requested completing the interrupted AUD-010 instead of allocating another report.
The previous attempt's raw scripts and logs remain local in the ignored evidence folder, under
`interrupted-attempt-harnesses/` and `interrupted-attempt/`. Its project-copy runners are not
published here or rerun. Some unchanged command logs name the temporary execution namespace used
before consolidation; these are historical command strings, not current paths to copy verbatim.

## Reproduction inputs and commands

`python-contracts-probe.py` loads the actual suite modules but replaces only the Argon2 boundary
with a recorder that stops before work. It uses the public fixtures in `vectors/`, an explicit
192 MiB address-space cap and a 20-second CPU limit. It needs the packages already installed in
the workspace's `workingspace/mhfe-python` location. It reports observed admission behavior as
JSON and returns nonzero when an invalid input reaches the KDF boundary. The normal-mode cases
currently do so with invalid counts/settings. The original exploratory script and its exit-zero
logs remain local and unchanged; this published harness adds an admission-failure exit status.
The `tampered-fixture` mode deliberately alters a public expected mask only in memory: normal
Python must return a nonzero status; optimized Python's zero status demonstrates the separate
unsupported-mode caveat.

`python-contracts-static.py` is the original public-data companion probe, with only its audit label
updated after consolidation. It reports syntax, dependency versions/hashes, creation-check code,
the profile helper's Unicode behavior and post-permutation recovery metadata. It performs no
Argon2 work. Assertions about its public inputs and syntax fail nonzero; its JSON observations
are reviewed in the report and are not a green release-acceptance signal.

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=../workingspace/mhfe-python python3 -B docs/audits/AUD-010-harnesses/python-contracts-probe.py
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=../workingspace/mhfe-python python3 -B docs/audits/AUD-010-harnesses/python-contracts-probe.py tampered-fixture 3
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=../workingspace/mhfe-python python3 -B docs/audits/AUD-010-harnesses/python-contracts-static.py
```

`emergency-runtime.py` runs real encryption, its creation check and recovery on public suite 3
zero-12 and suite 4 same-length-nonzero-12 fixtures. It keeps the specified 2 GiB memory,
12 passes and four lanes; each child has a 2.75 GiB address-space cap and starts only with at
least 6.75 GiB available, preserving a 4 GiB reserve. Run no other heavy job alongside it.
Optional operation arguments permit resuming without repeating successful expensive operations:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=../workingspace/mhfe-python python3 -B docs/audits/AUD-010-harnesses/emergency-runtime.py 3-encrypt 3-decrypt 4-encrypt 4-decrypt
```

The check expects each exact fixture container and exact recovery line, with its verification
label. It returns nonzero on a mismatch, child failure, timeout or insufficient memory. All
four operations passed in the audit across recorded runs. Earlier harness/resource failures are
retained separately; corrected exact-line checks were also applied to the saved stdout, avoiding
another expensive replay. These two samples do not replace a full new corpus replay.

`repair-replay.py` uses the frozen independent AUD-007 GF(2^11) decoder to reproduce all three
published damaged-container examples, without Argon2. It needs the Cargo-registry `english.rs`
at the location in `AGENTS.md`. `check-links.py` is the previous attempt's read-only link checker;
it checks current tracked Markdown and intentionally excludes historical archive/audit links.

```sh
python3 -B docs/audits/AUD-010-harnesses/repair-replay.py
python3 -B docs/audits/AUD-010-harnesses/check-links.py
```

After the repository's documented `node scripts/build-pdfs.mjs` succeeds, the following scripts
check structure/text identity and make labelled contact sheets. `pdf-structure.py` needs pypdf
(the audit used the existing document runtime, version 6.10.0), and `pdf-contact-sheets.py` needs
Pillow (12.1.1 was already available). `inspection-requirements.txt` pins these and the JSON-schema
validator with their PyPI archive hashes for `pip install --require-hashes` in the workspace's
approved Python dependency location, if the existing runtime is unavailable. The audit installed
no packages. The scripts edit no PDFs.

```sh
python3 -B docs/audits/AUD-010-harnesses/pdf-structure.py
python3 -B docs/audits/AUD-010-harnesses/pdf-contact-sheets.py
```

Both return nonzero on a failed assertion. Contact sheets must match a successful per-attempt
verification record and artifact hashes; their visual review remains a human/agent action.
`write-report.py` only assembles the paired report from the retained local evidence bundle; it
does not repeat the audit or infer missing results. `validate-report.py` validates that report,
the source bindings and evidence after assembly.

`unknown-token-probe.py` checks a late allegation that word-lookup errors echo their input.
It runs four real CLI refusals with a synthetic unknown token, all before Argon2. On the audited
Python 3.14.4 it exits zero: the errors omit the token, so the allegation was not accepted as a
current finding. A different interpreter can have different diagnostic text; any failure is
reported as such, rather than silently attributed to the audited runtime.

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=../workingspace/mhfe-python python3 -B docs/audits/AUD-010-harnesses/unknown-token-probe.py
```
