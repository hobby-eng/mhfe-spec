# AUD-011 — EasyCrypt proofs: validity, exact correspondence and publication readiness

## Assessment

All 18 current EasyCrypt sources passed fresh strict checking. No incorrect final security
inequality, misplaced success event or assumed security conclusion was identified under the
formal statements' premises. The revised K5 loss and W5 generation-budget exception are correct.

**The stronger claim of completely literal, unrestricted correspondence to every word of the
current specification is not established.** The passphrase domain is finite; attackers and refusal
continuations have explicit termination requirements; two unnumbered quantitative consequences
are represented by weaker forms; and several representation and abort/depth bridges remain
mathematical interpretation rather than separate checked theorems. These are not counterexamples
to the inequalities that EasyCrypt actually proves.

**Publication recommendation:** publish the proof source after repairing verification-command
status propagation and cache handling and tightening coverage/provenance wording. The evidence supports a useful
scoped formal result, not a claim that the entire utility or every unrestricted prose assertion
has been verified. If exact coverage of the whole prose is required, complete the extensions listed
below before using that claim. No commit, push, release, proof fix or specification edit was made.

## Record metadata and source identity

- Audit: AUD-011, repository sequence number 11; completion UTC: {{COMPLETED_UTC}}.
- Reviewer: Codex coordinator plus three read-only scopes (model/W family, deniability/G family,
  known-pair/K family), followed by independent challenges of identified discrepancies.
- Exact model identifier and reasoning effort: unknown; JSON records null rather than inference.
- Specification HEAD: `{{SPEC_COMMIT}}`; source baseline clean.
- The pre-existing proof package is machine-local `tmp/easycrypt-mhfe-2026-11-09/`, outside
  the specification Git tree. `<EC>` below denotes that package. Source locations use its `src/`.
- Source fingerprint: `{{SOURCE_FINGERPRINT}}` (SHA-256 of the canonical
  JSON file manifest; includes 18 sources, six package documents/manifests, and the two spec texts).
- Normative README SHA-256: `debbc9169b1a792f4f46f98de6d328672643183f07c430a12629d5e90a49f485`.
- Supplement SHA-256: `50affa7d36c43e10af0cff1e6aabaeb304cf3838e081bcb1317575bc94026346`.
- Proof inventory: 18 files, 19,223 physical lines; 799 named lemma declarations and 104 named
  equivalence declarations. These explicit lexical categories are not a count of every generated
  or realized proof obligation. The README's 1,027-lemma total was not reproducible from a retained
  counting method; omit it or define and regenerate the intended measure.
- All manifest entries were rehashed before assembling this record; reviewed source bytes stayed
  unchanged. Unrelated workspace instruction/setup edits were preserved.

The proof README pins supplement commit `6161a3f` with correct hash `5364de02…8a87`. Current
HEAD additionally explains G7's A-first sequentialization and permits capped generation returning
failure. The former has a compatible proof route; the latter's zero-win-on-failure lift is informal.
Normative changes since that pin also include generation guidance and implementation metadata.
This audit compares against current HEAD, rather than silently treating the old pin as current.

## Scope, method and trust boundary

The report is adapted to a proof audit with the owner's explicit permission. It retains audit
identity, finding IDs, English report/JSON, source hashes, evidence, dispositions and schema,
while replacing application/browser checklists with mathematical correspondence and trust checks.
The legacy 32-check applicability map appears at the end. The shared coding guide was not edited.

The authoritative algorithm text is `README.md`; `docs/DESIGN-NOTES.md` is its explanatory
supplement. Reviewed claims include Deniability, all appendix-A numbered results, their games,
supporting constants, ranked-mass claims, selection rules, costs and matching attacks. The three
specialist annexes below supply exact source/text locations and explicit qualifications.
They are consolidated evidence, not three additional audits or independent certification.

The checking method combines (1) direct reading of definitions, module interfaces, hypotheses,
final signatures and critical proof paths; (2) independent discrepancy challenges; (3) fresh
strict source checking of every file; (4) positive/negative controls; and (5) static source and
hash inventories. It does not claim an independent handwritten rederivation of every auxiliary
tactic line. A passed proof certifies its formal statement relative to the trusted logic and
assumptions; correspondence of that statement to prose remains a reviewed mathematical judgment.

Trusted components include EasyCrypt's logic/program logics, its standard library and random-oracle
theories, Why3 translations/drivers, and the SMT solvers. This is not independent proof-object
replay in Lean's kernel. The official [EasyCrypt ambient-logic guide](https://easycrypt.gitlab.io/easycrypt-web/docs/tutorials/introduction-itp-program-logics/ambient-logic/)
describes sending SMT goals externally; the [reference manual](https://www.easycrypt.info/easycrypt-doc/refman.pdf)
explains weak checking. Local source inspection confirms default strict mode and the distinction
between strict and weak proof pragmas. Neither upstream implementation nor solver soundness was
audited here. Controls demonstrate rejection on these inputs, not universal soundness.

No concrete Argon2id/BLAKE2b/HMAC/PBKDF2 property, memory/time lower bound, actual randomness
quality, side-channel freedom, BIP39 parser or Rust/browser implementation correctness follows from
this audit. Those are excluded scopes, not failed mathematical checks. Lean and the old comparison
are audited in later separate reports; their previous assertions were not used as proof evidence.

## Fresh execution

Toolchain: EasyCrypt source commit `ce19cb6cbab4951e58553c36128e8a19f2f90c6a`, Why3 1.9.0,
configured Alt-Ergo 2.6.5, Z3 5.4.1 and CVC5 1.4.2. Effective configuration lists these provers.
The Alt-Ergo executable prints revision `997f541` for its version; the effective Why3 identity
is recorded separately. EasyCrypt binary SHA-256 is
`03800247446f6dd3f22fc60c3da53e026de83eda859379eb7a54ba4b3578c356`.

Every source was checked as the principal input in its own command. Required files alone are
not treated as rechecked proofs. No root `.eco` existed: `-no-eco` prevents cache writing but
does not bypass a valid existing cache. The rerunnable audit harness now refuses cached source
directories. No `Proofs:weak` or `admit` was inserted. Source inspection found no `admit`, `abort`
or active pragma in current sources. Successful compilation included an Alt-Ergo response failure
(another prover discharged that goal), unused unfolding targets and an initialization warning for
internal `Generation.DG.r21`; it is not characterized as warning-free. DG starts at i=-1 with
ok=false and a positive `ntr=2^80`, so the loop executes and samples r21 before its read. This
warning is not a demonstrated uninitialized execution or a missing proof hypothesis.
Development helpers that emit weak-check variants were not used for acceptance.

The machine had 15.3 GiB physical RAM. Available memory was measured globally with
`MemAvailable`; the runner uses a dynamically admitted memory cap, no swap and five-second
resource samples, with at least a 5% physical-RAM emergency reserve. This host's board is
another model, so CORE-53's rule specific to `NP950QED-KA2DE` is inapplicable. The existing runner
nevertheless imposed conservative thermal pauses. Passed runs remain passes; no pause-induced
timeout is reported as a source defect. Independent lightweight controls shared the measured
budget; no arbitrary memory padding or cryptographic-parameter reduction was used.

The retained command pattern, with home paths anonymized, is:

```sh
EC_SWITCH=mhfe-easycrypt-main \
EC_PROVERS_BIN=/home/user/Documents/bip_tools/workingspace/easycrypt-provers/bin-main \
EC_WHY3_CONF=/home/user/Documents/bip_tools/workingspace/easycrypt-provers/why3-main.conf \
python3 ec-run.py compile -no-eco -I <EC>/src <EC>/src/FILE.ec
```

The audit harness imports the existing runner and raises its emergency floor to 784 MiB;
each local `.command.json` retains the exact argument vector, UTC times, exit status and log hash.
These evidence files are **machine-local**, ignored by Git, and not public download links.

| Source | Exit | Seconds | Output SHA-256 |
| --- | --- | --- | --- |
