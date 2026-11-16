# AUD-013 — EasyCrypt/Lean comparison and current EasyCrypt follow-up

## Assessment

The two developments support the same core numerical security bounds under their respective
formal hypotheses. Current K5 uses `2^-128 + 11·2^-256` in both; current W5 retains original `k_S`
only in `δ_gen` while charging the appended seed query elsewhere. No false final inequality was
identified. **They do not establish literally identical experiments or unrestricted coverage of
every sentence of the specification.** Their domains, adversary semantics, record kernels and
exported ancillary results differ.

The existing Claude comparison is useful and substantially careful. Its detailed sections already
disclose most important limitations, including the genuine-record restriction, finite passphrase
corollaries, missing fractional optimizer/expectation/brackets and non-blind provenance. Those are
not concealed discoveries of this audit. Several concrete descriptions and its broad conclusions
nevertheless need correction. The independent port review confirms the intended mathematics and
exact header counts, with explicit limits on what that textual tool can establish.

After AUD-011, the owner confirmed that a separate round of EasyCrypt changes had finished. This
report separately checks that later state: exact finite-uniform `top2`, failure-returning capped
Theorem 5, corrected verification scripts and qualified publication claims. The original AUD-011
snapshot and its historical findings are preserved; the later additions are not retroactively
credited to it.

**Publication recommendation:** the current EasyCrypt artifact can be presented as checked results
within its prominently stated finite/lossless/ideal-model scope after ordinary packaging decisions.
Lean still needs its failure-masking checker command and its trust/scope descriptions corrected;
either extend its genuine-record experiment or identify the narrower theorem explicitly. Publish
neither package as a proof of exact unrestricted equivalence to all prose. Correct the existing
comparison and port narrative before using them as publication evidence. The two Low findings in
this report are documentary; AUD-012's conditional model/verification blockers remain separate.

## Identity, sequence and authority

- Completed UTC: {{COMPLETED_UTC}}; specification commit
  `98620cce3d75a011e751cb2d3c1c315b7c23669d`.
- Normative README SHA-256:
  `debbc9169b1a792f4f46f98de6d328672643183f07c430a12629d5e90a49f485`;
  supplement: `50affa7d36c43e10af0cff1e6aabaeb304cf3838e081bcb1317575bc94026346`.
- Existing comparison: `tmp/easycrypt-mhfe-2026-11-09/LEAN-COMPARISON.md`, SHA-256
  `db3c45d66d008cbb5d9e1ca4ca9a20d3138466fa630a59a657800e7e7aed3502`.
- Port account: `tmp/lean-review-2026-11-11/PORT-v4.35.md`, SHA-256
  `98f458f581d1eba79871eb18f0672765d941fc7ce7aed785d08b7ca354bfc526`.
- Baselines: [AUD-011](AUD-011-2026-11-12.md) and [AUD-012](AUD-012-2026-11-12.md), with paired
  JSON, source manifests and completed independent review records. Their final document hashes
  are recorded below. Their full tests are not recounted as new tests in this report.
- The reviewed packages are existing machine-local artifacts outside this repository's Git tree.
  No source tree was copied, no toolchain/cache was downloaded, and no proof/specification,
  comparison document or dependency was changed by this audit. Only audit records/tools/index
  were written. No commit, push, tag or release occurred.

The owner requested EasyCrypt first, Lean second and comparison third, with separate exhaustive
reports and a proof-specific layout. The actual sequence follows that order. Three specialist
scopes contributed independent source reviews; the coordinator challenged conclusions and checked
the execution evidence. Exact model/reasoning identifiers are not retained and remain null.

The complete 870-line existing comparison was read, including its appendices and dated updates.
Historical counts/toolchain results are treated as historical. Its heading identifies an older
supplement hash and Lean 4.28, while later sections explicitly discuss the 4.35 K5/W5 changes.
This report does not treat that mixed historical document as today's immutable package manifest.

## What agreement does and does not establish

| Property | EasyCrypt | Lean | Comparison verdict |
| --- | --- | --- | --- |
| Core final coefficients and success-event distinctions | Checked ideal games and explicit budgets | Checked PMFs/oracle programs and explicit budgets | Agree on audited core bounds; no mechanical cross-language equivalence theorem |
| Current K5/W5 | Strengthened current text | Strengthened 4.35 port | Confirmed; the old 4.28 sources intentionally retain former weaker statements |
| Genuine-wallet record in Theorem 2 | Depends on realized decoy Q/state/U record; no arbitrary full function-table argument | Depends on genuine context/full original tables; no later realized Q/U record | Final games do not contain one another; already disclosed by Claude |
| Passwords | Finite normalized alphabet, arbitrary prior | Finite/ranked alphabet and recoding support | Compatible with bounded normalized encodings; no concrete normalization verification |
| Passphrases | Finite arbitrary prior | Main deterministic T5 has genuine arbitrary-PMF transport; final W5/W6/W7 finite | No unrestricted equality of quantifiers |
| Adversaries | Lossless probabilistic modules under hard per-run budgets | Total OracleComp plus explicit independent PMF strategy mixtures | Both model randomness; no universal partial-executable-program representation theorem |
| Generation/selection | Operational loop and final theorems over covered rules | Exact selected-law/full-view bridges to the source law, final T5 not restated with policy binder | Both have meaningful bridges; “not connected” understates Lean coverage |
| Uniform top2 | Exact saturated identity added and freshly checked after AUD-011 | Exact saturated identity already checked | Current equality coverage agrees; old upper-only comparison was historically correct |
| Fractional top | Formula, universal upper bound, attainment and floor/ceil facts | Formula and needed universal/coarse upper bounds | Lean does not export full optimizer/lower-floor/general-real-x package |
| General adaptive total cost | Constant per-run envelope | Expected-top2 pair-counting component | Neither exports exact general-prior expectation-form source-game endpoint; uniform-cost results exist |
| G8/K5/W7 brackets | Exported attack/upper combinations | Checked lower/resource/upper components; final bracket assembly absent | Mathematical consequence versus exported full source-game result |
| Capped no-container generation | New final T5 seed/pair bounds checked at every fixed integer cap | Internal option/fallback laws; final no-container success-domination wrapper absent | Distinguish failure, fallback and conditional-on-success distributions |
| G7 | Lazy batch accounting and final depth bound | Actual batch program, exact serialization/result/count bridges and final bound | Both final bounds; intermediate batch-Early claims not separately exported in Lean |
| G10 phrase encoding | Abstract injections instantiated synthetically | Bit regrouping/checksum-dependent composition and query-cost bridges | Neither is a verified wordlist/parser/Unicode implementation |
| Creation refusal | Arbitrary lossless continuation with explicit refusal charge | Arbitrary PMF response with explicit refusal charge | No claim that repeated operational retry loops were fully implemented |
| Trust | EasyCrypt logics, Why3 and accepted SMT answers | Lean kernel and three permitted logical axioms; library definitions | Distinct proof engines, shared specification and non-blind statement provenance |

The stronger guarantee of a small kernel concerns validity **of its stated theorem**. It does not
by itself make the theorem's experiment closer to the prose. Conversely an operational EasyCrypt
game still has finite domains, losslessness and abstract encodings. No sound numerical probability
of an undetected shared modeling error follows from having two AI-written developments.

## Current EasyCrypt changes and previous finding dispositions

Only two mathematical source files changed after AUD-011. Removing the new blocks in memory
recovers their exact former hashes: Selection lines 763–803 and 939–1040; Theorem5 lines
1280–1334 and 1374–1427 in the new source. This is a byte-preservation check, not a copied tree
or a substitute for fresh checking. The new blocks add 252 lines; current 18-source total is
19,475 lines. The metadata and two verification scripts are separately hashed below.

Fresh strict checks cover both changed modules and the dependent W5W6/W7 endpoints, with zero
source `.eco` caches before/after and no weak/admit bypass. All four exit zero. The ordinary
source-independent script self-test also passes all four expected cases after correcting the
audit adapter described below. Every positive proof result is tied to unchanged pre/post hashes.

| Original ID | Baseline status | Later current-state verification |
| --- | --- | --- |
| AUD-011-BLD001 | Open: README loop masked failure | Verified at the new check.sh hash: fail-first/nonzero behavior tested |
| AUD-011-BLD002 | Open: existing weak cache bypassed -no-eco | Verified guard in new check.sh: rejects existing cache before compiler; compiler behavior itself remains unchanged |
| AUD-011-DOC001 | Open: exact-coverage wording lacked qualifications | Verified current README scope table/limitations; new uniform equality and capped T5 endpoints close two observations; finite/cost/encoding restrictions remain explicit |
| AUD-011-DOC002 | Open: ambiguous independence wording | Verified current explicit separate-development/non-blind provenance paragraph |

These are a later verification at uncommitted artifact hashes, with no fix/verification commit.
They do not rewrite the historical AUD-011 findings or assert that every formal scope difference
has disappeared. AUD-012's four findings remain open because its inputs are unchanged.

The new capped theorem counts failure as **no win**. It is not a bound conditioned on successful
creation. The generic transfer covers cutoff and creation refusal, and the existing
`deltacut + 2·2^-256 ≤ deltagen` slack absorbs both. The seed free-guess term and exact pair minimum
are retained. Exact uniform top2 includes saturation at both alphabet cardinalities. The detailed
new-source review below traces these facts.

The actual source checks cover both installed EasyCrypt release r2026.10 and the main
commit/toolchain used by AUD-011. They are targeted checks of changed/importing modules,
not a claimed new full 18-file replay or per-solver isolation. No new Lean compilation/replay was
needed: all 47 AUD-012 inputs remained byte-identical and its completed evidence was rechecked.

## Comparison-tool reproduction and limitations

The corrected original scripts reproduce exactly **2,582 same, 13 changed, 3 removed and 30 added**
parser keys. All three regenerated TSVs are byte-identical to the retained ones. Twelve public
synthetic snippet pairs exercise the actual parser/comparator. The `(N := N)` conclusion regression
is fixed. The snippets are textual tool probes, not extra Lean-checked security theorems.

The comparison excludes most definition values, inherited context and modifier columns, and is
not string-aware. It also treats named instances as whole-header identities. Equal source headers
do not establish equal elaborated types or unchanged meanings of referenced definitions. This is
relevant to the real finite-answer class migration and restored PMF name resolution. Independent
source/upstream-definition review supports their intended equivalence; no additional unintended
mathematical change was found. A stronger future tool should align elaborated types and reachable
non-proof definitions, with explicit cross-version constant correspondence.

The current GNU chapter diff is 661 additions/384 deletions across 37 changed/new chapter files;
the retained patch is 660/382 and the account says 618/380. The later relative Checkpoint-path edit
explains the retained/current patch drift. These use GNU alignment; Python difflib's 662/385 is
not evidence of further source edits. The two intentionally removed K5 allowance helpers are
explicit exceptions to the account's universal theorem-presence claim.

## Execution exceptions retained honestly

The first current-script self-test failed because this audit's initial adapter reused a runner
that automatically added `-no-eco`, preventing the deliberately weak synthetic cache from being
created. The script correctly stopped rather than claiming that its cache case passed. The
corrected audit adapter preserves caller cache options, runs under the already reviewed bounded
resource guard and retains each real compiler call. The original failed command/log remain local.
No package source, assertion or gate was changed to obtain the passing rerun.

The first targeted four-module run used the existing runner's default release-r2026.10
configuration. It passed. A second run explicitly selected main and its corresponding Why3/prover
configuration to verify the version named by the current README. The two runs are separate
toolchain evidence, not eight distinct mathematical module results. The self-test records identify
the binary/configuration used in each invocation.

Some targeted EasyCrypt commands recorded thermal pauses from the pre-existing runner. Accepted
commands finished with exit zero; a paused timeout is not credited as a proof. Physical memory
was sampled throughout and scopes retained the system reserve. The small parser probes needed
no heavy proof process. Original failures, controls and historical test totals are not added
together as successful theorem counts.

Initial report assembly resolved bare checksum-list filenames at the package root instead of
src/ and failed closed. A premature dependent validation then found no report to validate.
The source-root mapping was corrected; both original failures are retained. No checksum, proof
assertion or expected result was relaxed.

## Proposed replacement conclusion for the existing comparison

Both developments check the supplement's principal numerical bounds in distinct formal systems.
Their final theorems have different hypotheses and represented experiment families. The detailed
correspondence table, rather than a blanket equality claim, defines their common scope. In
particular their genuine-record kernels are incomparable, EasyCrypt passphrases remain finite,
Lean's arbitrary-PMF extension covers main deterministic Theorem 5, and some exact ancillary
assemblies are exported in only one development or neither.

Current K5 and W5 match the corrected text. Lean's actual batch and selection-law bridges should
be credited. EasyCrypt's later exact uniform-top2 and capped-failure endpoints should be dated and
bound to their new verified hashes. The independent builds/replays validate each statement in
its own environment; textual port-header comparison is supporting evidence with stated limits.

The two proof engines provide useful cross-checks without blind statement independence or a
formal cross-language equivalence theorem. Neither result certifies concrete primitive costs,
randomness, side channels or the Rust/browser implementation. A public claim should state these
boundaries and supply verification commands that propagate failure and exclude invalid caches.

