# MHFE formal proofs

Start with the result statements in the table below. Each chapter keeps a mathematical argument
with its operational definitions and supporting lemmas. `Checkpoint.lean` imports the chapters
and requests the single common axiom report; the logs and earlier source snapshots are outside
this directory.

## Results to read

Every declaration below starts with `MhfeLean.`. The assumptions precede the colon; the conclusion
follows it. `PMF` is a discrete probability distribution. Applying a Boolean experiment to `true`
gives its success probability. `ENNReal` is a nonnegative extended real, with subtraction truncated
at zero. No actual mnemonic, seed or password is inserted into these proofs.

| Supplement result                                           | Chapter                                                                                                                                                              | Entry point                                                                             |
| ----------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------- |
| Lemmas 1–3                                                  | [Feistel](Feistel.lean)                                                                                                                                              | `Lemma1.consistency`, `Lemma2.uniform_and_independent`, `Lemma3.network_uniform`        |
| Theorem 1                                                   | [Feistel](Feistel.lean)                                                                                                                                              | `Theorem1Feistel.joint`                                                                 |
| Theorem 2, both suites                                      | [DeniabilityGames](DeniabilityGames.lean)                                                                                                                            | `Theorem2.bits`, `Theorem2.suite3_error`, `Theorem2.suite4_error`                       |
| Theorem 2, real record drawn after the disclosed one        | [DeniabilityRecords](DeniabilityRecords.lean)                                                                                                                        | `Theorem2Records.bits`, `Theorem2Records.independent`                                   |
| Prepared-disclosure simulation                              | [Deniability](Deniability.lean)                                                                                                                                      | `PreparedDisclosure.simulation`, `.conditional`, `.failure`                             |
| Theorem 3                                                   | [ShortSources](ShortSources.lean)                                                                                                                                    | `Theorem3.bound`, `Theorem3Randomized.bound`                                            |
| G1                                                          | [ShortSources](ShortSources.lean)                                                                                                                                    | `G1.joint_resampling` and the source resampling arguments                               |
| G2–G5                                                       | [ChainMonitoring](ChainMonitoring.lean), [ChainEarly](ChainEarly.lean), [ChainCompletion](ChainCompletion.lean)                                                      | `G2`, `G3.lemma_g3`, `G4`, `G5` namespaces                                              |
| G6                                                          | [ShortSources](ShortSources.lean)                                                                                                                                    | `G6.bound`, `G6.randomized`                                                             |
| G7                                                          | [BatchQueries](BatchQueries.lean)                                                                                                                                    | `G7.bound`                                                                              |
| G8                                                          | [MatchingAttack](MatchingAttack.lean)                                                                                                                                | `G8.weighted`, `G8.coarse`, `G8.budgets`                                                |
| G9                                                          | [WalletSource](WalletSource.lean), [CreationRefusal](CreationRefusal.lean)                                                                                           | `G9Game.probability` and the source-specific refusal bounds                             |
| G10                                                         | [WalletData](WalletData.lean)                                                                                                                                        | `G10.bound`, `G10Direct.bound`                                                          |
| G10 matching attacks                                        | [WalletMatching](WalletMatching.lean), [DerivedWalletMatching](DerivedWalletMatching.lean)                                                                           | `G10Matching.bound`, `G10DerivedMatching.bound`                                         |
| K1–K4 and Theorem 4                                         | [KnownPairResampling](KnownPairResampling.lean), [KnownPairCross](KnownPairCross.lean), [KnownPairEarly](KnownPairEarly.lean), [KnownPairBound](KnownPairBound.lean) | `Theorem4.bound`, `Theorem4.randomized`                                                 |
| K5                                                          | [KnownPairAttack](KnownPairAttack.lean)                                                                                                                              | `K5.bound`, `K5.coarse_bound`, `K5.budgets`, `K5.refused_bound`                         |
| W1                                                          | [ShortSources](ShortSources.lean), [PasswordPairs](PasswordPairs.lean)                                                                                               | `W1.lemma_w1` and the pair-mass consequences                                            |
| W2                                                          | [GenerationBound](GenerationBound.lean)                                                                                                                              | `W2Source.generation_bound`, `W2Source.joint_generation_bound`                          |
| W3–W4 and Theorem 5                                         | [WalletResampling](WalletResampling.lean), [WalletCollision](WalletCollision.lean), [SeedPairs](SeedPairs.lean), [WalletSource](WalletSource.lean)                   | `Theorem5.seed_bound`, `Theorem5.pair_bound`                                            |
| Theorem 5, arbitrary passphrase alphabet                    | [PassphraseDomains](PassphraseDomains.lean)                                                                                                                          | `PassphraseRefusal.seed_bound`, `PassphraseRefusal.pair_bound`                          |
| W5                                                          | [WalletRecovery](WalletRecovery.lean)                                                                                                                                | `W5.bound`, `W5Randomized.bound`                                                        |
| Theorem 5 and W5, number of trials revealed                 | [TrialCount](TrialCount.lean)                                                                                                                                        | `Theorem5Trials.seed_bound`, `.pair_bound`, `W5Trials.bound`, `…TrialsRandomized`       |
| W6                                                          | [OrdinaryWallet](OrdinaryWallet.lean)                                                                                                                                | `W6.seed_bound`, `W6.pair_bound`, `W6.source_bound`                                     |
| W7, wallet/check/both tests                                 | [WalletPairAttack](WalletPairAttack.lean)                                                                                                                            | `W7Source.seed_refused`, `W7PairSource.refused`, their weighted and `top2` consequences |
| Hidden selection rules                                      | [SelectionRules](SelectionRules.lean)                                                                                                                                | `WalletSelection.chosen_eq`, `WalletSelection.actual_eq`, `SelectionRules.joint`        |
| Password encodings and ranking                              | [PasswordDomains](PasswordDomains.lean)                                                                                                                              | `PasswordDomains.joint`, `.combined_execution`, `.theorem3`, `.admitted_finite`         |
| Known passphrase, uniform dictionaries, adaptive total cost | [JointCost](JointCost.lean)                                                                                                                                          | `KnownPassphrase`, `UniformTop2`, `FullCostRandomized` namespaces                       |

For Theorem 3, follow the oracle model, chain monitoring, premature-query bound and completed-chain
count before reading the final assembly. For Theorem 4, add the two-chain resampling and intersection
arguments. Fractional credit belongs to the upper bound; no attack achieving it is asserted.

For Theorem 5, follow pair counting, profile generation, resampling, then useful seed-query counting.
The attack chapters can be read afterwards. Their false-match losses remain explicit. Theorem 2 has
its own width-parametric operational model in `DeniabilityModel`: half-state width changes with the
suite, while salts remain 128 bits and oracle keys remain 256 bits.

## Scope

The models count queries to independent ideal functions. They do not establish the physical memory
or time cost of Argon2id or PBKDF2, or verify their implementations. Security assumptions and query
budgets are premises of the result statements, rather than axioms added to Lean.

The password alphabet is finite and includes zero-prior labels an adversary may query. Ranking is
an exact relabeling of that whole alphabet, including admitted byte encodings. The original wallet
corollaries, the theorems on the number of trials and the matching-attack endpoints use finite
passphrase alphabets. Theorem 5 additionally has an explicit arbitrary-PMF passphrase transport:
finite observable windows retain the true source row, agree with the existing native source
experiment and have a vanishing prior tail. A uniform PMF on an infinite full function space is
never assumed.

Theorem 2 draws the real wallet's record from the real password, the source and the tables before
the decoy is drawn (`Theorem2.bits`), or after the disclosed record, from the whole realized
disclosure as well (`Theorem2Records.bits`). The first experiment is a case of the second
(`Theorem2Records.independent`). A record is fixed before the adversary runs.

Programs are total: they halt on every answer, and their branching is finite wherever the answers
are, which excludes only the record type of the deniability games. Independent private coins are
averaged through the randomized results and the common expectation lemmas; no theorem turns an
arbitrary probabilistic program that halts with probability one into such a mixture. Hidden source
selection may use trial order, pass/fail outcomes and coins independent of the trial values, must
terminate almost surely, and must reveal no search history or duration. The selection chapter proves
that such a rule, whose coins may depend on the `S` and `T` tables at a fixed passphrase, gives the
law of the sequential completion and of the whole experiment with the adversary (`chosen_eq`,
`actual_eq`); Theorem 5 is not stated again with a rule as a parameter. `joint`, for a policy
indexed by any context, is used by no statement. The sequential rule may also reveal its number of
trials and a duration that depends only on it and on independent coins: `TrialCount` proves Theorem
5 and W5 for it with `2^-120` added. Other rules that reveal their trials have no formal statement.

G7 has the supplement's final numerical bound, obtained through exact serialization of committed
batches. Its stronger intermediate batch-Early sentence is not separately formalized. K5's
six-level parallel-filtering observation is not a separate security theorem in this development.
The explicitly open extensions of the supplement remain open.

Some sentences of the supplement follow from the stated results without being stated themselves:
the brackets after G8, K5 and W7, the attainment of the fractional top and its lower bound, the
one-cost-budget bound for general secrets, and the bounds for a generation that stops at a limit.
The README at the root of the development lists every such difference.

## Rechecking

See "Checking the proofs" in the README at the root of the development. `./check.sh` builds every
module from its source, requires the inventory line that `Checkpoint.lean` prints after it has
rejected any axiom other than `propext`, `Classical.choice` and `Quot.sound`, and replays every
chapter through Lean's kernel with `leanchecker`. It stops at the first failure with a nonzero
status.
