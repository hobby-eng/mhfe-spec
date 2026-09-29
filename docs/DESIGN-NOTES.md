# MHFE Design Notes and Analysis

This is a supplement to the MHFE specification in [`README.md`](../README.md). It is not normative
and does not define the format: it explains in more detail why MHFE is built the way it is and what
is known about its security. The specification's [Rationale](../README.md#rationale) explains the
design decisions; this supplement develops their analysis.

Part I is analysis written for suite 3. Part II is the detailed design discussion first written for
suite 2 and brought up to date for suite 3: its parameters, formulas and figures describe suite 3,
which differs from suite 2 in its identifiers, its Argon2id memory (2 GiB instead of 512 MiB), its
work-factor settings (a PIM range of `0..1023` and a new memory level, both bound into the salt and
mask messages) and its Unicode version for password normalization. `README.md` defines suite 3;
where the documents differ, `README.md` takes precedence. Words such as "must" and "should" in this
supplement describe the design; the requirements themselves are those of the specification. The text
of suite 2 as released is kept unchanged in the [archive](archive/README.md).

Mathematical notation in Part II uses GitHub-supported LaTeX.

## Contents

- [Part I. Analysis for suite 3](#part-i-analysis-for-suite-3)
  - [Why a state-derived salt and a Feistel network](#why-a-state-derived-salt-and-a-feistel-network)
  - [Security model](#security-model)
  - [Ciphertext-only guessing](#ciphertext-only-guessing)
  - [Known pairs](#known-pairs)
  - [What a guess costs](#what-a-guess-costs)
  - [Composition with the BIP39 passphrase](#composition-with-the-bip39-passphrase)
  - [Deniability](#deniability)
  - [Parameter rationale](#parameter-rationale)
  - [Final-word-preserving cycle walking (research idea)](#final-word-preserving-cycle-walking-research-idea)
  - [Open questions for review](#open-questions-for-review)
- [Part II. Detailed design discussion](#part-ii-detailed-design-discussion)
  - [Threat models and security discussion](#threat-models)
  - [Packing and recovery analysis](#universal-24-word-containers-for-shorter-sources)
  - [Final-word profile in detail](#final-word-preserving-cycle-walking-for-24-word-sources)
  - [Alternative Feistel geometries](#direction-a-and-direction-b-geometry-comparison)
  - [Implementation and measurements](#reference-implementation)

## Part I. Analysis for suite 3

### Why a state-derived salt and a Feistel network

**A constant salt would work, but it would help the attacker.** Encrypting 256 bits into 256 bits
without storing anything is easy on its own: derive one key as `Argon2id(password, constant)` and
use any 256-bit block cipher, such as Threefish-256 or a wide-block mode like HCTR2. Decryption
needs only the container, the password and the constant from the specification. The weakness is that
the constant is the same for every user. An attacker computes Argon2id once for each password in a
large dictionary and then tests that list of keys against every container in the world with a cheap
cipher operation. The expensive work is paid once and reused everywhere.

**The only unique material is the container itself.** MHFE stores no salt, so the one thing that
differs between two users' backups is the backup. The Argon2id salt must therefore come from the
data being encrypted, and decryption must be able to recompute it from the container. Some value
must therefore be available both before a step during encryption and after it during decryption.

**A Feistel network is a simple way to meet this requirement.** In each round the right half passes
through unchanged and becomes the next left half. The salt of every round is derived from that half.
The last round's salt comes from the left half of the container, which anyone holding the container
can read. Independently created containers therefore have different salt chains except when branch
values repeat or salts collide; these exceptions are negligible under the model below. An attacker
cannot ordinarily reuse a password's KDF work across such containers. In this construction the
unchanged half is what lets decryption recompute a different salt for every round. SLIP-0039 uses
the same idea with PBKDF2 [20].

Other structures considered here also offer a value that one round leaves unchanged, but none is
simpler:

- An unbalanced Feistel network, called Direction B in Part II, splits the state unevenly. It needs
  more rounds, and therefore more Argon2id calls, for comparable idealized bounds.
- The Lai-Massey scheme [37] keeps the XOR of its two halves unchanged within a round, so the salt
  could be derived from that value. Without an extra mixing step, the same value would survive every
  round and pass the XOR of the source halves straight into the container; the scheme therefore
  needs an orthomorphism between rounds [38], which adds complexity and is less studied in this
  setting.
- The swap-or-not shuffle [39] has a round invariant too, but it decides one swap per round and
  needs hundreds of rounds. With one Argon2id call per round that would take hours.

A Feistel network needs few rounds, has a well-studied theory, and keeps the construction easy to
implement and check.

### Security model

The main threat is simple: someone obtains the 24-word container, for example by finding or
photographing a metal plate, and tries to recover the original mnemonic by guessing the password
offline. Everything else is secondary.

The attacker is assumed to know the suite, the MHFE format and, unless the owner keeps them secret,
the PIM and the memory level. The attacker may also be able to check a candidate mnemonic against
the blockchain, because a wallet with funds or history reveals itself. Rarer situations, such as
knowing an original mnemonic together with its container (a "known pair"), are treated separately
below; Part II lists the full set of threat models, T1 to T8.

The arguments below use the random-oracle model, the standard idealization for analysing password
hashing:

- Argon2id with fixed parameters is modelled as a random function `A(P, S)` of password and salt.
  Distinct input pairs have independent outputs; repeated pairs reuse the same output. Each query
  costs one KDF evaluation in this model, without prescribing the attacker's memory allocation.
- BLAKE2b, SHA-256 and HMAC-SHA-256 are modelled as random functions.
- The password is drawn from some distribution; `p_1 >= p_2 >= ...` are the probabilities of the
  most likely passwords.

Treating Argon2id outputs for different salts as independent is the assumption Part II calls A1. The
random-oracle model does not capture how expensive each evaluation is in memory and time; that
question belongs to the Argon2id analysis itself and is addressed under
[What a guess costs](#what-a-guess-costs).

These are arguments, not proofs. Argon2id evaluations are the main cost counted below; the other
functions are cheap, but their number still matters, as Conjecture 1 shows. The claimed absence of
cheaper attacks is conjectural; the known-pair filter below is an explicit construction, not a proof
of optimality.

The model also omits side channels. Argon2id uses data-independent memory addresses only during the
first half of its first pass; the rest are data-dependent [13]. This hybrid design does not prove
that an MHFE implementation resists timing or cache observation. Platform-specific analysis and
careful handling of intermediate states remain necessary even on an offline computer.

### Ciphertext-only guessing

What counts as a password test depends on the source. Ordinary recovery performs twelve Argon2id
evaluations. For a short source, the recovered candidate can be screened by its verifier. For a
24-word source, recovery alone cannot confirm a password; confirmation requires external
information, such as a known address, and needs the full recovered mnemonic.

**Conjecture 1.** Let the source entropy be uniformly random and independent of the password. For a
short source, no practical way is known to screen a password guess against one container alone with
fewer Argon2id evaluations than the twelve of a recovery; for a 24-word source, the same holds for
checks with external information that need the full recovered mnemonic. This is not a lower bound on
Argon2id evaluations or total work.

A quantitative bound would have to count hash computations as well as Argon2id evaluations. In a
model that treats the other functions as free, the verifier of a short source could be inverted by
brute force, as the argument below shows, so a formula that counts only Argon2id evaluations does
not hold. An earlier draft gave such a formula; it is withdrawn until a bound with a separate budget
for ordinary computation is derived.

**Argument.** Decryption starts from the container halves `L_12` and `R_12`. The inverse of round
`i` needs the mask `M_i`, computed from the salt of `R_i = L_{i+1}`. For round 11 that half, `L_12`,
is part of the container. For every earlier round, `L_{i+1}` was produced by the inverse of round
`i + 1` and is hidden behind the mask `M_{i+1}`: as long as the attacker has not evaluated
`A(P, S_{i+1})` for the true password, it is uniformly random from the attacker's point of view, and
the next salt can be hit only by guessing 128 bits. The ordinary inverse therefore evaluates the
rounds in order, from round 11 down to round 0; this does not rule out other attack strategies.

After the eleven evaluations for rounds 11 down to 1, the right half `R_0 = L_1` of the packed state
is known; only the left half `L_0` is still masked by `M_0`. The usual verifier and blockchain
checks need all of `E`, including `L_0`. For a 12-word source `R_0` is `Trunc_128(SHA-256(E))`:
exhaustive enumeration of the `2^128` possible values of `E` could test whether that hash output has
a preimage, rejecting some wrong passwords without the twelfth Argon2id call. A model with free
hashes does not charge for this impractical search. For 15 to 21 words `R_0` holds the tail of `E`
and a verifier over all of `E`; for 24 words it is simply the second half of `E`, independent of the
first. These observations neither exclude other early filters nor prove a `2^128` work requirement.
A proof needs an explicit budget for both hash computations and Argon2id evaluations.

**Many containers.** The salt of the last round comes from the container's own left half, so
evaluations made against one container are useless against an independently created one unless their
salts coincide. Containers with the same left half, or salts that collide after truncation to 128
bits, do share evaluations; for independently created containers this has negligible probability, so
the uniqueness of salts is probabilistic, not guaranteed. There is no shared table that could be
computed once for all users. If several containers use the same password, finding it opens all of
them; that is inherent to any password scheme.

**Blockchain checks.** A 24-word source has no internal verifier, but a funded wallet does: the
attacker can derive addresses from each candidate and look them up. This check needs the full
candidate mnemonic, so in the ordinary inverse it comes after all twelve evaluations. It means that
"no verifier" does not by itself stop a guesser when the wallet has no BIP39 passphrase (see
[Composition](#composition-with-the-bip39-passphrase)).

### Known pairs

A known pair is an original mnemonic together with its container, for example after the original
leaked through another channel. With a known pair the attacker can test a password guess by
evaluating the rounds from both ends and checking that they meet.

**Observation 2.** With a known pair, a password guess can be tested with 11 of the 12 Argon2id
evaluations. No cheaper test is known; whether 11 is optimal is an open question.

**Argument.** Compute rounds `0..k-1` forward from `X` and rounds `11..k+1` backward from `Y`.

- If exactly one round `k` is skipped, the Feistel relation `L_{k+1} = R_k` compares two known
  128-bit values without that round's mask. This is a valid filter with 11 evaluations.
- If two adjacent rounds `k` and `k+1` are skipped, the known values satisfy `L_{k+2} = L_k XOR M_k`
  and `R_{k+2} = R_k XOR M_{k+1}`. Each relation contains a mask that was never computed and is
  uniformly random, so neither relation says anything about the password.
- Skipped rounds that are not adjacent split the chain so that the part between them can be computed
  from neither side.

So the best known filter saves one round, a discount of one round in `N`, the number of rounds. The
cases above do not exclude every other strategy, precomputation or combination of several known
pairs, so this describes the known attack rather than a lower bound. With four rounds, as in
SLIP-0039, the same filter would save one quarter; with twelve rounds it saves one twelfth. This is
one concrete reason for the round count (see [Parameter rationale](#parameter-rationale)).

### What a guess costs

The figures in this section come from one simple cost model. They are estimates, not measurements of
a complete wallet attack.

At the default settings (PIM 0, memory level 0) one guess performs 12 Argon2id calls with 2 GiB and
12 passes each: about 288 GiB of Argon2id memory processing. Computing each 1 KiB block logically
reads two blocks and writes one; from the second pass on, version 1.3 also reads the old content of
the block it overwrites (RFC 9106, section 3.2). That is 3 to 4 KiB of logical memory access per KiB
processed, roughly 0.9 to 1.2 TB per guess. Caches and registers can serve part of it, so the actual
traffic to main memory depends on the implementation. A graphics card limited by memory bandwidth
therefore manages on the order of one guess per second for every 1 TB/s of bandwidth; the model uses
exactly one guess per second per card as a round figure, not as a measured attack speed. For
comparison, the PBKDF2-HMAC-SHA512 step with 2,048 iterations that protects a BIP39 passphrase is
taken as 1.5 million guesses per second per card, using the extrapolation below. Times are for
finding the password after searching half of the space. The model ignores address derivation and
lookups, and RFC 9106 discusses memory-time trade-offs that let an attacker use less memory at the
price of recomputation, so real costs may be lower or higher.

The PBKDF2 rate is a rounded extrapolation from the published RTX 4090 Hashcat 6.2.6 benchmark [45]:
about 3.12 million PBKDF2-HMAC-SHA512 candidates per second at about 1,000 iterations scales to
about 1.52 million at 2,048 if time scales linearly. This is a generic primitive benchmark: its
candidate varies the PBKDF2 password, whereas a BIP39 passphrase varies the salt while the mnemonic
is fixed. Kernel optimizations, input lengths and preprocessing can therefore differ. The two rates
are model inputs, not measurements of a complete MHFE-versus-BIP39 wallet attack on one card.

Word-based passwords in the table use independent uniform choices from the EFF list of 7,776 words
[42]. Two words illustrate a weak password, not a recommendation. The 30- and 40-bit rows describe
uniform random choices from spaces of `2^30` and `2^40` possibilities. Passwords that people invent
are not uniform and cannot be assigned a row just from their length.

| Password                         |  Bits | MHFE default, one card | MHFE default, 1,000 cards | BIP39 passphrase, one card |
| -------------------------------- | ----: | ---------------------: | ------------------------: | -------------------------: |
| Two random words, a weak example | ~25.8 |              ~350 days |                  ~8 hours |                ~20 seconds |
| Uniform 30-bit random password   |    30 |              ~17 years |                   ~6 days |                 ~6 minutes |
| Three random words               | ~38.8 |           ~7,500 years |                ~7.5 years |                  ~1.8 days |
| Uniform 40-bit random password   |    40 |          ~17,000 years |                 ~17 years |                    ~4 days |
| Four random words                | ~51.7 |      ~58 million years |             ~58,000 years |                  ~39 years |
| Five random words                | ~64.6 |     ~4.5 x 10^11 years |         ~4.5 x 10^8 years |             ~300,000 years |

The ratio between the two schemes is about 1.5 million, or about 20 bits: in this model an MHFE
password is as expensive to find as a BIP39 passphrase about 20 bits stronger. The password's
entropy itself does not change. One random word from a 7,776-word list carries about 12.9 bits, so
the default settings are worth roughly one and a half extra words. An attacker limited by memory
capacity rather than bandwidth, such as a custom chip, is hit harder in this model: in the
full-memory implementation it assumes, each active guess uses about 2 GiB of Argon2 working memory.

The relative cost in bits is `log2(BIP39 rate / MHFE rate)`, so it is sensitive to both assumed
rates. Holding the BIP39 rate at 1.5 million per second, MHFE rates of 0.1, 1 and 10 guesses per
second give about 23.8, 20.5 and 17.2 bits of relative cost respectively. These are sensitivity
examples, not additional measurements or changes to password entropy.

This is a supporting argument for MHFE rather than its main one. The main arguments are that MHFE
protects the mnemonic itself, which a passphrase does not, and that it can be applied to an existing
wallet without moving funds. The gain in bits comes on top, and for a cold-storage backup it costs
the owner little. Measured as whole operations at the default settings on the author's laptop, a
recovery took about 70 seconds on the command line, about 90 seconds in a browser's fast mode and
about four minutes in a browser's standard mode; an encryption with its check took roughly twice as
long
([measurement record](https://github.com/hobby-eng/mhfe/blob/883373c5833ca6aefc88345caa3a18cbbfcf0f5c/measurements/README.md)).

**Farms and botnets.** Two larger attackers, in the same model:

- a hypothetical farm of about 25 data-centre graphics cards with 80 GB each, 2 TB of memory in
  total, an assumed aggregate bandwidth of 90 TB/s and ideal scaling: at the model's rounded 1 TB
  per guess, roughly 90 guesses per second together. Total memory alone does not determine this
  throughput;
- a botnet of one million ordinary computers, each able to spare 2 GiB and each finishing one guess
  in about two minutes, roughly 8,000 guesses per second together. Devices unable to provide that
  memory are excluded from this particular estimate, which leaves out many older phones and small
  devices but not current phones with 8 GB or more; implementations using time-memory trade-offs are
  outside the model.

| Password                       | Farm, 2 TB of card memory | Botnet, one million computers |
| ------------------------------ | ------------------------: | ----------------------------: |
| Uniform 30-bit random password |                 ~2 months |                     ~18 hours |
| Four random words, ~51.7 bits  |            ~640,000 years |                  ~7,000 years |
| Five random words, ~64.6 bits  |          ~5 billion years |             ~54 million years |

**Password length versus work factor.** At a fixed memory level, this model treats cost as
approximately proportional to the number of passes, so PIM `k` multiplies the per-guess cost by
`k + 1`. Increasing memory has a different, model-dependent effect: doubling it roughly doubles cost
for a bandwidth-limited attacker or quadruples area-time cost under the capacity-limited assumptions
in [Parameter rationale](#parameter-rationale). Memory-time trade-offs can change these estimates.

Under the pass-scaling assumption, PIM 1023 multiplies the cost by 1,024 (about 10 bits of cost) and
makes a recovery take roughly 17 to 34 hours. Each additional independent random word multiplies the
search space by 7,776 (about 12.9 bits), without increasing the Argon2id work factor. The work
factor is therefore a margin on top of a good password, not a substitute for one.

The practical advice follows directly: a password that a person invents without a method can fall to
a well-funded attacker within days, while four or five words chosen with dice, for example from the
EFF large wordlist of 7,776 words, put the container out of reach in this model.

### Composition with the BIP39 passphrase

MHFE protects the mnemonic; the BIP39 passphrase protects the wallet derived from it. They are
applied one after the other: recovery restores the original mnemonic, and the passphrase is then
used as before. The estimates below assume a known source length, independent uniformly chosen
secrets (`N1` MHFE passwords costing `C1` each; `N2` passphrases costing `C2` each), and no separate
check that identifies the original mnemonic. They describe sequential searches, not lower bounds.

**12 to 21 words: the costs add up when false matches are rare.** The recovery verifier tests the
MHFE password on its own, so an attacker first searches the MHFE passwords and then attacks the
passphrase through the blockchain. A wrong MHFE password passes an `r`-bit verifier with probability
about `2^-r`, and each such false match needs its own full passphrase search. The expected cost is
about

```text
N1 * C1 / 2  +  N1 * N2 * C2 / 2^(r+1)  +  N2 * C2 / 2
```

Relative to the MHFE work, the middle term's ratio is `N2 * C2 / (2^r * C1)`; relative to the final
passphrase search, it is `N1 / 2^r`. Thus `N1` much smaller than `2^r` is sufficient for that term
to be negligible overall, but no source length guarantees this for arbitrary secrets. With 21 words
(`r = 32`), searching half of a four-word dice-password space yields about 426,000 false matches;
with a five-word dice passphrase, their searches cost about 4,400 times the MHFE work in the model
above. Even then, this pair-search term is `2^32` smaller than for a 24-word source with the same
secrets, not comparable to it.

**24 words: the search runs over pairs.** With no separate mnemonic check, the attacker runs one
MHFE recovery per MHFE password and then tries passphrases on the resulting phrase, for an expected
cost of about

```text
N1 * C1 / 2  +  N1 * N2 * C2 / 2
```

This is not the product of two complete searches, but its second term grows with the product of the
two spaces. Related or reused secrets lose most of this gain.

Example with independent 30-bit secrets, in the model above:

| Source   | Search                                                           | Expected time on one card |
| -------- | ---------------------------------------------------------------- | ------------------------: |
| 12 words | MHFE password, then passphrase                                   | ~17 years plus ~6 minutes |
| 24 words | about `2^30` MHFE passwords, each with a search over passphrases |             ~12,000 years |

Without a passphrase, a 24-word source offers no such gain: wallet history provides an external
check of a candidate recovered with an MHFE password. A short source instead supplies an internal
verifier, with the false-match probability described above.

This is a choice for the user rather than a weakness of either option. A short source gives a
recovery that reports whether a candidate passes its verifier, automatic length detection and simple
password rehearsal. A 24-word source with an independent passphrase gives the strongest combination
of the two secrets. The specification's Rationale section presents this choice.

### Deniability

A person who is forced to disclose a password can disclose a different one, prepared in advance.
This section states precisely what such a decoy disclosure achieves and proves it. The notion
follows receiver-deniable encryption in the sense of Canetti, Dwork, Naor and Ostrovsky [46]: an
honest disclosure and a prepared one are compared in two experiments, and the adversary must tell
them apart from the information it has. The proofs hold for one container and one disclosure in the
model below. Unlike the arguments above, they are proofs within that model, but they have not been
reviewed by an independent cryptographer.

**The idea in words.** For every password, encryption is a permutation: it shuffles all `2^256`
states. A shuffle of a uniformly random state gives a uniformly random state, so a container made
from a 24-word phrase is a uniformly random state whatever password made it. Reading such a
container with any other password again gives a uniformly random state, which is exactly what an
honest owner's phrase is. A prepared disclosure and an honest one therefore look the same. What
differs is that behind a prepared disclosure a second wallet exists, the real one, and the adversary
finds it only with about the probability of guessing the real password.

**Notation.** The suite and the settings are fixed. `E_P` is the permutation `Perm(P, .)` of the
256-bit states and `D_P` its inverse. A password is identified with its normalized encoding `P_enc`,
so spellings that normalize to the same bytes are one password. Passwords are drawn from a
distribution over normalized encodings with probabilities `p_1 >= p_2 >= ...`. A wallet is
identified by its phrase, including its length: a packed 12-word state read as 24 words is a
different phrase with a different wallet. A usage scenario `U` is a randomized procedure that, given
a phrase, produces the public record of its wallet's use, such as its transactions; distinct wallets
get independent records, and a wallet that is never used has an empty record. Independent records
are an abstraction: a transfer between two wallets links their records.

**Lemma 1 (consistency).** For every password `Q` and container `Y`, the state `X' = D_Q(Y)` read as
24 words is a valid BIP39 phrase, and `E_Q(X') = Y`.

**Proof.** Every 256-bit state is valid 24-word entropy, and `E_Q` and `D_Q` are inverse
permutations.

A prepared disclosure is therefore a genuine opening of the container: recovering `Y` with `Q` gives
`X'`, and applying the permutation `E_Q` to `X'` gives `Y`. The full creation procedure with `Q`
gives the same container unless `Y = X'`, a fixed point that it refuses.

**Lemma 2 (uniformity).** If a state `Z` is uniformly random and a permutation `F` is chosen
independently of it, then `F(Z)` is uniformly random and independent of `F`.

**Proof.** For every fixed `F` and state `y`, `Pr[F(Z) = y] = Pr[Z = F^-1(y)] = 2^-256`.

**Lemma 3 (one input, two rounds).** Let a Feistel network have at least two rounds with independent
random round functions, and let its input `(L_0, R_0)` be fixed. Then its output is uniformly
random.

**Proof.** The first mask is uniform, so `R_1 = L_0 xor M_0` is uniform. The second mask is uniform
and independent of `R_1`, so after round 1 the state `(L_2, R_2) = (R_1, R_0 xor M_1)` is uniform.
The later rounds form a permutation independent of the first two masks, so the output is uniform by
Lemma 2.

The lemma concerns a single input. For two inputs with the same right half, two rounds keep the
relation `L_2 xor L'_2 = L_0 xor L'_0`, so a uniform output for each input alone does not make a
Feistel network indistinguishable from a random permutation. One input suffices below because an
adversary who does not know the real password never sees the real permutation applied to a second
input: it is applied once, to the real source.

**Experiments.** Both experiments give the adversary a container `Y`, a disclosed password and the
public record of the disclosed phrase's wallet, and let it look up the record of any phrase. A
lookup of the disclosed phrase returns that record; in the prepared experiment, a lookup of the real
phrase, when it differs from the disclosed one, returns the real wallet's record; every other lookup
returns an empty record. In both, creation refuses a container equal to its source, as the
specification requires, and the owner then draws another password.

- **Honest disclosure.** A 24-word phrase with uniformly random entropy `X` is created and a
  password `P` is drawn. The container is `Y = E_P(X)`. The wallet of `X` is used according to `U`.
  The adversary receives `Y`, `P` and the record `U(X)`.
- **Prepared disclosure.** The owner's real source, with packed state `X`, and a password `P` give
  `Y = E_P(X)`. A decoy password `Q` is drawn from the same distribution and drawn again while it
  equals `P`, and `X' = D_Q(Y)`. The disclosed phrase is `X'` read as 24 words, and its wallet is
  used according to the same `U`; the real wallet, that of the owner's source phrase, is used in any
  way. The adversary receives `Y`, `Q` and the record `U(X')`.

The adversary knows the construction and how decoys are prepared, may query the random oracles of
the [Security model](#security-model) adaptively, and may look up the record of any state. Let `k`
be the number of distinct passwords with which it queries Argon2id, `h` the number of its
HMAC-SHA-256 queries and `l` the number of its lookups. Every computation of the experiment itself,
including the decoy recovery `D_Q(Y)`, uses the same oracles. It outputs a guess of the experiment;
its advantage is the difference between the probabilities that it answers "prepared" in the two
experiments. The condition that both disclosed wallets follow the same scenario `U` is essential: a
decoy created a minute ago cannot pass for a wallet with years of history.

**Theorem 1 (24-word source, exact).** Let the real source have 24 words and uniformly random
entropy, independent of the passwords, and ignore the refusal of fixed points and the redrawing of
`Q`. Then the random oracles, the container, the disclosed password, the disclosed phrase and its
wallet's record have exactly the same joint distribution in both experiments.

**Proof.** In the prepared experiment `X` is uniform and independent of `P`, of `Q` and of the
oracles, so by Lemma 2 `Y = E_P(X)` is uniform and independent of all of them. For each value of `Q`
and of the oracles, Lemma 2 applied to `D_Q` shows that `X' = D_Q(Y)` is uniform, and `Y = E_Q(X')`
by Lemma 1. So the oracles together with `(Y, Q, X')` have the distribution of the oracles together
with `(E_P(X), P, X)` in the honest experiment, and the records `U(X')` and `U(X)` follow, since the
scenario is the same. The argument holds for any fixed functions in place of the oracles.

What Theorem 1 leaves open is the real wallet: a lookup of `X` shows its record in the prepared
experiment only. Theorem 2 bounds the effect of that and of everything else.

**Theorem 2 (bound, every source length).** Let the real source have 12 to 24 words and uniformly
random entropy `E` of `ENT` bits, independent of the passwords. For a source shorter than 24 words,
let the adversary have no information about the source length beyond what the experiment gives it.
In the random-oracle model the advantage is at most

`(k + 2) * p_1 + l * 2^-ENT + (12 * h + 146) * 2^-256`.

**Proof.** The proof moves from the prepared experiment to the honest one through a sequence of
games in the sense of Shoup [47]: each step either changes nothing in distribution, or leaves two
games identical until a stated event occurs, and then changes the result by at most that event's
probability. The oracles are sampled lazily.

- **Game 0** is the prepared experiment.
- **Game 1** draws `Q` once, independently of `P`, and keeps it even if it equals `P`; the owner
  also keeps the first password even if it gives a fixed point. Games 0 and 1 use the same random
  choices and differ only if the first `Q` equals `P`, which has probability at most `p_1`, or if
  the first password gives a fixed point, which by Lemma 3 has probability `2^-256` in the
  random-oracle model.
- **Game 2** encrypts the real source with private copies of the random functions: Argon2id with the
  password `P`, and HMAC-SHA-256 with the twelve resulting keys `K_i`, are answered by random
  functions independent of the shared oracles. A lookup of the real phrase returns an empty record
  unless the real phrase is the disclosed one. Games 1 and 2 proceed identically until a bad event:
  the adversary queries Argon2id with `P`; the decoy recovery uses `P`, that is `Q = P`; the
  adversary or the decoy recovery calls HMAC-SHA-256 with one of the keys `K_i`; or the adversary
  looks up the real phrase while it differs from the disclosed one. BLAKE2b and SHA-256 remain
  shared in both games and answer every query alike. An adversary may compute salts, but without `P`
  they give only independent Argon2id outputs, and a query with `P` is already a bad event.
- **Game 3** is the honest experiment without the refusal of fixed points, which differs from the
  honest experiment by at most `2^-256`, again by Lemma 3.

Games 2 and 3 have the same distribution. In Game 2 the twelve round functions that produced `Y` are
independent random functions, independent of the shared oracles: they come from the private copies,
and their mask input messages contain the round index and the half, so no two rounds share an input
even where two salts coincide. By Lemma 3, `Y` is uniform and independent of the source, of `Q` and
of the shared oracles. As in Theorem 1, the adversary then faces the same random oracles, a
container that is uniform and independent of them, the disclosed password, the phrase that it
recovers, that phrase's record and empty records for every other phrase, exactly as in Game 3,
including every answer to its adaptive queries.

In Game 2 everything the adversary sees is independent of `P`, of the keys `K_i` and of the real
source, so the bad events have these probabilities. Each password has probability at most `p_1`, so
the adversary's `k` passwords include `P` with probability at most `k * p_1`, and `Q = P` has
probability at most `p_1`. The keys `K_i` are uniform 256-bit values, independent of the keys of the
decoy recovery, so the `h` HMAC queries of the adversary and the twelve of the decoy recovery hit
one of them with probability at most `12 * (h + 12) * 2^-256`. The real phrase is determined by `E`,
so each lookup hits it with probability at most `2^-ENT`. Adding the steps gives the bound: `p_1`
and `2^-256` for Game 1, `(k + 1) * p_1 + 12 * (h + 12) * 2^-256 + l * 2^-ENT` for Game 2 and
`2^-256` for Game 3.

**Remark on cost.** An ordinary search computes `D_p(Y)` for candidate passwords `p`, twelve
Argon2id evaluations each, and looks up the results. Theorem 2 bounds the probability of success by
the number of passwords tried and lookups made; it does not show that this search is the cheapest
way to try a password (see Conjecture 1).

**Corollary (a prepared disclosure adds no information).** A prepared disclosure can be simulated
from the container alone: draw a password from the distribution, recover the container with it,
which costs twelve Argon2id evaluations, and sample a record from the usage scenario, which is
public behaviour. The simulated disclosure differs from a real one only in that its password is
drawn independently instead of different from `P`, a difference of at most `p_1`. Whatever an
adversary can do with a container and a prepared disclosure, it can therefore do with the container
alone at the cost of one recovery, with a success probability at most `p_1` lower. This holds for
every source length and needs no idealized function. It does not make the real wallet safe by
itself: that still rests on the password and on MHFE, as without any disclosure.

The owner must not select the decoy password by the phrase it produces. For example, a decoy phrase
that also passes a 21-word verifier, which happens with probability about `2^-32`, must be kept,
because an honest 24-word phrase can do the same.

**Honey encryption.** For a 24-word source the construction has the structure of honey encryption in
the sense of Juels and Ristenpart [16], with a uniform message model and the identity as its
encoder: every password recovers an equally likely phrase, so only external information, above all
the use of the real wallet, identifies the right one. Whether MHFE meets the formal security
definition of honey encryption is not claimed; that also depends on what external information is
available. Part II's remark that MHFE has no such model refers to wallet entropy in general. A short
source is different: its verifier deliberately rejects wrong passwords, which is why Theorem 2 needs
an adversary who does not know the source length.

**Limits of the guarantee.**

- Both theorems compare a prepared disclosure with an honest owner of a 24-word source. An adversary
  who knows that the original has fewer than 24 words, for example from the device or software that
  created it, sees that a not-verified 24-word result cannot be the original.
- The decoy password must be drawn like a real one. A noticeably weaker or differently formed
  password is evidence outside the experiments.
- The decoy wallet must follow the same usage scenario as an honest wallet. Its phrase cannot be
  chosen, so it is a new wallet, and its use has to begin as early and look as ordinary as an honest
  owner's would. A transfer between the real and the decoy wallet links their records.
- The bounds include the probability of guessing the real password, but not of learning it in
  another way. If it leaks, the decoy does not help.
- Several containers with related passwords, repeated disclosures, a BIP39 passphrase and side
  channels are not covered.
- Cryptography cannot promise that a particular person will believe a disclosure; the theorems only
  bound what the adversary can learn from the information in the experiments.

### Parameter rationale

**Cold storage.** MHFE is meant for long-term offline backups that are created once and recovered
rarely. Waiting a couple of minutes for such an operation is acceptable, while the attacker repeats
the work for each password guess, at a speed that depends on the hardware. The parameters are chosen
for that use and not for everyday unlocking.

**Memory and passes follow RFC 9106.** The first option that RFC 9106 recommends is Argon2id with 2
GiB of memory, four lanes and one pass [13]. Its general procedure is to choose the largest amount
of memory the application can afford and then to increase the number of passes until the available
time is used. MHFE applies that procedure: 2 GiB and four lanes as recommended, and twelve passes
because a cold-storage operation can afford several seconds per round. The twelve passes are this
project's choice under that procedure, not a value the RFC prescribes. On the author's mid-range
laptop from 2022 (Intel Core i7-1260P, 16 GB) one such call took about 4.4 to 7 seconds with the
reference C code and about 10 seconds with OpenSSL, using four threads, so a recovery takes about
one to two minutes and a creation, which ends with a full recovery as its check, about twice as
long. Newer computers are faster and commonly have far more memory.

More memory is worth more than more passes. For the owner, doubling either doubles the waiting time.
In an area-time cost model the attacker's cost grows roughly with memory multiplied by time, so
doubling the memory quadruples it while doubling the passes only doubles it. That holds only under
assumptions: the attacker is limited by memory capacity, such as a custom chip or a graphics card
running many guesses side by side; the time of one guess grows in proportion to its memory; the
hardware is fixed; and no favourable memory-time trade-off is used. Under them, compared with suite
2's 512 MiB, one suite 3 guess costs about four times as much for a card limited by memory bandwidth
and roughly sixteen times as much for an attacker limited by memory capacity. It is a model, not a
guarantee against every attacker.

2 GiB is the right default: most current laptops and desktops can spare it, although a machine with
only 4 GB may not once the system and other programs are counted. It is also the most that the
reference C implementation of Argon2 accepts when pointers are 32 bits wide, so 32-bit WebAssembly
builds support exactly this default and no higher memory level. Users with larger computers can
choose more through the memory level in the native program.

**Two work-factor settings.** The PIM multiplies the pass count; the memory level raises the memory
in steps of 1.5 and 4/3, doubling it every two levels. They are separate because memory must fit the
computer that will be used for recovery, possibly years later, while waiting time is a matter of
patience. A single number that raised memory first would stop a user with a 16 GB laptop at the
point where memory runs out, even if that user were willing to wait longer. Argon2id itself, and
tools such as KeePass, also expose memory and passes separately.

Both settings serve as headroom. As hardware becomes cheaper, new containers can keep or raise their
cost per guess without a new suite.

**Why PIM stops at 1023.** PIM `k` multiplies the owner's time roughly by `k + 1`, so 1023 gives a
factor of 1,024: ten bits, and roughly 17 to 34 hours per recovery at 2 GiB on the reference laptop.
Beyond that, every further doubling adds one bit while doubling a wait that is already measured in
days, and a single extra dice word adds almost thirteen bits for free. The limit is a judgement of
what is still sensible, not a technical boundary; Argon2id itself would allow far more passes.

**Why the memory level uses half steps.** Doubling at every level would leave large gaps: a laptop
with 16 GB could safely use 8 GiB but nothing between 8 and 16. Alternating factors of 1.5 and 4/3
give the series 2, 3, 4, 6, 8, 12, 16, 24 GiB and so on, which fits real machines more closely,
keeps every value a whole number of GiB and can be computed exactly with integers:
`m(MEM) = (2 + MEM mod 2) * 2^(20 + floor(MEM / 2))` KiB.

**Why the memory level stops at 21.** Level 21 means `3 * 2^30` KiB, 3 TiB. Level 22 would need
`2^32` KiB, one more than the largest memory Argon2id accepts, so level 21 is a real technical
limit. Such amounts are far beyond ordinary personal recovery computers; the upper levels provide
headroom for unusually large systems rather than a practical default.

**Keeping the settings secret.** Recovery needs a non-default setting exactly, so its owner must
remember it; nothing requires writing it next to the container. An owner may also keep it secret, as
VeraCrypt allows for its PIM. That helps only to the extent that the value is unpredictable to the
attacker, and it gives no fixed additional margin. An example makes the effect concrete under
explicit assumptions: `N` equally likely passwords, a PIM drawn independently and uniformly from
`0..Q-1`, a fixed memory level, a test of one password at PIM `j` costing `(j + 1) * C0`, a reliable
way to recognise the right pair, and no work shared between tests. An attacker who tries all
passwords at PIM 0, then all at PIM 1 and so on, which is the best order under these assumptions,
pays for a true PIM `k`

```text
known PIM:   C_known(k)  = C0 * (N + 1)(k + 1) / 2
hidden PIM:  C_hidden(k) = C0 * (N(k + 1)^2 + (k + 1)) / 2
```

For large `N` the ratio approaches `k + 1`: about 1,024 for a true PIM of 1023 in this model, which
is a conditional result for that value, not a general gain from the range. Averaged over the uniform
PIM the ratio of the mean costs is `(N(2Q + 1) + 3) / (3(N + 1))`, approximately 683 for `Q = 1024`
and large `N`. Popular values, the owner's habits or any other guidance reduce the effect, and a
guessable choice gains much less.

A forgotten secret setting has to be searched by the owner as well. An owner who knows the password
and the memory level, tries PIM 0, 1 and so on, and can recognise a successful recovery pays for a
true PIM `k` about `(k + 1)(k + 2) / 2` times the cost of a default recovery, or `(k + 2) / 2` times
the cost with the PIM known. Recognising success needs the verifier of a short source, which can
also give a false match with small probability, or, for a 24-word source, external information such
as a known address. A strong password remains the better investment; a secret setting is an optional
extra with its own risk of being forgotten.

**Twelve rounds.** Total cost could in principle be reached with any round count by adjusting
Argon2id, so the round count is chosen for structural reasons:

- The best known known-pair filter saves one round ([Known pairs](#known-pairs)). With twelve rounds
  that is one twelfth.
- Twelve sequential steps give natural progress reporting and cancellation points.
- Twelve is above the round counts for which Patarin proves strong bounds for ideal random round
  functions (seven against chosen plaintexts, ten against chosen plaintexts and ciphertexts) and
  well above SLIP-0039's four rounds. This is a margin, not a proof for MHFE, because the proofs
  assume independent random round functions.

**Parallel lanes.** In the author's measurements the same browser recovered a container in 90 to 95
seconds with the threaded build and in 234 to 239 seconds with the single-threaded one, and one
Argon2id call took 4.6 to 5.0 seconds natively with four threads; the
[measurements](#performance-measurements) give the details. These figures illustrate the effect of
threading on one computer rather than establish a general speed ratio. The specification requires
implementations to compute the four lanes in parallel wherever threads are available, so the owner
can use that parallelism too. The actual benefit depends on the implementation and hardware.

**Unicode 17.0.0.** Suite 2 pinned Unicode 18.0.0, for which no normalization tables were available
in Rust when it was written, so the reference implementation could only accept ASCII passwords.
Normalization of assigned characters never changes between Unicode versions, so pinning the version
only matters for rejecting code points that were unassigned at that time. Suite 3 pins Unicode
17.0.0, which current libraries implement.

### Final-word-preserving cycle walking (research idea)

This idea is not part of suite 3. It is recorded here because it answers a real wish, and because
the reasons for not using it are worth keeping.

**What it is for.** The container would end with the same word as the original 24-word mnemonic. An
owner who remembers the last word of each wallet could then tell which plate belongs to which wallet
without decrypting anything. This would also be a quick check of a plate before any computation: a
plate whose last word differs from the remembered one is not this wallet's container or was copied
wrongly. It is an 11-bit check of the plate, not of the password or of the other 23 words, and it
does not show that a recovery used the right password.

**How it would work.** The permutation is applied again and again until the last word of the result
matches the last word of the start, first during creation and then in the inverse direction during
recovery:

```text
creation:                         recovery:
  target = FW(X)                    target = FW(Y)
  Y = Perm(X)                       X' = Perm^-1(Y)
  while FW(Y) != target:            while FW(X') != target:
      Y = Perm(Y)                       X' = Perm^-1(X')
```

`FW` is the 11-bit index of the last word: the last three entropy bits followed by the 8-bit BIP39
checksum. The first application is mandatory, no counter is stored, and the walk fails if it returns
to its start before finding another match. An unreleased suite 2 draft specified exactly this as the
optional profile `MHFE-BIP39-256-EXPERIMENTAL-2-CYCLE-WALK-FINAL-WORD`; Part II keeps its full rules
and analysis.

**What it risks.**

- The last word reveals three bits of the source entropy directly and, through its 8-bit checksum,
  about 11 bits of information about the source in total: the source is confined to a class of about
  `2^245` values.
- It does not confirm the password. A successful walk under a wrong password also returns a mnemonic
  with the same last word.
- The owner must remember that it was used. Standard recovery would silently produce a different
  24-word wallet.
- The number of steps depends on the password and the source, which creates a timing signal; Part II
  quantifies it.

**What it costs.** A match is expected after about 2,048 complete permutations, with a long tail and
no practical upper bound. With the suite 3 parameters, at one to two minutes per permutation on the
reference laptop, that is roughly one to two days at the median, one and a half to three days on
average and up to about 13 days at the 99th percentile, for every recovery; a creation with its
check walks the same way forward and back and takes about twice as long. Each password guess has a
similarly large expected cost under this model, although individual walk lengths vary, so trying
many variants of a half-remembered password is generally impractical.

**Why the proposed cheaper variants do not solve the problem.** Three cheaper variants come up
naturally. The first is a walk with a fast permutation and only one expensive Argon2id call to
derive its key. The difficulty is the salt of that call. It must be computable from the original
during creation and from the container during recovery, and the only thing the two share is the last
word itself: 11 bits. There would therefore be only 2,048 possible salts in the world. An attacker
could compute Argon2id for a password dictionary once per salt and then test every such container
almost for free, which is exactly the shared dictionary that state-derived salts exist to prevent.
The second, doing the expensive part first and a cheap walk afterwards, fails differently: during
recovery the backward walk has no way to recognise where the expensive part ended. The third is to
find a matching container cheaply with light parameters and then look for a way to reach it with the
real ones, which does not help either: for a given password and settings, the expensive permutation
sends the source to exactly one container, fixed but unpredictable until it is computed. Any search
for a password, setting or tweak that makes that container land on the right last word succeeds with
probability about 1 in 2,048 per attempt, so it costs as many expensive evaluations as cycle walking
itself. Part II also records a variant on 253 bits, which would need about 256 expensive
permutations instead of 2,048 but requires a new permutation and its own analysis.

**Conclusion.** With the suite 3 derivation parameters, we see no reason to use this idea.
Recognising a plate by its last word does not justify days of computation for every recovery, the
loss of practical password-variant search and about 11 bits of information revealed about the
source, three of them directly. It stays a documented research idea.

### Open questions for review

1. Prove or refute Conjecture 1 with a quantitative bound that counts both Argon2id evaluations and
   hash computations, stating the A1 assumption precisely, and show whether the right half `R_0`,
   known after eleven evaluations, or the structure of short sources allows any practical test with
   fewer than twelve Argon2id evaluations. Define separate budgets for KDF evaluations, fast
   hash/MAC queries, preprocessing and memory. State the source and password distributions,
   available known pairs or oracle queries, and whether success means filtering a guess, recovering
   the source or identifying its wallet; these are different games. The independence assumed for
   distinct Argon2 inputs in A1 is not an established property of the concrete construction.
2. Determine whether the known-pair filter of Observation 2 is optimal, including strategies with
   several known pairs and precomputation.
3. Check the cost estimates against real graphics cards, published Argon2id cracking figures and the
   memory-time trade-offs discussed in RFC 9106.
4. If the final-word idea is ever revived, analyse it for shortcuts across repeated applications and
   for its timing signal.
5. Maintain the conformance coverage and reproducible generator/verifier provenance of the
   [suite 3 corpus](../vectors/suite3/) as the specification evolves, retain independent full-cost
   replay evidence, and obtain an implementation by another author. The current corpus records
   OpenSSL 3.5.5 replay of all 17 positive transcripts and six negative recovery cases; this is
   independent primitive-level reproduction, not an independently authored MHFE implementation.
6. Review the Unicode 17.0.0 assignment check in a real implementation.
7. Review the deniability proofs, and extend the game to several containers, repeated disclosures
   and a BIP39 passphrase.

## Part II. Detailed design discussion

The sections below develop the design in more detail. They were first written for suite 2 and have
been brought up to date for suite 3; the released suite 2 text is kept in the
[archive](archive/README.md). Cross-references such as "**Reference Implementation**" refer to
sections of this Part. Citation numbers refer to the single reference list in
[`README.md`](../README.md#references).

For the requirements, use the [specification](../README.md#specification); Part I gives the main
analysis.

One statement applies to the whole of Part II, so the sections below do not repeat it: the cited
Feistel results assume independent random round functions and do not transfer to MHFE automatically,
the heuristics used are modelling assumptions rather than proofs, and nothing here has been reviewed
by an independent cryptographer. The consolidated list is under **Status and security claim**.

### Motivation

#### Practical purpose: protecting a physical backup without expanding it

**The practical goal is to keep a recovery phrase on a familiar, capacity-limited physical backup
while making possession or a photograph of that backup insufficient, by itself, to recover the
original phrase.**

Physical seed-backup products such as Cryptosteel, and comparable metal plates or capsules, provide
a finite number of character or word positions. Cryptosteel's own instructions describe storing
longer BIP39 phrases using abbreviated words [1]. Such media cannot accommodate arbitrary expansion
without changing the storage arrangement. A password-encrypted container that remains a valid
24-word BIP39 phrase could use the same word-oriented recording method, subject to the medium's
capacity and supported wordlist. This is the practical reason for investigating a fixed-size format
rather than simply adding more fields to a backup.

Physical durability, confidentiality, and concealment address different problems. An unencrypted
phrase on paper or metal can be read, copied, or photographed by anyone who encounters it, even
without removing the original. MHFE is intended to make recovery from that record require a password
rather than expose the original phrase immediately.

The 24-word container also has the ordinary syntax of a valid BIP39 mnemonic and carries no in-band
marker identifying it as encrypted. A casual observer may therefore interpret it as an ordinary
recovery phrase and may not realize that another mnemonic is concealed behind it. This format
ambiguity can reduce opportunistic attention and avoid revealing the encryption workflow itself.
This is practical concealment, not formal plausible deniability. Storage context, accompanying
instructions, known wallet addresses, repeated containers, or prior knowledge of MHFE may reveal the
record's purpose and permit password candidates to be tested at the construction's KDF cost. Part I
analyses [decoy disclosures](#deniability), which remain possible when the use of MHFE is known.

The MHFE password must therefore be retained independently: memorized or recorded in a separate
location, possibly in a discreet form meaningful to its owner. If the original wallet also uses a
BIP39 passphrase, it must likewise be preserved and should not be stored beside the container as
part of the same exposed backup. A deliberately selected non-default PIM or memory level must be
remembered as well, since recovery needs exactly the same value. Keeping secrets apart from the
container helps preserve both confidentiality and the container's ambiguous appearance, but a
disguised written password is not a substitute for resistance to guessing. Losing any secret or
non-default recovery input can prevent recovery.

**Author's motivation and hypothesis:** the author considers managing one sufficiently strong,
memorable password potentially easier than memorizing 12 or 24 mnemonic words in their exact order.
A separate, discreet password record may also be easier to manage than another full mnemonic record.
On that basis, the author considers an encrypted physical backup with a separately managed password
potentially safer against accidental viewing or photography than keeping the complete recovery
phrase openly readable. This is an authorial usability and security hypothesis motivating the
research, not a measured user-study result or a claim that the current MHFE construction has proven
security.

#### Prior problem statement and community context

BIP39 provides a compact human-readable representation of wallet entropy [2], but it does not define
an in-place encryption format for an existing mnemonic. The optional BIP39 passphrase affects the
512-bit seed derived from the mnemonic; it does not encrypt or alter the mnemonic backup itself.

The problem has a concrete public history. In May 2021, approximately five years before this draft,
a Bitcoin Stack Exchange discussion posed almost the same goal: encrypt an existing BIP39 mnemonic
into another mnemonic while preserving recovery of the original wallet seed, and it linked an
experimental AES-CTR prototype [3], [4]. The available public record stops short of a complete,
reviewed, interoperable proposal: it does not provide a stable format, a memory-hard KDF profile,
comprehensive test vectors, or a construction-specific security analysis. This unresolved discussion
is the closest historical anchor for presenting MHFE to technical forums such as Delving Bitcoin.
MHFE treats it as evidence that the use case predates this draft, not as validation of the present
construction.

#### Baseline design goals

Conventional password-encryption formats normally store additional information such as a random
salt, nonce, version, and authentication tag. The baseline goal here is narrower: emit one exact
24-word BIP39 container while making recovery depend on a separate password.

The baseline construction targets the following constraints; research alternatives explicitly
identify which constraints they retain or relax:

- the plaintext is a valid 12-, 15-, 18-, 21-, or 24-word BIP39 mnemonic and the encrypted container
  is a valid 24-word BIP39 mnemonic;
- the underlying transform is a permutation over all 256-bit BIP39 entropy values;
- no per-container bits are available outside that 256-bit space;
- the password is the only user-held secret required by the transform itself;
- password guessing should require memory-hard work;
- short-source recovery verification must be clearly distinguished from AEAD authentication.

#### Practical recovery requirements

In the standard suite 3 workflow, the user is not expected to memorize or separately record the
literal `SUITE_{ID}`, the BIP39 wordlist, the original short-mnemonic length, or default settings.
They are supplied or inferred as follows:

- The compatible MHFE implementation fixes the exact suite identifier internally.
- Suite 3 uses the English BIP39 wordlist.
- Omitted settings mean the defaults: PIM `0` and memory level `0`.
- For a 12-, 15-, 18-, or 21-word source, the encrypted recovery verifier permits automatic
  source-length detection after one inverse permutation.

In that standard workflow, the separately retained user secrets are the **MHFE password** and, only
if the original wallet used one, its distinct optional **BIP39 passphrase**. The BIP39 passphrase is
not part of MHFE and cannot be reconstructed from the container. These two secrets should not be
recorded next to the encrypted container.

A deliberately selected non-default PIM or memory level is the only additional parameter the user
must retain; recovery needs exactly the same value. Users who keep the defaults need nothing else,
except in the rare case in which creation finds that the packed state also passes the verifier of
another short length; the original word count should then be kept for manual selection during
recovery.

The container does not identify itself as MHFE: its intended outward form is an ordinary valid
24-word English BIP39 mnemonic. Recovery therefore still requires compatible MHFE software or
knowledge that the record is an MHFE container, just as any encrypted data requires knowledge of its
format. This does not require the user to memorize the literal suite-identifier string.

Automatic length detection is extremely reliable for short sources but is probabilistic rather than
authenticated. If no short-source verifier matches, the candidate is treated as a 24-word source. A
genuine 24-word source can accidentally satisfy a short-source verifier, dominated by the 21-word
probability near $`2^{-32}`$. Recovery software should therefore expose the detected length, must
permit an explicit 24-word override, and should allow final comparison with a known public address
or other wallet identity data. Remembering the original length is useful corroborating information,
not a required separately stored field in the standard workflow.

No original backup should be destroyed solely because one MHFE container was created. Before an
implementation presents a container as a replacement backup, the user should complete a recovery
rehearsal and compare known public addresses or other wallet identity data using maintained wallet
software.

### Notes on the construction

These explanatory paragraphs accompany the normative text of the specification.

#### Salt and mask lengths

The 128-bit lengths of `S_i` and `M_i` do not select 128-bit variants of the underlying
cryptographic primitives. `S_i` is truncated from a 256-bit BLAKE2b digest, `K_i` is the full
256-bit Argon2id output, and `M_i` is truncated from a 256-bit HMAC-SHA-256 output. The mask must be
128 bits because it is XORed with one 128-bit half of the fixed 256-bit Feistel state. Expanding
that mask to 256 bits would require a 512-bit state and would no longer fit a 24-word BIP39
container. Expanding the salt to 256 bits would not add independent entropy because its variable
Feistel-branch input is only 128 bits.

#### Argon2id lanes and default cost

RFC 9106's first and second recommended Argon2id options both use $`p = 4`$, and its general
parameter-selection procedure likewise begins with four lanes [13]. Suite 3 therefore selects
$`p = 4`$. Reducing `p` merely to lengthen wall-clock time is not presumed to improve
password-guessing resistance: an attacker can parallelize independent password candidates, and
changing `p` changes the Argon2 function itself.

Suite 3's default $`m_{\mathrm{bits}} = 2^{34}`$ bits (2 GiB), $`t_{\mathrm{eff}} = 12`$, $`p = 4`$
tuple is not one of RFC 9106's two recommended tuples. It keeps the memory and the four lanes of the
RFC's first recommended option and deliberately raises its single pass to twelve for an infrequent
high-cost backup operation. With four lanes, 2 GiB is the total Argon2 memory, nominally 512 MiB per
lane; it is not 2 GiB per lane.

One MHFE permutation or inverse performs twelve sequential Argon2id calls; an encryption with its
required check performs twenty-four. If one working buffer is reused, its peak Argon2 allocation is
nominally $`m(\mathrm{MEM})`$, 2 GiB at the default memory level, regardless of PIM. At the default
settings, the nominal full-memory-pass volume of one permutation is
$`12 \cdot 12 \cdot 2\,\mathrm{GiB} = 288\,\mathrm{GiB}`$. In general it is
$`288\,\mathrm{GiB} \cdot (\mathrm{PIM} + 1) \cdot m(\mathrm{MEM}) / 2\,\mathrm{GiB}`$. These values
are not runtime predictions or attack-cost proofs. The mapping is exact for suite 3, but its safety,
upper bound, and usability remain provisional until measured across the stated target systems and
reviewed in the full construction.

#### Domain separation

The explicit purpose labels, `BE32(MEM)`, `BE32(PIM)`, and `BE32(i)` separate salt derivation from
mask derivation, different permitted work factors, other protocols, and other rounds. This does
**not** establish security against a named class of Feistel attack; it prevents accidental reuse of
one byte-level domain for different protocol roles.

`SUITE_{ID}` identifies the complete experimental cryptographic suite, not merely an editorial
revision of this document. Any incompatible change to the Feistel geometry or round count `N`; state
packing or encoding; password normalization or limits; salt derivation; the Argon2 variant, version,
fixed parameters, the permitted ranges or cost mappings of PIM and the memory level; or `RoundMask`
requires a new `SUITE_{ID}`, `DS_{SALT}`, and `DS_{MASK}`. Selecting a different permitted PIM or
memory level under the unchanged mappings does not define a new suite. An identifier must not be
reused for a changed mapping.

#### Mnemonic and seed

A **BIP39 mnemonic** is not itself the BIP39 seed. This construction packs the entropy encoded by a
valid BIP39 mnemonic into a 256-bit state. After decryption, normal BIP39 seed derivation may still
use the separate optional BIP39 passphrase.

#### Only the end salts are public

`S_i` is an actual Argon2 salt input, but it is deterministically derived from the Feistel state. It
does not add entropy and is not guaranteed to be globally unique. Only the salts at the two ends of
the chain can be computed without the password: for a known plaintext, `R_0` and therefore `S_0` are
known; when inversion begins from a ciphertext, $`R_{N-1} = L_N`$ is likewise available from the
ciphertext state. Every other salt depends on the password and is as sensitive as the state it comes
from. A leaked intermediate salt `S_i` allows a filter that works backwards from the container and
needs `11 - i` Argon2 calls with twelve rounds: one for `S_10`, eleven for `S_0`. With a known
source the filter can also start from the other end, so that `S_1` is checked after one forward
round. This is the cost of these particular filters, not a proven lower bound for all attacks. The
term **state-derived salt** is used throughout this document instead of "pseudo-salt".

#### Choice of HMAC

HMAC-SHA-256 is a conventional keyed function, but the complete effective MHFE round function
derives its HMAC key from its own input through Argon2id, so the choice of HMAC alone does not make
the effective round functions independent random functions.

### Rationale

#### Why Feistel

The core requirement is a reversible mapping from exactly 256 bits to exactly 256 bits. Feistel
networks provide a convenient way to construct a permutation from a round function that does not
itself need to be invertible. For one round:

```math
\begin{aligned}
input : L_i \mathbin{\Vert} R_i \\
mask  : M_i &= F_i(R_i) \\
output: R_i \mathbin{\Vert} (L_i \oplus M_i)
\end{aligned}
```

The right half remains available after the round as the next left half. This property is what allows
a salt derived from `R_i` to be recomputed during decryption.

#### Why twelve rounds

The round count is informed by results for ideal balanced random Feistel schemes, but those results
must be stated with their attack models. Patarin [14] proves near-full-branch security for seven or
more rounds against adaptive chosen-plaintext attacks; the same paper states ten or more rounds for
adaptive chosen-plaintext-and-ciphertext attacks. A later result [15] establishes its stated
chosen-plaintext-and-ciphertext bound for six or more rounds under that paper's conditions.

$`N = 12`$ is therefore the suite 3 choice: it is six rounds above the six-round threshold in [15],
five rounds above the seven-round CPA threshold in [14], and two rounds above the distinct ten-round
CPCA threshold stated in [14]. These differences are engineering margins, because MHFE uses
password-, settings- and state-dependent effective functions `G_{i,P,MEM,PIM}` rather than
independent random ones. Twelve rounds are an engineering candidate rather than a theorem-backed
security level.

#### Why state-derived salts

A conventional password-encryption format stores a random salt. The zero-metadata requirement
removes that option for the full 24-word domain. MHFE instead derives the Argon2 salt from state
that is available in both encryption and decryption.

This does not create new entropy. It provides per-state KDF diversification without storing an
additional field. For two independently sampled states compared at the same settings and round
index, salt equality can arise either because their 128-bit `R_i` values are equal or because
unequal inputs collide after BLAKE2b-256 is truncated to 128 bits. If the branches are modeled as
independent uniform 128-bit values and BLAKE2b as a random function, the combined probability is
close to $`2^{-127}`$ for one pair. The corresponding birthday scale is approximately $`2^{63.5}`$
comparable invocations. Different settings or round indices make the hash inputs distinct, so only
the approximately $`2^{-128}`$ truncated-hash collision probability remains in that model.
Accidental collisions are therefore expected to be negligible at any realistic number of containers.

MHFE does not claim conformance to NIST SP 800-132, which requires the randomly generated part of a
PBKDF2 salt to have at least 128 bits [48]. The more direct guide for Argon2id is RFC 9106, which
recommends a 16-byte salt for password hashing and a salt unique for each password [13]. MHFE salts
have 16 bytes but are derived from the state instead of being generated at random: for a fixed
password, the permutation must map every 256-bit source to exactly one 256-bit container, which
leaves no room for fresh randomness. Uniqueness is therefore a property to be argued, not one given
by construction. The estimate above, about `2^-127` for one pair of salts at the same settings and
round index under the stated model, covers accidental repetition between independently created
containers; it does not by itself make derived salts equivalent to independently generated ones. A
reviewer would also ask whether an adversary can force salts to repeat, whether related states let
expensive evaluations be reused, and what changes for identical sources, short sources and chosen
inputs; the threat models below and the open questions of Part I address parts of this. SLIP-0039
uses the same kind of salt, the right half of the state, for its extendable backups [20], which
shows that the technique is not unusual but does not establish the security of MHFE. A variant that
kept a 12-word source at its own length, with 64-bit halves (see
[Shorter BIP39 mnemonics](#shorter-bip39-mnemonics)), would have only `2^64` possible salt inputs
per round: the hashed salt would still be 16 bytes long, but its diversity would be limited to 64
bits, which would have to be stated and justified as a deviation. No such variant is planned.

These estimates treat intermediate Feistel branches as independent and uniform. Reprocessing the
same state with the same password, settings and round index repeats the same salt by design; that is
not an accidental collision.

#### Research note: public pre-mixing of the KDF schedule

Public reversible full-state pre-mixing was considered as a way to make the first state-derived KDF
input depend syntactically on the complete source state. It is not selected by any current profile.
For a uniformly random 256-bit source, it has little apparent practical benefit: the original
128-bit right branch already gives a distinct-source pair-collision probability of $`2^{-128}`$ and
a birthday collision scale of approximately $`2^{64}`$ independently sampled sources.

Pre-mixing also cannot prevent adversarially constructed branch collisions because the transform
would be public and invertible. Nor would it add entropy or remove the deterministic relation
between the two halves of a packed short source. The idea is retained only as a record of a
considered alternative; it should not add another cryptographic operation to the principal candidate
without a demonstrated benefit and separate analysis.

#### BIP39 checksum semantics

A 24-word BIP39 mnemonic contains 256 entropy bits and an 8-bit checksum, but only $`2^{256}`$
24-word sequences are valid. The checksum does not provide 8 extra payload bits.

Consequently the baseline transform operates only on the 256-bit entropy and recomputes the standard
checksum afterward. This preserves the BIP39 word count but leaves no independent room for an
authentication tag or version field.

For shorter sources, the universal packing candidate uses the otherwise unoccupied part of that same
256-bit state for `V_r`. This does not alter the outer BIP39 rule: every encrypted container still
carries the ordinary 8-bit checksum of `Y` outside the 256-bit encrypted payload.

#### Baseline and research alternatives

This document keeps one precisely identified baseline, suite 3, while examining competing
directions. The research section compares balanced and source-heavy unbalanced Feistel, as well as
different payload-verification choices. Keeping alternatives in one document is intentional; an
interoperable implementation would still need to select and identify a complete profile.

### Backward Compatibility

This construction changes no Bitcoin consensus, peer-to-peer, or RPC rules. Compatibility concerns
are entirely at the wallet/application layer.

An MHFE-encrypted 24-word mnemonic is intentionally syntactically valid BIP39. A legacy wallet that
supports 24-word English BIP39 mnemonics will generally accept the encrypted mnemonic as an ordinary
mnemonic and generally derive a different wallet from it; the construction does not rule out fixed
points. The encrypted mnemonic contains no in-band flag that says "decrypt me first".

Fixed points are an expected property of the idealized permutation model, not by themselves a
structural failure of the design. A uniformly random permutation on a finite set has exactly one
fixed point in expectation; as the set grows, its fixed-point count approaches a Poisson
distribution with parameter 1. For one particular 256-bit state `X`, however, the probability that
$`\mathrm{Perm}_{P,\mathrm{MEM},\mathrm{PIM}}(X) = X`$ is only $`2^{-256}`$ in that model. A
ciphertext-only observer cannot determine from `Y` alone whether it is such a fixed point of the
unknown permutation parameterized by the password and the settings, so the existence of fixed points
does not supply a generic password test or key-recovery shortcut.

The rare equality still matters operationally because it defeats concealment for that concrete
state. For a 24-word source, $`Y = X`$ makes the encrypted mnemonic identical to the source
mnemonic; for a shorter source it would expose the complete packed state
$`X = E \mathbin{\Vert} V_r`$, even though the word counts differ. The specification therefore
requires creation to compare the input and output states, refuse to present an unchanged state as an
encrypted backup, and ask for a different password, PIM or memory level. Reapplying the same suite
with the same password, settings, and input cannot escape the same fixed point. These operational
checks do not replace analysis of whether the concrete MHFE construction behaves sufficiently like
the idealized permutation.

Applications implementing MHFE must therefore present encrypted mnemonics as a distinct workflow and
must not silently pass them to normal BIP39 seed derivation. Users must retain knowledge that a
backup is MHFE-encrypted; compatible software supplies the exact suite definition rather than
requiring the user to memorize its literal identifier.

With the correct password and compatible suite implementation, MHFE decryption recovers the original
BIP39 mnemonic for use by unmodified BIP39-compatible software. For a short source, the
recovery-verifier check supplies a failure signal for most incorrect candidates; for a 24-word
source, merely completing decryption does not verify that the inputs were correct. If that wallet
also uses the optional BIP39 passphrase, the BIP39 passphrase remains an independent second input
and is applied only after MHFE decryption.

### Security Considerations

#### Status and security claim

MHFE is an experimental research construction that has not been independently reviewed. No real
funds should depend on it. This is the one place where its limits are listed:

- no formal PRP/SPRP proof for the MHFE construction and no proof that twelve rounds are sufficient;
- no proof that the Argon2id-derived round functions satisfy the assumptions of Luby-Rackoff or
  Patarin analyses;
- the per-guess cost arguments in Part I are unreviewed random-oracle sketches;
- no AEAD authentication and no internal wrong-password detection for a 24-word source;
- no formal honey-encryption [16] guarantee; the plausible deniability of
  [decoy disclosures](#deniability) is analysed in Part I in a stated model, without review.

#### Resource exhaustion and untrusted containers

A checksum-valid 24-word input can force a decoder to perform every expensive Argon2id operation
required by the selected suite. The outer BIP39 checksum filters transcription errors but is not
authorization to consume unbounded resources. Suite 3 fixes its KDF parameters for each setting and
bounds the normalized password; implementations must additionally enforce a local resource ceiling
and fail rather than substitute cheaper parameters.

Applications should start recovery only after an explicit user action, should keep the interface
responsive during long operations, and should offer cancellation where the execution environment
permits it. A worker or background thread is a responsiveness boundary, not a cryptographic vault.
Implementations must reject unknown suite identifiers, a PIM outside `0..1023`, a memory level
outside `0..21` or above what they support, and any other caller-supplied parameter override before
allocating large amounts of memory. These measures limit denial-of-service and accidental resource
use; they do not reduce the attacker's offline password-guessing cost.

#### Threat models

The following models must be kept distinct. Unless a model states otherwise, the attacker is assumed
to know the suite and the public settings. The original source length may be known, tried
explicitly, or inferred with the same recovery-verifier rules available to the owner. Known wallet
identity data can provide an external password test, especially for a 24-word source.

**T1 — single-container offline guessing.** The attacker has one encrypted entropy `Y`. A baseline
attack evaluates a candidate inverse permutation
$`\mathrm{Perm}_{P',\mathrm{MEM},\mathrm{PIM}}^{-1}(Y)`$ for each password guess `P'` and checks a
short-source `V_r` relation or any available external evidence. This does not imply that an optimal
attacker must perform a full inversion when a cheaper filter is available.

**T2 — same-password multi-container, ciphertext-only.** Many ciphertexts were created under the
same normalized password, settings, and suite, but their plaintext mnemonics are unknown. This is
not automatically equivalent to a chosen-plaintext or known-pair oracle. Determinism reveals
ciphertext equality when the packed plaintext is repeated, and any attack may also consider the
structured short-source subsets, but unknown plaintexts do not become known pairs merely because
many containers are available.

**T3 — disclosed known pairs.** The attacker knows one or more specific mappings `(X_i, Y_i)` made
under the same password, settings, and suite, for example because the plaintext mnemonic was later
disclosed or compromised by another channel. Such pairs may be used to filter password guesses or to
attack other containers governed by the same permutation.

**T4 — chosen-input oracle access.** The attacker can obtain forward transformations of chosen
plaintexts, inverse transformations of chosen ciphertexts, or both, under one fixed password,
settings, and suite. Forward-only access is closest to classical PRP analysis, while access to both
complete directions is closest to SPRP analysis. An interface that reveals only verifier acceptance
is a weaker oracle but may still provide a useful password filter.

**T5 — cross-container aggregation under a shared weak password.** Independently leaked known pairs
from different users or wallets form one permutation only when the same normalized password,
settings, and suite are shared. If the same weak password is reused with different settings or
suites, those samples belong to different permutations and do not form one classical multi-query
transcript, but they may still be combined as evidence in a dictionary attack on the shared password
by evaluating each applicable parameter set. A large corpus created under unrelated passwords
provides no such shared-password test.

**T6 — active container modification or substitution.** The attacker can replace or alter a recorded
container and recompute its ordinary BIP39 checksum. Suite 3 provides no cryptographic
authentication. A short-source verifier rejects most incorrect recovered states but does not
authenticate the container or its origin; a 24-word source has no internal verifier at all. This
integrity and availability threat must be analyzed separately from offline password guessing and
confidentiality. The checks that a recovery can use trust different things, and none of them alone
protects against substitution:

| Check                                                   | What it confirms                                                            | What it does not confirm                                                     |
| ------------------------------------------------------- | --------------------------------------------------------------------------- | ---------------------------------------------------------------------------- |
| The container's BIP39 checksum                          | The words were recorded and read without most accidental errors             | That the container is genuine: anyone can recompute it                       |
| The recovery verifier of a short source                 | The recovered state satisfies the verifier relation for the selected length | Authenticity: whoever knows the password can build another passing container |
| The check at creation, decoding the words and inverting | This implementation and computer produced a consistent container            | Anything about a copy that is replaced later                                 |
| A known address or fingerprint                          | The recovered phrase belongs to the expected wallet                         | Anything, if the address itself came from an untrusted source                |

**T7 — old containers after a change.** A container stays useful to an attacker for as long as its
source phrase controls funds. Encrypting the same source again under a new password, higher settings
or a new suite does not neutralize an old container that was copied or stolen: it can still be
attacked with its own password and settings, and it recovers the same wallet. This differs from T5,
because the old and the new passwords may be unrelated. The practical protection is that of the
weakest copy an attacker can obtain; a new password protects the funds only after they are moved to
a new source phrase, or after every old copy is destroyed.

**T8 — partly known or weak source.** The analysis assumes a uniformly random source that the
attacker does not know. If part of the source leaks, the remaining uncertainty can be small: when
the first 11 words of a 12-word phrase are known, the last word carries 7 entropy bits and the 4-bit
checksum, so 128 completions remain, and with a known address and no BIP39 passphrase they can be
tested without MHFE at all. A strong container password does not undo a leak of the source itself,
and a source generated with little entropy is weak in the same way. The bounds of Part I describe a
uniform source; extending them to partial leaks would require including that information in the
model explicitly.

#### Where known pairs can come from

A known pair is not free information. Realistic sources include later voluntary disclosure,
inheritance, audit, migration, independent compromise of a plaintext backup, malware observing a
later recovery, or deliberately published test material. The attacker must be able to link a
specific plaintext `X_i` to a specific encrypted container `Y_i`.

#### Known-plaintext shortcut and KDF cost

`N` Feistel rounds do not by themselves prove a lower bound of `N` expensive Argon2 evaluations per
wrong password guess.

Given a known plaintext/ciphertext pair, an attacker can compute forward from `X` through some
rounds and backward from `Y` through the remaining rounds. At a skipped round, the Feistel relation

```math
\begin{aligned}
L_{i+1} &= R_i
\end{aligned}
```

can be checked without evaluating that round's mask. This provides a password filter when the
compared halves depend on the password guess, while omitting a selected expensive round. For
example, omitting the only round of a one-round network gives no password-dependent filter. The
rejection rate and the best multi-round shortcut require analysis of the full construction.

In a multiround design with earlier password-dependent inexpensive rounds, making only the last
round memory-hard permits an initial known-pair password filter that omits the expensive round. Its
effectiveness still depends on the preceding rounds.

#### Birthday bounds and password guessing

For a balanced Feistel network with a `2n`-bit state and `n`-bit branches, classical small-round
multi-query analyses contain birthday-scale terms around:

```math
\begin{aligned}
q ~ 2^{n/2}
\end{aligned}
```

where `q` counts queries or known/chosen pairs under one fixed permutation.

For the 128-bit same-length research variant, $`n = 64`$, giving a birthday scale around $`2^{32}`$
in those classical games. That number must **not** be reinterpreted as "the password breaks after
$`2^{32}`$ guesses". In T1, different password guesses select different password-indexed
permutations at the selected settings, so the guesses do not accumulate as `q` queries to one fixed
`Perm_{P,MEM,PIM}`. For the 256-bit state of suite 3, $`n = 128`$ and the corresponding birthday
scale is around $`2^{64}`$ queries under one fixed permutation.

The multi-query viewpoint becomes relevant only when many samples genuinely belong to the same
permutation, parameterized by the password and the settings, and the attack has the information
model required by the particular proof or distinguisher.

#### Patarin and beyond-birthday security

The birthday scale is not a universal ceiling for balanced Feistel networks. Patarin's positive
security results show that, with enough rounds and independent random round functions, balanced
Feistel constructions can achieve security far beyond the basic birthday scale and approach the
information-theoretic scale associated with the branch size [14], [15], [18]. Reference [17] instead
develops generic attacks on Feistel schemes and supplies adversarial limits.

These results show that a 64-bit branch does not by itself imply a hard $`2^{32}`$ security ceiling.

The relevant question for MHFE is whether its effective round functions satisfy assumptions strong
enough to justify any Patarin-style reduction.

#### Effective round function

For fixed password `P`, settings, and round index `i`, define the effective round function:

```math
\begin{aligned}
S_i(R) &= \mathrm{Trunc}_{128}(\mathrm{BLAKE2b\text{-}256}(\mathrm{DS}_{\mathrm{SALT}} \mathbin{\Vert} \mathrm{BE32}(\mathrm{MEM}) \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM}) \mathbin{\Vert} \mathrm{BE32}(i) \mathbin{\Vert} R)) \\
\\[0.4em]
K_i(R) &= \mathrm{Argon2id}\!\left(
\begin{gathered}
\mathrm{password}=P_{\mathrm{encoded}},\quad \mathrm{salt}=S_i(R), \\
\mathrm{memory}=m(\mathrm{MEM})\ \mathrm{KiB},\quad \mathrm{passes}=t(\mathrm{PIM}),\quad \mathrm{lanes}=4, \\
\mathrm{version}=\mathtt{0x13},\quad \mathrm{type}=\mathrm{Argon2id}, \\
\mathrm{secret}=\varnothing,\quad \mathrm{associated\_data}=\varnothing,\quad
\mathrm{outlen}_{\mathrm{bits}}=256
\end{gathered}
\right) \\
\\[0.4em]
G_{i,P,\mathrm{MEM},\mathrm{PIM}}(R) &= \mathrm{Trunc}_{128}(\mathrm{HMAC\text{-}SHA\text{-}256}(K_i(R),\ \mathrm{DS}_{\mathrm{MASK}} \mathbin{\Vert} \mathrm{BE32}(\mathrm{MEM}) \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM}) \mathbin{\Vert} \mathrm{BE32}(i) \mathbin{\Vert} R))
\end{aligned}
```

This is exactly the same 128-bit salt, 256-bit derived key, Argon2id profile, and round-mask
function used in encryption and decryption. No Argon2 parameter or optional input is implicit in
this expanded definition. For fixed settings, $`m(\mathrm{MEM})`$ and
$`t(\mathrm{PIM}) = 12(\mathrm{PIM} + 1)`$ are as specified for suite 3. Here `K_i(R)` is the
functional form of the round key; evaluating it at the actual branch `R_i` gives the normative round
key `K_i`.

Although the internal derived subkey depends on `R`, `G_{i,P,MEM,PIM}` is still one deterministic
function from 128-bit inputs to 128-bit outputs. Therefore generic Feistel analysis cannot be
dismissed merely because the internal subkey is input-dependent.

At the same time, attacks that specifically rely on reusing one fixed internal subkey over many `R`
values do not automatically transfer unchanged to this construction.

#### Argon2 salt-separation hypothesis

A potentially favorable heuristic concerns diversification across distinct `(i,R)` inputs. Different
inputs are not guaranteed to produce different 128-bit salts, and distinct salts do not
mathematically guarantee distinct 256-bit Argon2id outputs. In an ideal random-function model, two
distinct salts produce the same 256-bit output with probability $`2^{-256}`$ per pair, so accidental
output collision is not the principal concern here. Repeated `(MEM,PIM,i,R)` inputs under the same
password and suite necessarily reuse the same salt and key. If, for fixed unknown `P`, fixed
settings (and therefore fixed memory and passes), and all other suite parameters, the mapping

```math
S \longmapsto \mathrm{Argon2id}(P_{\mathrm{encoded}},S;\text{ fixed suite 3 parameters})
```

behaves with sufficient pseudorandomness and decorrelation over distinct public salts, this might
support a random-function model for the effective functions `G_{i,P,MEM,PIM}`. A useful assumption
would need to cover their joint behavior across rounds and inputs, account for salt collisions and
repeated inputs, and incorporate both the guessability of the password and behavior across
attacker-chosen password candidates. Input-dependent keys alone do not establish an advantage over a
conventional keyed round function.

Argon2id was designed and analyzed primarily as a memory-hard password hash/KDF and for resistance
to time-memory trade-offs. RFC 9106 discusses Argon2 security as a hash function and KDF, but
neither cited source establishes the construction-specific joint-pseudorandomness property that MHFE
would require across many salts at one fixed low-entropy human password. A1 is therefore a separate
assumption that must be justified or removed by a future proof or construction [13], [19].

Call this open assumption **A1 — Argon2 salt-separation hypothesis**.

#### Argon2id and side channels

Argon2id combines data-independent and data-dependent memory addressing: slices 0 and 1, the first
half of the first pass, follow the Argon2i-style data-independent strategy, while the remaining
computation uses Argon2d-style data-dependent addressing. It is therefore inaccurate to characterize
Argon2id's memory-addressing pattern as uniformly data-independent or uniformly data-dependent [13].

Implementations should use a well-reviewed Argon2id library, follow its memory-wiping facilities
where available, and separately analyze timing/cache exposure on the target platform. Native desktop
and browser/WASM implementations may have different side-channel constraints even on otherwise
supported high-memory systems.

#### Recovery verification is not authentication

A reversible mapping over all $`2^{256}`$ entropy values consumes the entire 256-bit output domain.
A separate authentication tag cannot be embedded without reserving some outputs, adding external
bits, or giving up full-domain bijectivity.

The ordinary 8-bit BIP39 checksum on the encrypted mnemonic detects many accidental transcription
errors; a uniformly random 264-bit candidate passes that relation with probability $`2^{-8}`$. It is
not a cryptographic authentication tag. An attacker can modify the 256-bit entropy and recompute a
valid checksum. Likewise, the checksum recomputed after decryption cannot validate the MHFE password
because every 256-bit candidate entropy has one corresponding valid BIP39 checksum.

Short-source profiles deliberately reserve a strict subset of the 256-bit plaintext domain by
requiring $`X = E \mathbin{\Vert} \mathrm{Trunc}_{r}(\mathrm{SHA256}(E))`$. A uniformly random
recovered state satisfies that relation with probability $`2^{-r}`$, so the verifier detects most
wrong-password candidates and untargeted corruption under the corresponding uniform-candidate model.
It nevertheless remains an unkeyed relation inside the encrypted plaintext. It does not provide AEAD
authenticity, establish the container's origin, protect against every maliciously constructed
replacement, or conceal from an offline attacker whether a fully decrypted password candidate passed
the same relation.

#### Determinism and equality leakage

For one fixed password, settings, and plaintext entropy, the ciphertext is deterministic:

```math
\begin{aligned}
\mathrm{Perm}_{P,\mathrm{MEM},\mathrm{PIM}}(X) &= Y
\end{aligned}
```

with no nonce. Re-encrypting the same `X` under the same normalized `P` and the same settings yields
the same `Y`. Because `Perm_{P,MEM,PIM}` is a bijection, the converse also holds within one fixed
suite, password, and settings: equal ciphertexts imply equal packed plaintexts. An observer who
knows that two containers use that same permutation can therefore recognize reuse of one packed
state, although the state itself remains unknown. This normally indicates reuse of one source; the
rare case in which one packed state satisfies more than one short-source layout remains subject to
the source-length ambiguity rule.

Ciphertext equality across different passwords, settings, or suites does not establish plaintext
equality because those settings select different permutations. For two independently and uniformly
sampled BIP39 sources of the same `ENT`-bit length, the pairwise source-equality probability is
$`2^{-\mathrm{ENT}}`$; even the shortest supported 128-bit source therefore has probability
$`2^{-128}`$ for one pair and a birthday scale near $`2^{64}`$ sources. Accidental equality is
negligible at realistic scales, but deliberate reuse remains visible under one fixed permutation.

#### Password quality

Memory-hard KDF evaluations are intended to raise offline-guessing cost; they do not create entropy
in a weak human password. Effective guessing cost depends on the unavoidable KDF evaluations,
password quality, available verification, and any structural shortcut that reduces the required
Argon2 work per guess.

#### Sensitive-memory handling

Implementations should minimize copies of plaintext entropy, encoded password, Argon2 outputs, and
intermediate Feistel states, and should erase such buffers when the language/runtime provides a
reliable mechanism. This is an implementation hygiene requirement, not a substitute for analysis of
the cryptographic construction.

### Related Work and Alternatives

#### SLIP-0039

SLIP-0039 is especially relevant prior art [20]. Its master-secret encryption already uses a
four-round Feistel network in which PBKDF2 acts as the round function and the current right half `R`
is included in the PBKDF2 salt. In its extendable-backup mode the additional salt prefix is empty;
the right half remains part of the PBKDF2 salt.

Therefore the broad idea "Feistel + password KDF + current Feistel half in the KDF salt" is **not
novel to MHFE**. Any novelty claim must be narrower and should focus, if justified, on the exact
combination of a full 256-bit BIP39 entropy permutation, no in-band per-container metadata, Argon2id
memory hardness, and the resulting security/compatibility analysis.

SLIP-0039 differs materially in purpose and format: it is a Shamir mnemonic-sharing standard with
its own identifier, extendable-backup flag, iteration exponent, wordlist, and share structure. It
does not define an in-place 24-word BIP39-to-BIP39 encryption format.

#### BIP38

BIP38 standardizes passphrase-protected private keys and uses scrypt plus AES [21]. It stores format
information and a 32-bit address hash inside an expanded encoded record. This provides useful prior
art for password normalization, KDF parameterization, test vectors, and wrong-password verification,
but it does not satisfy the zero-expansion 24-word requirement.

#### BIP39 optional passphrase

BIP39 itself already gives every mnemonic/passphrase pair a valid derived seed, without a built-in
passphrase-error signal. This can support deniability in some contexts, but known wallet information
can still verify a guess. That mechanism affects seed derivation, not encryption of the mnemonic
backup [2]. MHFE must not be presented as a replacement for the BIP39 passphrase; the two can
coexist.

#### Honey encryption

Juels and Ristenpart formalize honey encryption for low-min-entropy keys by using a
distribution-transforming encoder so that decryption under wrong keys yields plausible messages
[16]. This is the relevant source for the term, but it does not describe MHFE's present security
claim. MHFE does not define a general encoder for arbitrary, non-uniform distributions of wallet
entropy; known wallet addresses can verify a candidate; and the short-source recovery verifier
intentionally rejects almost all wrong-password candidates. Syntactically valid BIP39 output is
therefore not sufficient to claim honey-encryption security in general. The special case of a
uniformly generated 24-word source, with a uniform model and the identity as its encoder, is
analysed in Part I together with [decoy disclosures](#deniability).

#### Earlier BIP39 backup-encryption and obfuscation proposals

A 2021 Bitcoin Stack Exchange discussion asked directly how an existing BIP39 mnemonic could be
encrypted into another mnemonic without changing the recovered wallet seed and linked a small
AES-CTR prototype [3], [4], [22]. This is direct community history for the problem statement. The
initial prototype derived its AES key as $`\mathrm{SHA256}(\mathrm{password})`$; a later revision
changed that step to PBKDF2-HMAC-SHA512 with 2,048 iterations and the fixed salt
`mnemonic-encryption`. Both revisions use AES-CTR with an all-zero IV. Reusing one password
therefore repeats the CTR keystream, so for two source entropies `E_1` and `E_2` and their
ciphertext entropies `C_1` and `C_2`:

```math
\begin{aligned}
C_1 \oplus C_2 &= E_1 \oplus E_2
\end{aligned}
```

The relation alone does not recover either of two independently random and otherwise unknown
entropies. If either entropy is known or attacker-controlled, however, it reveals the other one
directly. This is separate from the cost of deriving the password key and violates CTR's
cross-message counter-block uniqueness requirement [23]. The prototype was not a bitcoin-dev
mailing-list proposal. MHFE avoids this particular relation through a password-indexed permutation
and state-derived round inputs.

`Seedshift`, `bip39_obfuscator`, and `BIP39Colors` are community projects for shifting BIP39 word
indices or re-encoding them as Traditional Chinese wordlist code points or RGB colors [24], [25],
[26]. They illustrate demand for backups that do not visibly expose the original English words, but
they provide forms of concealment rather than comparable modern encryption. `bip39_obfuscator`
applies a public, deterministic index-for-index mapping with no secret key; anyone who recognizes
the representation can reverse it. `BIP39Colors` likewise uses a public deterministic encoding that
packs the positions of 12 or 24 BIP39 words into 8 or 16 hexadecimal RGB colors and includes enough
position information to recover the words even when the colors are reordered [26]. It has no secret
key and therefore provides visual obfuscation rather than confidentiality against an informed
observer. `Seedshift` applies manually computable modular shifts derived from dates. Its own
documentation warns that the result is not cryptographically secure and can be brute-forced [24].
None of these constructions uses a memory-hard KDF or provides a security argument for a
password-indexed pseudorandom permutation. They should therefore be treated as public re-encodings,
obfuscation, or a simple shift cipher, not as substitutes for reviewed mnemonic encryption. This
comparison does not itself establish the security of MHFE.

`MnemonicCrypt` is a closer implemented comparison: it removes the source BIP39 checksum, applies
configurable Argon2id and AES-CBC with a separate random 128-bit salt, and renders the ciphertext
and salt as word sequences [27]. For a 12-word source it produces a 24-word encrypted mnemonic plus
a 12-word salt mnemonic, or 36 words of total recovery material. For a 24-word source it produces a
36-word encrypted mnemonic plus a 12-word salt mnemonic, or 48 words in total. The KDF parameters
must also be preserved separately. Its padded representation is intentionally an extension of BIP39
rather than an ordinary wallet-generated mnemonic. It therefore addresses password hardening and
word-oriented storage, but not MHFE's fixed 24-word, no-in-band-metadata design constraint.

Other mnemonic encryption systems reserve capacity or change the mnemonic domain. `Mnemonikey`
encodes a 128-bit OpenPGP seed in a custom 4,096-word list; its encrypted 16-word form carries a
version, creation time, random salt, encrypted seed, checksum, and a 5-bit password verifier, and
derives its AES-128 key with Argon2id [28]. `pktseed` defines a custom 15-word PKT seed containing
version, encryption, checksum, birthday, and seed fields [29]. Its current encryption code derives a
19-byte mask from Argon2id with a fixed salt and XORs that mask with the birthday-and-seed payload,
so same-passphrase reuse creates a cross-record XOR relation analogous to the Niondir prototype.
These are useful comparisons for compact mnemonic metadata and recovery verification, but neither
transforms an existing BIP39 mnemonic into another BIP39 mnemonic.

`seed-otp` takes a different approach: it adds a separately stored per-word pad modulo 2,048 [30].
This can preserve the source word count and BIP39 wordlist membership and can provide one-time-pad
security when the pad is uniformly random, secret, and never reused. Its ciphertext normally fails
the BIP39 checksum, and the scheme moves the backup burden to another secret of comparable size
rather than deriving protection from a memorable password.

A non-exhaustive search of public GitHub repositories and the cited community discussions, last
repeated on 2026-09-22, found many encrypted wallet files, mnemonic obfuscators, secret-sharing
formats, and custom word encodings, but no implementation combining all of the following properties:

- an existing 12-, 15-, 18-, 21-, or 24-word BIP39 source;
- one ordinary checksum-valid 24-word BIP39 ciphertext container;
- exact recovery of the original entropy under a password;
- for every shorter source, use of all otherwise unused state capacity as one hash-based recovery
  verifier $`V_r = \mathrm{Trunc}_r(\mathrm{SHA256}(E))`$, whose first $`\mathrm{ENT}/32`$ bits are
  exactly the source mnemonic's BIP39 checksum and whose 128-, 96-, 64-, or 32-bit width gives
  uniform-candidate false-acceptance probability $`2^{-128}`$, $`2^{-96}`$, $`2^{-64}`$, or
  $`2^{-32}`$, respectively, without expanding the container;
- no mandatory separately stored salt, nonce, authentication tag, or expansion words; the default
  settings are implicit, while deliberately selected non-default settings must be remembered; and
- a memory-hard, state-derived KDF schedule inside a format-preserving permutation.

This search result narrows the known comparison set; it is not an exhaustive prior-art search, a
novelty claim, or evidence that MHFE is secure.

#### Luby-Rackoff and Patarin

Luby-Rackoff supplies the foundational theory for constructing pseudorandom permutations from round
functions. Patarin's later work is relevant to generic attacks and beyond-birthday security for
multi-round balanced and unbalanced Feistel schemes. These papers define the PRP/SPRP models and
Feistel bounds against which MHFE should be evaluated. Their proofs assume independent idealized
round functions. MHFE instead derives every effective round function from one password and
state-dependent Argon2id inputs, so their security bounds cannot be claimed for MHFE without a
separate construction-specific reduction [14], [15], [17], [18], [31].

#### Format-preserving encryption

General FPE constructions demonstrate how to build permutations on constrained domains [32], but
they do not by themselves provide memory-hard password guessing or solve the no-metadata salt
problem. Morris, Oberschelp, and Santhakumar construct a no-expansion pseudorandom permutation in
the bounded retrieval model using a large key, random-oracle assumptions, and the Thorp shuffle
[33]. Its hybrid analysis and explicit treatment of uniform distinct messages are relevant
methodology, but its leakage model, key structure, round function, and security game differ
materially from MHFE.

#### Thorp and maximally unbalanced Feistel

Thorp-style constructions are important prior art for very small domains and show that the birthday
behavior of a small balanced branch is not a universal limitation of all Feistel architectures.
Published Thorp bounds [34] use many cheap micro-rounds. Substituting a full Argon2id invocation for
every micro-round can require hundreds or more expensive calls at these state sizes, depending on
the selected bound and target security. This suggests a substantial latency problem, but neither a
practical latency figure nor a universal minimum round count follows without choosing and analyzing
a specific construction. Whether a memory-hard key can safely control a whole pass of cheap
unbalanced rounds without reintroducing a state/salt circular dependency remains an open research
question.

### Theoretical Investigation and Alternative Designs

The following sections explain the packing and the geometry that suite 3 adopted and record the
alternatives that were studied but not adopted. Suite 3 uses the balanced $`128 \mid 128`$-bit
Feistel network and the universal packing below. The shorter-state variants, the final-word profile
and the source-heavy 1:3 family are research alternatives, not production recommendations or
finalized encodings. Unless explicitly labeled otherwise, sizes in the construction formulas and
tables below are expressed in bits.

#### Shorter BIP39 mnemonics

BIP39 entropy sizes are:

| Words | ENT | BIP39 checksum | Full mnemonic bits | Spare bits after storing ENT only |
| ----: | --: | -------------: | -----------------: | --------------------------------: |
|    12 | 128 |              4 |                132 |                               128 |
|    15 | 160 |              5 |                165 |                                96 |
|    18 | 192 |              6 |                198 |                                64 |
|    21 | 224 |              7 |                231 |                                32 |
|    24 | 256 |              8 |                264 |                                 0 |

The last column assumes that the original checksum is discarded and later recomputed. It does not
describe capacity after storing the complete original word bitstring.

A balanced Feistel transform operating directly on each `ENT`-bit source entropy would use branch
sizes of 64, 80, 96, 112, and 128 bits respectively. The 64-bit branch of a 12-word mode does not
automatically imply a $`2^{32}`$ password security ceiling; classical birthday bounds and password
guessing are different attack models, and Patarin-style results show that multi-round Feistel can
exceed the basic birthday regime in ideal models. Nevertheless, every shorter state size would
require separate analysis.

#### Universal 24-word containers for shorter sources

Suite 3 packs every standard BIP39 source length with one formula:

```math
\begin{aligned}
\mathrm{ENT} &= bit length of source entropy E \\
r   &= 256 - \mathrm{ENT} \\
\\[0.4em]
V_r &= \mathrm{Trunc}_{r}(\mathrm{SHA256}(E)) \\
X   &= E \mathbin{\Vert} V_r
\end{aligned}
```

When $`\mathrm{ENT} = 256`$, $`r = 0`$, `V_r` is the empty bitstring, and $`X = E`$. For every
shorter source, the source entropy is retained exactly and every remaining position in the 256-bit
state is filled by deterministic recovery-verifier bits. No independent checksum field, second
custom check, tag, padding rule, or random filler is added.

| Source words | `ENT` | `r` | Packed state `X`                                                           | Uniform-candidate verifier acceptance |
| -----------: | ----: | --: | -------------------------------------------------------------------------- | ------------------------------------: |
|           12 |   128 | 128 | $`E_{128} \mathbin{\Vert} \mathrm{Trunc}_{128}(\mathrm{SHA256}(E_{128}))`$ |                          $`2^{-128}`$ |
|           15 |   160 |  96 | $`E_{160} \mathbin{\Vert} \mathrm{Trunc}_{96}(\mathrm{SHA256}(E_{160}))`$  |                           $`2^{-96}`$ |
|           18 |   192 |  64 | $`E_{192} \mathbin{\Vert} \mathrm{Trunc}_{64}(\mathrm{SHA256}(E_{192}))`$  |                           $`2^{-64}`$ |
|           21 |   224 |  32 | $`E_{224} \mathbin{\Vert} \mathrm{Trunc}_{32}(\mathrm{SHA256}(E_{224}))`$  |                           $`2^{-32}`$ |
|           24 |   256 |   0 | `E256`                                                                     |                  No internal verifier |

This construction exploits a direct relationship with BIP39. For a source entropy of length `ENT`,
the ordinary BIP39 checksum is:

```math
\begin{aligned}
\mathrm{CS} &= \mathrm{Trunc}_{\frac{\mathrm{ENT}}{32}}(\mathrm{SHA256}(E))
\end{aligned}
```

Because `V_r` is a longer prefix of that same digest for every short source, its first
$`\frac{\mathrm{ENT}}{32}`$ bits are exactly the original BIP39 checksum. The remainder extends the
same check:

| Source words |       Original BIP39 checksum inside `V_r` | Additional verifier bits | Total `V_r` |
| -----------: | -----------------------------------------: | -----------------------: | ----------: |
|           12 |                                          4 |                      124 |         128 |
|           15 |                                          5 |                       91 |          96 |
|           18 |                                          6 |                       58 |          64 |
|           21 |                                          7 |                       25 |          32 |
|           24 | Not present in `V_r`; recomputed on output |                        0 |           0 |

The important economy is conceptual and structural: the source checksum is not stored twice, and all
remaining capacity becomes one continuous verifier. For example, the 21-word profile does not store
a 7-bit checksum plus a separate 25- or 32-bit field. It stores one 32-bit SHA-256 prefix whose
first 7 bits already are the source checksum and whose remaining 25 bits strengthen recovery
screening.

The full data path is:

```text
source entropy E
    || Trunc_(256-ENT)(SHA256(E))
                    |
                    v
      256-bit packed plaintext X
                    |
              MHFE Perm_{P,MEM,PIM}
                    |
                    v
       256-bit encrypted entropy Y
                    |
          BIP39 checksum CS8(Y)
                    |
                    v
        24-word encrypted container
```

The inner `V_r` and outer `CS8(Y)` have different purposes. `V_r` is encrypted with the source and
checks a candidate recovery after MHFE decryption. `CS8(Y)` is the ordinary visible BIP39 checksum
of the encrypted container and detects many recording or transcription errors before decryption. The
outer checksum contributes no additional wrong-password rejection because it is computed from `Y`
and can be recomputed by anyone.

The measurable reasons for this short-source packing are recovery verification, probabilistic
source-length detection, complete use of otherwise unoccupied payload capacity, and the hypothesized
near-full-width marginal distribution of the first-round KDF context. Its explicit costs are known
redundancy, an offline password oracle after candidate decryption, and a structured and correlated
initial Feistel state. The last property is an analysis requirement; adding another public hashing
or mixing layer would not remove the deterministic relation.

##### Recovery-verifier properties

For one explicitly selected short source length, recovery parses `X` into $`E \mathbin{\Vert} V_r`$
and accepts the candidate only if:

```math
\begin{aligned}
V_r &= \mathrm{Trunc}_{r}(\mathrm{SHA256}(E))
\end{aligned}
```

All `r` bits are compared. For uniformly distributed candidate `X`, the set of states satisfying
this relation has exactly $`2^{\mathrm{ENT}}`$ members among $`2^{256}`$, because each possible `E`
determines one and only one `V_r`. Its acceptance fraction is therefore exactly $`2^{-r}`$; this
counting statement does not require treating SHA-256 as a random oracle. Applying that fraction to
actual wrong-password decryptions does require an appropriate assumption about the MHFE
permutation's candidate distribution.

`V_r` is an unkeyed **recovery verifier**, not AEAD, and does not authenticate the container or its
origin. Anyone can alter `Y` and recompute the visible outer BIP39 checksum. Without the password,
however, that party cannot in general choose the resulting decrypted `X` or recompute a valid
verifier inside the encrypted plaintext; under the uniform-candidate model, an altered candidate
passes with probability $`2^{-r}`$. A party that knows the password can construct a different valid
container. Both the owner and an offline attacker testing password candidates can evaluate `V_r`
after candidate decryption. The intended cost control is that obtaining the candidate requires the
MHFE inverse and its memory-hard Argon2id evaluations; whether the structured state permits a
shortcut using fewer KDF evaluations is an explicit open research question.

The verifier does not add source entropy. A 12-word source still has 128 bits of source entropy, not
256, even though its packed state is 256 bits wide. Its remaining 128 bits are completely determined
by `E`.

##### Fixed $`128 \mid 128`$ state structure

The packing gives every source length the same 256-bit balanced Feistel geometry:

```math
\begin{aligned}
L_0 &= E[0{:}128] \\
R_0 &= E[128{:}\mathrm{ENT}] \mathbin{\Vert} V_r
\end{aligned}
```

| Source words | `L_0` | Raw source bits in `R_0` | Hash-derived bits in `R_0` | Conditional source entropy in `R_0` given `L_0` |
| -----------: | ----: | -----------------------: | -------------------------: | ----------------------------------------------: |
|           12 |   128 |                        0 |                        128 |                                               0 |
|           15 |   128 |                       32 |                         96 |                                              32 |
|           18 |   128 |                       64 |                         64 |                                              64 |
|           21 |   128 |                       96 |                         32 |                                              96 |
|           24 |   128 |                      128 |                          0 |                                             128 |

For every short profile, `R_0` includes hash-derived information computed from all of `E`; it also
feeds the first state-derived salt. This makes one fixed implementation possible and avoids separate
64-, 80-, 96-, and 112-bit balanced cores. It does not create independent entropy or by itself prove
stronger Feistel security. Dependencies among round inputs, repeated salts, related structured
states, and shortened password-testing paths still require analysis.

For a uniformly random source, the final table column is exact rather than approximate. Let
`\mathsf{H}` denote Shannon entropy in bits, distinct from the salt-hash symbol `H`. Write
$`E = L_0 \mathbin{\Vert} T_t`$, where $`t = \mathrm{ENT} - 128`$. The packing copies `T_t` verbatim
into `R_0` and appends a deterministic hash prefix. For each fixed `L_0`, different `T_t` values
therefore produce different `R_0` values, so:

```math
\begin{aligned}
\mathsf{H}(R_0 \mid L_0) &= \mathsf{H}(T_t \mid L_0) = t
\end{aligned}
```

The resulting conditional source entropy is exactly 0, 32, 64, 96, or 128 bits for 12-, 15-, 18-,
21-, or 24-word sources respectively, under the stated uniform-source assumption. This conditional
property is distinct from the marginal distribution of `R_0`: a branch can look close to a
full-width 128-bit value when observed alone while still being correlated with, or in the 12-word
case completely determined by, `L_0`. Well-distributed does not mean independent.

###### Early whole-source sensitivity and the structured plaintext domain

The verifier provides one concrete early whole-source-sensitivity property. A conventional balanced
Feistel round function sees only `R_0`, and MHFE likewise forms its first state-derived KDF input
from `R_0`. In each short-source profile here, however, the hash-derived suffix of `R_0` is computed
from all source entropy `E`. Under the hash-prefix heuristic stated below, the first state-derived
salt is therefore sensitive to changes in either original half.

For a change confined to `L_0`, the raw entropy tail in `R_0` remains fixed and sensitivity comes
from `V_r`. Under the heuristic that the relevant SHA-256 prefix behaves like a uniform `r`-bit
value, the probability that this verifier suffix remains unchanged is $`2^{-r}`$: $`2^{-128}`$,
$`2^{-96}`$, $`2^{-64}`$, or $`2^{-32}`$ for 12-, 15-, 18-, or 21-word sources respectively. If
`R_0` changes, the subsequent 128-bit salt hash is also expected to change except for its own
collision probability.

This property comes with a structured plaintext domain. For each short source length, valid packed
states form the set:

```math
\mathcal{S}_{\mathrm{ENT}} =
\left\{ E \mathbin{\Vert}
\mathrm{Trunc}_{256-\mathrm{ENT}}(\mathrm{SHA256}(E))
\;\middle|\; E \in \{0,1\}^{\mathrm{ENT}} \right\}
```

$`\mathcal{S}_{\mathrm{ENT}}`$ contains exactly $`2^{\mathrm{ENT}}`$ states and occupies the
fraction $`2^{\mathrm{ENT}-256}`$ of the complete 256-bit domain. It is a structured subset,
specifically the graph of a deterministic truncated-hash function; it is not generally a linear
subspace.

That restricted size is not a special price paid for early whole-source sensitivity. It is
mathematically unavoidable for any deterministic lossless encoding of an `ENT`-bit source into a
256-bit container: there are only $`2^{\mathrm{ENT}}`$ distinct sources to place in $`2^{256}`$
possible states. The hash-based construction chooses how those states are distributed and
simultaneously supplies recovery verification and early whole-source sensitivity.

A permutation satisfying full-domain PRP security remains indistinguishable when an adversary
restricts its queries to a structured subset. The existence of $`\mathcal{S}_{\mathrm{ENT}}`$ is
therefore not by itself evidence of a weakness. Because MHFE's KDF schedule depends on the evolving
state, analysis must still determine whether the public relation defining
$`\mathcal{S}_{\mathrm{ENT}}`$ enables related-input, known-pair or reduced-KDF password tests.

###### Collision-diversity hypothesis for the first state-derived salt

The mixed raw-and-hash construction may give `R_0` close to 128 bits of collision diversity across
distinct independently sampled source entropies, even though the hash suffix adds no independent
entropy. Reuse of the exact same source is excluded from this statement because the construction is
deterministic and necessarily reproduces the same `R_0`.

For the 21-word profile:

```math
R_0 =
\underbrace{E[128{:}224]}_{96\ \mathrm{bits}}
\mathbin{\Vert}
\underbrace{\mathrm{Trunc}_{32}(\mathrm{SHA256}(E))}_{32\ \mathrm{bits}}
```

Two distinct independent sources must first have the same 96-bit entropy tail and then the same
32-bit hash prefix to produce the same `R_0`. Under the heuristic that the SHA-256 prefix behaves
independently for distinct full inputs sharing that tail:

```math
\Pr[R_0^{(1)} = R_0^{(2)}]
\approx 2^{-96} \cdot 2^{-32} = 2^{-128}
```

The same heuristic pattern holds for every supported source length:

| Source words | `R_0` construction                                                                     | Heuristic distinct-source pair-collision probability |
| -----------: | -------------------------------------------------------------------------------------- | ---------------------------------------------------: |
|           12 | $`\mathrm{Trunc}_{128}(\mathrm{SHA256}(E_{128}))`$                                     |                           approximately $`2^{-128}`$ |
|           15 | $`E_{\mathrm{tail},32} \mathbin{\Vert} \mathrm{Trunc}_{96}(\mathrm{SHA256}(E_{160}))`$ |   approximately $`2^{-32} \cdot 2^{-96} = 2^{-128}`$ |
|           18 | $`E_{\mathrm{tail},64} \mathbin{\Vert} \mathrm{Trunc}_{64}(\mathrm{SHA256}(E_{192}))`$ |   approximately $`2^{-64} \cdot 2^{-64} = 2^{-128}`$ |
|           21 | $`E_{\mathrm{tail},96} \mathbin{\Vert} \mathrm{Trunc}_{32}(\mathrm{SHA256}(E_{224}))`$ |   approximately $`2^{-96} \cdot 2^{-32} = 2^{-128}`$ |
|           24 | `E_{tail,128}`                                                                         |         $`2^{-128}`$ for independent uniform sources |

The $`2^{-128}`$ entries describe the probability that one distinct independently sampled pair has
the same `R_0`; they do not mean that collisions require $`2^{128}`$ samples. The corresponding
birthday scale is approximately $`2^{64}`$ independent sources.

The first state-derived salt is:

```math
S_0 = \mathrm{Trunc}_{128}\!\left(
  \mathrm{BLAKE2b\text{-}256}\!\left(
    \mathrm{DS}_{\mathrm{SALT}}
    \mathbin{\Vert} \mathrm{BE32}(\mathrm{MEM})
    \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM})
    \mathbin{\Vert} \mathrm{BE32}(0)
    \mathbin{\Vert} R_0
  \right)
\right)
```

Its dependence on `R_0` may provide close to full-width diversification across containers. For two
distinct containers using the same suite and settings, an idealized random-function calculation
allows pairwise equality of `S_0` to arise either from equal `R_0` values or from a hash collision
between unequal values. Using the preceding $`2^{-128}`$ heuristic for equal `R_0`, the combined
probability is $`2^{-128} + (1 - 2^{-128})2^{-128} = 2^{-127} - 2^{-256}`$, which is close to
$`2^{-127}`$ rather than exactly $`2^{-128}`$. Conditional on `L_0`, the source entropy remaining in
`R_0` is still only 0, 32, 64, 96 or 128 bits as shown above: the effect may reduce accidental salt
reuse, but it adds no entropy.

##### Source-length identification

An explicitly selected short source length checks only its corresponding `V_r`. Any explicit
source-length selection, including 24 words, removes auto-detection ambiguity. In the standard
workflow, a decoder can infer a short source length without stored metadata. After decrypting the
container to one 256-bit candidate `X_{candidate}`, it tests:

```text
12-word candidate:
    E = X_candidate[0:128]
    V = X_candidate[128:256]
    accept if V == Trunc128(SHA256(E))

15-word candidate:
    E = X_candidate[0:160]
    V = X_candidate[160:256]
    accept if V == Trunc96(SHA256(E))

18-word candidate:
    E = X_candidate[0:192]
    V = X_candidate[192:256]
    accept if V == Trunc64(SHA256(E))

21-word candidate:
    E = X_candidate[0:224]
    V = X_candidate[224:256]
    accept if V == Trunc32(SHA256(E))
```

If exactly one short relation passes, the decoder has a strong probabilistic indication of that
source length and recovers the corresponding `E`. If multiple relations pass, it must report an
ambiguous result. If none passes, it returns the complete 256-bit state as a 24-word source
candidate, but must label that fallback as unverified rather than as confirmation of the password.
The decoder must also permit an explicit 24-word override when a short relation passes.

Perfect self-description is impossible while the 24-word source mode covers all $`2^{256}`$
plaintext states. Every packed short state is also a possible 256-bit entropy value for some 24-word
source. Therefore failure of all short checks means only "no short profile was verified"; treating
the state as a 24-word source remains an unverified interpretation, not proof of a correct password.
For a uniformly distributed 256-bit candidate, including an independently generated 24-word source
under the model above, the individual accidental verifier-relation match rates are:

| Short relation tested |  Probability |                                    Approximate frequency |
| --------------------- | -----------: | -------------------------------------------------------: |
| 21 words              |  $`2^{-32}`$ |                                       1 in 4,294,967,296 |
| 18 words              |  $`2^{-64}`$ |                          1 in 18,446,744,073,709,551,616 |
| 15 words              |  $`2^{-96}`$ |              1 in 79,228,162,514,264,337,593,543,950,336 |
| 12 words              | $`2^{-128}`$ | 1 in 340,282,366,920,938,463,463,374,607,431,768,211,456 |

The probability that at least one short relation passes is bounded by:

```math
\begin{aligned}
2^{-32}
&\le \Pr[\text{at least one short relation passes}] \\
&\le 2^{-32} + 2^{-64} + 2^{-96} + 2^{-128}
\end{aligned}
```

The $`2^{-32}`$ term from the 21-word profile dominates, so the probability of at least one
accidental short-relation match is approximately $`2^{-32}`$, or about one in 4.29 billion. This is
strong probabilistic screening for accidental uniform candidates, not exact type information. A
deliberately constructed 24-word entropy can equal a valid packed short state with certainty. Under
the uniform-candidate heuristic, a wrong-password candidate reaches the unverified 24-word fallback
unless it produces one or more accidental short matches. This auto-detection bound also does not
replace the stronger selected-profile rate, such as $`2^{-128}`$ when the decoder explicitly checks
a 12-word source.

##### Final-word-preserving cycle walking for 24-word sources

An unreleased suite 2 draft defined and implemented the optional profile
`MHFE-BIP39-256-EXPERIMENTAL-2-CYCLE-WALK-FINAL-WORD`. It preserves the complete final word of a
24-word source while leaving the permutation unchanged. It is not part of suite 3; this subsection
describes the same construction over the suite 3 permutation, the research idea of Part I. Such a
profile would be separate from standard encryption and would have to be selected explicitly during
both creation and recovery. The 24-word container does not encode which profile was used.

Let $`\mathrm{FW}(E)`$ be the 11-bit index of the final BIP39 word obtained from 256-bit entropy
$`E`$: the final three entropy bits followed by the eight-bit BIP39 checksum. Let
$`\mathrm{Perm}_{P,\mathrm{MEM},\mathrm{PIM}}`$ be the suite 3 permutation. Creation applies the
permutation at least once and continues until the complete final-word index matches:

```text
target = FW(X)
Y = Perm_{P,MEM,PIM}(X)
while FW(Y) != target:
    Y = Perm_{P,MEM,PIM}(Y)
```

Recovery likewise applies the inverse at least once and continues until the candidate matches the
container's final-word index:

```text
target = FW(Y)
X_candidate = inverse(Perm_{P,MEM,PIM})(Y)
while FW(X_candidate) != target:
    X_candidate = inverse(Perm_{P,MEM,PIM})(X_candidate)
```

The first application is mandatory because the starting state already belongs to the selected class.
The result is the next distinct member of that class on the same permutation cycle, so no iteration
counter is stored. If the walk returns to its starting state before finding a distinct member,
creation or recovery must fail. Implementations should expose progress after each complete
permutation and should permit cancellation before the next permutation begins.

The encrypted container visibly reveals the source's final BIP39 word. This preserved word is not an
authentication tag or password verifier: a successful recovery under a wrong password returns a
different 24-word candidate with that same final word. The correct password and settings still
recover the exact source.

Under an ideal-permutation heuristic, a final-word class has density $`2^{-11}`$, giving a match
probability of approximately 1 in 2,048 per complete permutation. The iteration count is therefore
modeled geometrically, but this is an estimate rather than a strict latency bound. Using the
measured command-line recovery time of about 70 seconds per permutation under **Performance
measurements** only as an illustration:

|       Statistic | Complete permutations | Approximate sequential time |
| --------------: | --------------------: | --------------------------: |
|          Median |                 1,420 |                  27.6 hours |
|  Expected value |                 2,048 |                  39.8 hours |
| 95th percentile |                 6,134 |                 119.3 hours |
| 99th percentile |                 9,430 |                 183.4 hours |

There is no small deterministic bound. The distance to the next member of a class can be vastly
larger than 2,048, and the input- and password-dependent runtime creates availability and timing
side-channel concerns. Cancellation and progress reporting keep an application responsive but do not
reduce the cryptographic work.

###### Preserving the complete final word by excluding three bits

A 24-word BIP39 mnemonic's final word contains the last three source-entropy bits followed by the
eight-bit BIP39 checksum. A hypothetical new profile could preserve the three entropy bits unchanged
and apply a newly defined permutation only to the other 253 bits. Cycle walking would then need to
match only the eight-bit checksum. Under the same ideal-permutation heuristic, each iteration would
succeed with probability approximately $`1/256`$, so the expected work would fall from 2,048 to 256
applications of the new permutation while preserving the complete final word. Using the measured
command-line time of about 70 seconds per permutation under **Performance measurements** only as an
illustration gives:

```math
256 \cdot 70\ \mathrm{s} = 17{,}920\ \mathrm{s} \approx 4\ \mathrm{h}\ 59\ \mathrm{min}
```

This is not a shortcut that can be applied after the current 256-bit permutation. The BIP39 checksum
depends on all 256 entropy bits, including the final three, so changing those bits after a checksum
match generally invalidates the checksum. Restricting the existing 256-bit permutation to one fixed
three-bit suffix by an inner cycle walk would itself cost approximately eight permutation
applications and would restore the overall $`8 \cdot 256 = 2{,}048`$ expected-work factor. A direct
construction would instead require a new, separately analyzed 253-bit permutation, new domain
separation, new test vectors, and an explicit profile identifier.

The faster profile would deliberately disclose three bits of the source entropy, partition the
domain into preserved suffix classes, and replace the frozen balanced 256-bit construction with a
different geometry. No security reduction for that construction is provided here. The author does
not consider preserving a recognizable final word sufficient justification for sacrificing the
full-state confidentiality objective or changing the cryptographic construction in this way. This
direction is recorded for completeness and is not recommended for inclusion in any suite.

###### Known-pair composition across cycle-walking iterations

Cycle walking changes the known-pair problem from one exposed application of `Perm_{P,MEM,PIM}` into
a stopped iteration of the same permutation, parameterized by the password and the settings. Write:

```math
\begin{aligned}
W_0 &= X \\
W_j &= \mathrm{Perm}_{P,\mathrm{MEM},\mathrm{PIM}}(W_{j-1}) \\
\tau &= \min\{j \ge 1 : \mathrm{FW}(W_j) = \mathrm{FW}(W_0)\} \\
Y &= W_\tau
\end{aligned}
```

Under threat model T3, an attacker may know the cycle-walking endpoints `(X,Y)`. Except when
$`\tau = 1`$, those endpoints are not an adjacent pair $`(W_{j-1},W_j)`$ for one application of
`Perm_{P,MEM,PIM}`. Unless exposed through timing or instrumentation, the intermediate states and
`tau` remain hidden. The single-permutation Feistel shortcut described above therefore cannot simply
be applied independently `tau` times: each application would require an adjacent internal pair that
the attacker does not initially possess.

The opposite assumption is also unjustified. All iterations reuse the same `Perm_{P,MEM,PIM}`,
password, settings, and suite; they are not independently keyed layers. The stopping rule also
reveals a structured transcript condition:

```math
\begin{aligned}
\mathrm{FW}(W_j) &\ne \mathrm{FW}(X)
  \quad \text{for } 1 \le j < \tau \\
\mathrm{FW}(W_\tau) &= \mathrm{FW}(X)
\end{aligned}
```

A construction-specific analysis must determine whether a meet-in-the-middle computation, a Feistel
invariant spanning several applications, repeated state-derived salts, or the final-word
non-membership conditions can test a password while omitting expensive rounds in more than one
application. Any such saving must be analyzed jointly with the number of cycle-walking iterations;
neither multiplying the one-permutation shortcut by 2,048 nor charging 2,048 independent full
attacks is a justified cost model.

Timing can expose an additional filter even before such a shortcut is found. In the idealized
geometric model with final-word-match probability $`p_{\mathrm{match}} = \frac{1}{2048}`$, let the
observed correct stopping time be `tau` and the stopping time under an independent wrong-password
trajectory be `tau'`. If an exact iteration count can be associated with `Y`, this timing-only
filter does not require knowledge of `X`: an attacker can inverse-walk from `Y` under each password
guess and compare its first-return count with the observed value. For one concrete observation
$`\tau = t`$:

```math
\begin{aligned}
\Pr[\tau' = t]
  &= p_{\mathrm{match}}(1-p_{\mathrm{match}})^{t-1} \\
\mathbb{E}[\min(t, \tau')]
  &= \frac{1-(1-p_{\mathrm{match}})^t}{p_{\mathrm{match}}}
\end{aligned}
```

When both stopping times are independently sampled from that geometric model and the result is
averaged over the correct `tau`:

```math
\begin{aligned}
\Pr[\tau' = \tau]
  &= \frac{p_{\mathrm{match}}}{2-p_{\mathrm{match}}} = \frac{1}{4095} \\
\mathbb{E}[\min(\tau, \tau')]
  &= \frac{1}{1-(1-p_{\mathrm{match}})^2} \approx 1024.25
\end{aligned}
```

Thus an exact stopping-time observation would reject about 4,094 of 4,095 idealized wrong-password
trajectories by the stopping-time condition alone, while requiring approximately 1,024.25 complete
permutations on average to reach that decision. This does **not** mean that password entropy is
reduced by a fixed number of bits or that these idealized values carry over unchanged to MHFE. It
shows that variable runtime is part of the password-guessing model, not only a user-interface
problem. Timing-only, endpoint-only, endpoint-plus-stopping-time, leaked-intermediate-state, and
multiple known-pair cases require separate lower bounds on the unavoidable number of Argon2id
evaluations.

The resulting outer BIP39 mnemonic has the same complete final word as the source mnemonic. Its
11-bit index is exposed as a class label. It is not an independent verifier: every password defines
its own inverse permutation, and a successful inverse cycle walk under a wrong password returns a
candidate in the requested final-word class. The method therefore does **not** verify the password,
authenticate the recovered phrase, or contradict the information-capacity argument. It changes the
mathematical cycle-walk core into one permutation that preserves each of 2,048 final-word classes,
equivalently 2,048 restricted class permutations; no independence between those restrictions is
claimed. The operational rule above rejects fixed points of this induced permutation, so that
wrapper is a partial mapping on each full class, invertible on its accepted states. Separate
security and worst-case-runtime analysis is required.

The unreleased suite 2 draft implemented this application of cycle walking as an optional profile.
Black and Rogaway prove that cycle walking induces a uniform permutation on the target subset when
the underlying block cipher is ideal [35]; applying it to MHFE assumes that MHFE behaves like an
ideal permutation. That theorem applies to the mathematical core, which permits returning the
starting point, before the operational rejection rule is applied.

#### Direction A and Direction B: geometry comparison

Two research directions are retained:

- **Direction A — balanced Feistel, the geometry of suite 3.** Use $`128 \mid 128`$ bits for the
  256-bit container. The formulas of suite 3 describe this direction.
- **Direction B — source-heavy 1:3 Feistel, alternative candidate.** Update one quarter using the
  remaining three quarters, then rotate the state. $`32 \mid 96`$ bits describes a 128-bit state; a
  256-bit container requires $`64 \mid 192`$ bits instead.

The following table preserves the earlier comparison of hypothetical original-length states. It is
not the geometry of the universal 256-bit packing that suite 3 uses:

| Source words | Entropy state (bits) | Direction A split (bits) | Direction B split (bits) |
| -----------: | -------------------: | ------------------------ | ------------------------ |
|           12 |                  128 | 64 / 64                  | 32 / 96                  |
|           15 |                  160 | 80 / 80                  | 40 / 120                 |
|           18 |                  192 | 96 / 96                  | 48 / 144                 |
|           21 |                  224 | 112 / 112                | 56 / 168                 |
|           24 |                  256 | 128 / 128                | 64 / 192                 |

For a universal 256-bit outer payload, every source length instead uses $`128 \mid 128`$ bits in
Direction A or $`64 \mid 192`$ bits in Direction B. Input entropy and permutation state size are
different quantities. Packing a short source together with deterministic verifier redundancy into a
longer state does not create additional source entropy.

##### Evidence and trade-offs

Hoang and Rogaway analyze their unbalanced $`Feistel^r[m,n]`$ construction using independently and
uniformly random round functions [36]. Figure 4 explicitly compares proven CCA-security bounds on a
128-bit string for $`Feistel^r[32,96]`$ (bold curves) and balanced $`Feistel^r[64,64]`$ (dashed
curves), at 18, 36, 72, and 144 rounds. Their Appendix E comparison, particularly Figure 6 and its
surrounding discussion, states that imbalance improves the bounds when enough rounds are available,
while the balanced construction has the stronger bound when rounds are scarce. Their round counts
apply to that paper's idealized construction.

- **State updated by one round:** Direction A updates one half; Direction B updates one quarter.
- **Rounds until each original chunk has been targeted once:** Direction A requires 2; Direction B
  requires 4.
- **State supplied to a round function at fixed total width:** Direction A supplies one half;
  Direction B supplies three quarters.
- **Main 256-bit suite and round-mask input:** Direction A uses the 128-bit right half as the
  specified HMAC message suffix. Direction B's 192-bit source requires a different round-function
  definition.
- **Potential benefit:** Direction A fits the baseline more simply and needs fewer updates per
  traversal. Direction B offers a larger source branch and favorable idealized multi-query bounds
  when enough rounds are available.
- **Main cost concern:** Direction A still lacks a justified secure round count and an MHFE-specific
  proof. Direction B needs more expensive updates per traversal, and KDF cost may dominate its
  theoretical benefit.

Targeting each chunk once is not a security criterion. Comparisons must use equal measured latency
and peak memory, not merely the same number of rounds. Increasing the number of sequential Argon2id
calls increases work; it does not automatically multiply peak memory by the same factor. Reducing
each call's parameters to meet a time budget changes attack cost.

With the current 128-bit salt truncation, the following are upper bounds on the source width
retained as distinct salt values, not measured entropy or security levels:

| Total state (bits) | A: source width (bits) | B: source width (bits) | A: source/salt-width cap (bits) | B: source/salt-width cap (bits) |
| -----------------: | ---------------------: | ---------------------: | ------------------------------: | ------------------------------: |
|                128 |                     64 |                     96 |                              64 |                              96 |
|                192 |                     96 |                    144 |                              96 |                             128 |
|                256 |                    128 |                    192 |                             128 |                             128 |

Hash collisions, structured plaintext, and knowledge available to the attacker matter in addition to
these widths. A 128-bit salt cap is not automatically a 128-bit security bound on the entire cipher:
the effective round function also processes the state.

For an original-length 12-word experiment, the larger source branch makes Direction B particularly
interesting. For 18 words, its benefit must be assessed alongside the salt truncation and the
changed round function. For the universal 256-bit container, Direction A already has a 128-bit
source branch, so Direction B needs a concrete demonstrated advantage to justify its additional
complexity. These are research priorities, not security findings.

##### Known-pair filtering cost

Write one Direction B round on four equal chunks as:

```math
\begin{aligned}
(A, B, C, D) \to (B, C, D, A \oplus G_i(B \mathbin{\Vert} C \mathbin{\Vert} D))
\end{aligned}
```

Across three consecutive rounds, the initial `D` becomes the first output chunk without
modification. Given a known plaintext/ciphertext pair, an attacker can evaluate the rounds outside a
three-round gap and test that equality without evaluating the gap. In an adaptation with one KDF
evaluation per round, a four-round design therefore allows an initial filter using only one KDF
call. Equivalently, the first output chunk after four rounds is
$`A \oplus G_0(B \mathbin{\Vert} C \mathbin{\Vert} D)`$.

In an idealized random-function model the four-round filter has a false-acceptance rate of
$`2^{-w}`$, where `w` is the chunk width: 32, 48, or 64 bits for states of 128, 192, or 256 bits.
Surviving guesses require further checks. For balanced Feistel, a related known-pair filter can omit
one round; Part I describes this filter; whether a more efficient one exists is an open question.

Direction B therefore requires a separate round count, round-function definition, and
password-attack analysis. Larger KDF input alone is insufficient justification for choosing it.

### Reference Implementation

The reference implementation is maintained in the public
[`hobby-eng/mhfe`](https://github.com/hobby-eng/mhfe) repository, and the specification's
[Reference Implementation](../README.md#reference-implementation) section describes it and names the
revision that generated and independently verified the suite 3 vectors. Version 0.4.0 implements
only suite 3. Its Rust library, command-line tool and WebAssembly build use the reference C
implementation of Argon2 as their single Argon2 engine; browsers get two builds of that code, one
with threads for cross-origin isolated pages and one without threads for all other pages. Version
0.3.0 of the implementation remains available for suite 2.

The library, the command-line tool and the browser API detect the source length automatically after
one inverse permutation: they return a unique short-source match, fall back to an unverified 24-word
reading when none matches, and report every matching length when detection is ambiguous. An explicit
source length remains available as an override. Creation refuses a container equal to its source.
When the implementation finds too little free memory, or the operating system refuses to reserve the
Argon2 memory, it stops with a typed error, `NOT_ENOUGH_MEMORY` or `MEMORY_ALLOCATION_FAILED`,
instead of reducing the memory; the operating system or the browser can still end the process during
the work. The operational result exposes only the recovered phrase, its word count and whether it
passed a verifier; source entropy, packed states, Argon2 outputs, masks and round traces appear only
in the separate vector code, which works only on the fixed public test inputs. Buffers that the
implementation owns and that hold passwords, phrases, entropy and round material are zeroized when
they are dropped or reused, and the C code wipes the Argon2 work area at the end of every round.
Short-lived working buffers inside dependencies are not wiped, and in the browser a failed Argon2
round leaves its work area to be discarded with its worker; the implementation's
[security notes](https://github.com/hobby-eng/mhfe/blob/main/SECURITY.md) list these limits. This is
a memory-hygiene measure rather than a guarantee that compilers, allocators, browser strings,
operating systems or earlier reallocations leave no residual copies.

The implementation is not independently reviewed by a cryptography specialist, and it is not
independent evidence for its own vectors. The independent evidence is the OpenSSL-based verifier
recorded with the [suite 3 corpus](../vectors/suite3/), which replays every transcript in both
directions and every recovery case through its recovery. A toy reduced-width model must not be used
as evidence of production security.

#### Performance measurements

The following whole-operation timings at the default settings were measured on the author's laptop
(Intel Core i7-1260P), each from start to end: on the command line with the release builds of commit
`92d62e5`, and in the browser with the MHFE 0.4.0 browser package, driven in headless Chromium
through the MHFE panel of the Wallet Key Derivation Tool. The
[measurement record](https://github.com/hobby-eng/mhfe/blob/883373c5833ca6aefc88345caa3a18cbbfcf0f5c/measurements/README.md)
published in commit `883373c`, keeps the details:

| Environment                                                 |        Recovery | Encryption with its check |
| ----------------------------------------------------------- | --------------: | ------------------------: |
| Command line                                                |      67 to 72 s |          2 to 2.3 minutes |
| Browser, fast mode (served, cross-origin isolated, threads) |      90 to 95 s |        2.7 to 2.8 minutes |
| Browser, standard mode (page opened as a file, one thread)  | about 4 minutes |    about 7.7 to 8 minutes |

On the command line, the build with SSSE3 was 7 to 10 percent faster than the default build. One
Argon2id call at 2 GiB and 12 passes took 4.6 to 5.0 seconds natively with four threads, 5.7 seconds
in the browser's fast mode and about 19 seconds in its single-threaded standard mode.

These are observations on one computer, not a normative performance target, a minimum attacker cost
or a guarantee for similar machines. CPU power policy, thermal state, memory bandwidth, compiler,
Argon2 implementation, native versus WebAssembly execution and concurrent load can change the result
materially, and broader measurements on representative x86-64 and ARM64 systems would be needed
before these figures could support a portability or deployment claim.

### Test Vectors

The suite 3 corpus is published in [`vectors/suite3/`](../vectors/suite3/): 17 positive transcripts,
six recovery cases and 54 fast validation cases. The reference implementation generated them, and an
independent OpenSSL-based verifier replayed every transcript at full cost in both directions and
every recovery case through its recovery. Each transcript records the source mnemonic and entropy,
the normalized password bytes, the packed state, every round's salt and mask input messages, salt,
Argon2id output, mask and state, the container and the recovered result. The corpus notes record
provenance and checks, and the specification's [Test Vectors](../README.md#test-vectors) section
states the requirements. The suite 2 vectors remain at their published paths in
[`vectors/`](../vectors/) and must not be replayed under suite 3.

Following BIP 3's recommendation that test vectors be available under CC0-1.0 or FSFAP in addition
to any other license, the vectors are released under CC0-1.0 so that implementations can copy them
without license friction [7].

### Known Limitations

This section records the present boundaries of the experimental suite. It is not a roadmap and does
not commit the author to further research or implementation work.

- The selected Argon2id and Feistel parameters are supported by limited measurements on the author's
  laptop.
- Short-source recovery verifiers intentionally provide an offline password-checking signal, while
  the 24-word source mode has no internal wrong-password test and automatic source-length detection
  remains probabilistic. The reference APIs implement automatic detection and retain explicit source
  length as an override.
- Password-guessing lower bounds, multi-container behavior, structured short-source domains, and
  state-derived-salt assumptions remain unresolved analytical questions.
- Final-word-preserving cycle walking is not part of suite 3. It was implemented as an optional
  24-word profile of an unreleased suite 2 draft and is analysed here as research; its variable
  runtime and public final-word class would require separate analysis. The 253-bit shortcut and
  source-heavy unbalanced Feistel remain non-normative research alternatives and are not part of the
  reference implementation.

The implemented utility may be used for public experiments and interoperability testing under the
warnings in this document. Nothing in this section should be read as a promise of a future version
or as a claim that the current construction is suitable for protecting real funds.

## References

Citation numbers refer to the single reference list of the specification,
[`README.md`](../README.md#references).
