# MHFE Design Notes and Analysis

This is a supplement to the MHFE specification in [`README.md`](../README.md). It is not normative
and does not define the format: it explains in more detail why MHFE is built the way it is and what
is known about its security. The specification's [Rationale](../README.md#rationale) explains the
design decisions; this supplement develops their analysis.

Part I is analysis written for suite 3, and a section after it examines what the narrower state of
the length-preserving suite 4 changes. Part II is the detailed design discussion, first written for
suite 2 and since brought up to date; it describes suite 3. `README.md` defines suites 3 and 4;
where the documents differ, `README.md` takes precedence. Words such as "must" and "should" in this
supplement describe the design; the requirements themselves are those of the specification. The text
of suite 2 as released is kept, marked as historical, in the [archive](archive/README.md); only its
links to `mhfe` commits were updated.

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
- [Suite 4: what the narrower state changes](#suite-4-what-the-narrower-state-changes)
- [Part II. Detailed design discussion](#part-ii-detailed-design-discussion)
  - [Motivation](#motivation)
  - [Notes on the construction](#notes-on-the-construction)
  - [Rationale](#rationale)
  - [Backward Compatibility](#backward-compatibility)
  - [Security Considerations](#security-considerations)
  - [Related Work and Alternatives](#related-work-and-alternatives)
  - [Theoretical Investigation and Alternative Designs](#theoretical-investigation-and-alternative-designs)
  - [Reference Implementation](#reference-implementation)
  - [Test Vectors](#test-vectors)
  - [Known Limitations](#known-limitations)
- [Research directions](#research-directions)
  - [Container check words: a hash of the container (planned)](#container-check-words-a-hash-of-the-container-planned)
  - [Argon2i on the rounds with a public salt](#argon2i-on-the-rounds-with-a-public-salt)
  - [A second memory-hard function](#a-second-memory-hard-function)
  - [A hidden wallet behind an honest disclosure](#a-hidden-wallet-behind-an-honest-disclosure)
  - [Check words for derived wallets in the current suites](#check-words-for-derived-wallets-in-the-current-suites)
  - [Derived wallets of a chosen length](#derived-wallets-of-a-chosen-length)
  - [Nested containers](#nested-containers)
  - [A check for new 24-word and suite 4 sources by choosing the entropy](#a-check-for-new-24-word-and-suite-4-sources-by-choosing-the-entropy)
  - [A private check word for generated passwords](#a-private-check-word-for-generated-passwords)
  - [Alternative formats for multiple password openings with recovery checks](#alternative-formats-for-multiple-password-openings-with-recovery-checks)

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
can read. Containers of independently generated sources therefore have different salt chains except
when branch values repeat or salts collide; these exceptions are negligible under the model below.
An attacker cannot ordinarily reuse a password's KDF work across such containers. In this
construction the unchanged half is what lets decryption recompute a different salt for every round.
SLIP-0039 uses the same idea with PBKDF2 [19].

Other structures considered here also offer a value that one round leaves unchanged, but none is
simpler:

- An unbalanced Feistel network, called Direction B in Part II, splits the state unevenly. Its
  published idealized bounds [21] favor the imbalance only when enough rounds are available; with
  few rounds the balanced network has the stronger bound, and every extra round costs an Argon2id
  call.
- The Lai-Massey scheme [22] keeps the XOR of its two halves unchanged within a round, so the salt
  could be derived from that value. Without a mixing step between rounds, the same value would
  survive every round and pass the XOR of the source halves straight into the container. The scheme
  therefore needs such a step; Vaudenay proves security with an orthomorphism or an almost
  orthomorphism [23], which adds complexity and is less studied in this setting.
- The swap-or-not shuffle [24] has a round invariant too, but it decides one swap per round, and its
  published bounds call for hundreds of rounds or more, depending on the domain and the security
  target. These bounds are sufficient rather than proven minimums, but with one Argon2id call per
  round they would make a recovery many times slower.

A Feistel network needs few rounds, has a well-studied theory, and keeps the construction easy to
implement and check.

### Security model

The main threat is simple: someone obtains the 24-word container, for example by finding or
photographing a metal backup, and tries to recover the original seed phrase by guessing the password
offline. Part I analyses this threat first; others, some of them serious in practice, such as a
substituted container phrase or leaked intermediate values, are covered by threat models T1 to T15
in Part II.

The attacker is assumed to know the suite, the MHFE format and, unless the owner keeps them secret,
the PIM and the memory level. The attacker may also be able to check a candidate mnemonic against
the blockchain, because a wallet with funds or history reveals itself. Rarer situations, such as
knowing an original seed phrase together with its container (a "known pair"), are treated separately
below.

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
first half of its first pass; the rest are data-dependent [4]. This hybrid design does not prove
that an MHFE implementation resists timing or cache observation. Platform-specific analysis and
careful handling of intermediate states remain necessary even on an offline computer.

### Ciphertext-only guessing

What counts as a password test depends on the source. Ordinary recovery performs twelve Argon2id
evaluations. For a short source, the recovered candidate can be screened by its verifier. For a
24-word source, recovery alone cannot confirm a password; confirmation requires external
information, such as a known address, and needs the full recovered mnemonic. A phrase created with
the optional source check `MHFE-WALLET-CHECK-SEED-1` adds a 16-bit filter, evaluated on every
24-word reading as
[the source check](#a-check-for-new-24-word-and-suite-4-sources-by-choosing-the-entropy) explains.
With the empty BIP39 passphrase it screens MHFE password guesses alone; a wrong guess still passes
in about one case in 65,536. This check also needs the full recovered mnemonic.

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
the next salt can be hit only by guessing 128 bits. In suite 4 the halves have `h = ENT/2` bits, 64
for a 12-word source; each such guess still needs an Argon2id evaluation of its own, so it gives no
shortcut. The ordinary inverse therefore evaluates the rounds in order, from round 11 down to round
0; this does not rule out other attack strategies.

After the eleven evaluations for rounds 11 down to 1, the right half `R_0 = L_1` of the packed state
is known; only the left half `L_0` is still masked by `M_0`. The usual verifier and blockchain
checks need all of `E`, including `L_0`. For a 12-word source `R_0` is `Trunc_128(SHA-256(E))`:
exhaustive enumeration of the `2^128` possible values of `E` could test whether that hash output has
a preimage, rejecting some wrong passwords without the twelfth Argon2id call. A model with free
hashes does not charge for this impractical search. For 15 to 21 words `R_0` holds the tail of `E`
and a verifier over all of `E`; for 24 words it is simply the second half of `E`, independent of the
first. These observations neither exclude other early filters nor prove a `2^128` work requirement.
A proof needs an explicit budget for both hash computations and Argon2id evaluations.

**Many containers.** The salt of the last round comes from the container's own left half. In the
described direct guessing procedure, an Argon2id result for one password and salt is reused for
another container only when its password candidate and salt match. Containers with the same left
half, or salts that collide after truncation to 128 bits, can share that evaluation. For suite 3
containers of independently generated sources under the stated model, accidental salt collisions are
expected to be negligible; uniqueness is probabilistic, not guaranteed. This avoids the direct reuse
of one fixed-salt password table across all containers, but does not prove that every
multi-container attack requires separate work. Suite 4's narrower salt diversity is discussed in
[its analysis](#suite-4-what-the-narrower-state-changes). If several containers use the same
password, finding it opens all of them; that is inherent to any password scheme.

**Blockchain checks.** A 24-word source has no internal verifier, but a funded wallet does: the
attacker can derive addresses from each candidate and look them up. This check needs the full
candidate mnemonic, so in the ordinary inverse it comes after all twelve evaluations. It means that
"no verifier" does not by itself stop a guesser when the wallet has no BIP39 passphrase (see
[Composition](#composition-with-the-bip39-passphrase)).

### Known pairs

A known pair is an original seed phrase together with its container, for example after the seed
phrase leaked through another channel. With a known pair the attacker can test a password guess by
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

The PBKDF2 rate is a rounded extrapolation from the published RTX 4090 Hashcat 6.2.6 benchmark [7]:
about 3.12 million PBKDF2-HMAC-SHA512 candidates per second at about 1,000 iterations scales to
about 1.52 million at 2,048 if time scales linearly. This is a generic primitive benchmark: its
candidate varies the PBKDF2 password, whereas a BIP39 passphrase varies the salt while the mnemonic
is fixed. Kernel optimizations, input lengths and preprocessing can therefore differ. The two rates
are model inputs, not measurements of a complete MHFE-versus-BIP39 wallet attack on one card.

Word-based passwords in the table use independent uniform choices from the EFF list of 7,776 words
[6]. Two words illustrate a weak password, not a recommendation. The 30- and 40-bit rows describe
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
([measurement record](https://github.com/hobby-eng/mhfe/blob/b1d83504ba2458681111c14cade52fa0a178ddb4/measurements/README.md)).

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
applied one after the other: recovery restores the original seed phrase, and the passphrase is then
used as before. The estimates below assume a known source length, independent uniformly chosen
secrets (`N1` MHFE passwords costing `C1` each; `N2` passphrases costing `C2` each), and no separate
check that identifies the original seed phrase. They describe sequential searches, not lower bounds.

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
| 24 words | about `2^30` MHFE passwords, each with a search over passphrases |             ~12,200 years |

Without a passphrase, a 24-word source offers no such gain: wallet history provides an external
check of a candidate recovered with an MHFE password. A short source instead supplies an internal
verifier, with the false-match probability described above.

This is a choice for the user rather than a weakness of either option. A short source gives a
recovery that reports whether a candidate passes its verifier, automatic length detection and simple
password rehearsal. A 24-word source with an independent passphrase gives the strongest combination
of the two secrets. The specification's Rationale section presents this choice.

### Deniability

A person who is forced to disclose a password can disclose a different one, prepared in advance.
This section states precisely what such a decoy disclosure achieves and proves it. The notion is
modeled on receiver-deniable encryption in the sense of Canetti, Dwork, Naor and Ostrovsky [44]: an
honest disclosure and a prepared one are compared in two experiments, and the adversary must tell
them apart from the information it has. It is narrower than their definition, in which a faking
algorithm can make a ciphertext look like an encryption of any chosen alternative message: here the
owner chooses a decoy password, and the decoy phrase is whatever that password recovers. The proofs
hold for one container and one disclosure in the model below. Unlike the arguments above, they are
proofs within that model, but they have not been reviewed by an independent cryptographer.

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
are an abstraction: a transfer between two wallets links their records. In these experiments `U` is
an abstract generator of records, using only the supplied phrase and independent randomness; it does
not query the cryptographic random oracles or receive the hidden password or round keys. It models
public wallet use, not the cryptographic computations that produce real transactions. An extension
in which generating records makes such queries must account for them separately before claiming the
bounds below.

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

The raw source entropy is sampled freshly and uniformly, independently of the shared oracle tables,
the passwords and the adversary's prior information. The password distribution is fixed
independently of those tables, and the initial draws of `P` and `Q` are independent; the stated
rejection rules are applied afterward. For short sources this assumption concerns `E` before
packing, not the packed state `X`, whose verifier is computed using SHA-256. Marginal uniformity
alone is not enough: entropy computed from a public oracle answer can be uniform while already known
to the adversary.

- **Honest disclosure.** A 24-word phrase with uniformly random entropy `X` is created and a
  password `P` is drawn. The container is `Y = E_P(X)`. The wallet of `X` is used according to `U`.
  The adversary receives `Y`, `P` and the record `U(X)`.
- **Prepared disclosure.** The owner's real source, with packed state `X`, and a password `P` give
  `Y = E_P(X)`. A decoy password `Q` is drawn from the same distribution and drawn again while it
  equals `P`, and `X' = D_Q(Y)`. The disclosed phrase is `X'` read as 24 words, and its wallet is
  used according to the same `U`; the real wallet, that of the owner's original seed phrase, is used
  in any way. The adversary receives `Y`, `Q` and the record `U(X')`.

The adversary knows the construction and how decoys are prepared, may query the random oracles of
the [Security model](#security-model) adaptively, and may look up the record of any phrase. Let `k`
be the number of distinct passwords with which it queries Argon2id, `q` the number of its
HMAC-SHA-256 queries and `l` the number of its lookups. Every computation of the experiment itself,
when it calls a cryptographic primitive, uses the same oracles; `U` makes no such calls, and the
twelve HMAC calls of the decoy recovery `D_Q(Y)` are counted separately in the proof. The adversary
outputs a guess of the experiment; its advantage is the difference between the probabilities that it
answers "prepared" in the two experiments. The condition that both disclosed wallets follow the same
scenario `U` is essential: a decoy created a minute ago cannot pass for a wallet with years of
history.

**Theorem 1 (24-word source, exact).** Let the real source have 24 words and uniformly random
entropy, with the independence and password-sampling conditions of the experiments, and ignore the
refusal of fixed points and the redrawing of `Q`. Then the random oracles, the container, the
disclosed password, the disclosed phrase and its wallet's record have exactly the same joint
distribution in both experiments.

**Proof.** In the prepared experiment `X` is uniform and independent of `P`, of `Q` and of the
oracles, so by Lemma 2 `Y = E_P(X)` is uniform and independent of all of them. For each value of `Q`
and of the oracles, Lemma 2 applied to `D_Q` shows that `X' = D_Q(Y)` is uniform, and `Y = E_Q(X')`
by Lemma 1. So the oracles together with `(Y, Q, X')` have the distribution of the oracles together
with `(E_P(X), P, X)` in the honest experiment, and the records `U(X')` and `U(X)` follow, since the
scenario is the same. The argument holds for any fixed functions in place of the oracles.

What Theorem 1 leaves open is the real wallet: a lookup of `X` shows its record in the prepared
experiment only. Theorem 2 bounds the effect of that and of everything else.

**Theorem 2 (bound, every source length).** Let the real source have 12 to 24 words and uniformly
random entropy `E` of `ENT` bits, with the independence and password-sampling conditions of the
experiments. For a source shorter than 24 words, let the adversary have no information about the
source length beyond what the experiment gives it. In the random-oracle model the advantage is at
most

`(k + 2) * p_1 + l * 2^-ENT + (12 * q + 146) * 2^-256`.

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
decoy recovery, so the `q` HMAC queries of the adversary and the twelve of the decoy recovery hit
one of them with probability at most `12 * (q + 12) * 2^-256`. The real phrase is determined by `E`,
so each lookup hits it with probability at most `2^-ENT`. Adding the steps gives the bound: `p_1`
and `2^-256` for Game 1, `(k + 1) * p_1 + 12 * (q + 12) * 2^-256 + l * 2^-ENT` for Game 2 and
`2^-256` for Game 3.

**Remark on cost.** An ordinary search computes `D_p(Y)` for candidate passwords `p`, twelve
Argon2id evaluations each, and looks up the results. Theorem 2 bounds the probability of success by
the number of passwords tried and lookups made; it does not show that this search is the cheapest
way to try a password (see Conjecture 1).

**Corollary (simulating a prepared disclosure with a programmable record oracle).** In the synthetic
experiments above, a simulator receives the container and access to the same cryptographic functions
and real-wallet record oracle as an adversary without a disclosure. This base record oracle returns
the real wallet's record for its phrase and an empty record for every other phrase. The simulator
need not know the real phrase or its password. It draws a password from the distribution and
recovers the container with it, which costs twelve Argon2id evaluations, then samples a record for
the recovered phrase from `U`. For subsequent lookups it wraps the base oracle: the recovered phrase
returns this sampled record, while every other lookup is forwarded unchanged to the base oracle. In
particular, the real wallet's record remains available when its phrase differs from the disclosed
one.

This produces the prepared experiment's disclosure and subsequent oracle answers, except that the
drawn password is not rejected when it equals `P`, an event of probability at most `p_1`. An
adversary's success probability therefore differs by at most `p_1`. The simulation applies to every
source length and needs no idealized cryptographic function. It requires fresh, programmable
synthetic records at the time of disclosure and the stated access to the real-wallet oracle; it does
not construct that oracle from the container. It does not simulate disclosure against a fixed public
ledger or change answers to queries made before disclosure. The bounds of Theorems 1 and 2 stand on
their own. The real wallet's protection still rests on the password and on MHFE.

The owner must not select the decoy password by the phrase it produces. For example, a decoy phrase
that also passes a 21-word verifier, which happens with probability about `2^-32`, must be kept,
because an honest 24-word phrase can do the same. The same holds for the 16-bit check of
`MHFE-WALLET-CHECK-SEED-1`: a decoy phrase that passes it, with probability about `2^-16`, must be
kept too.

**Honey encryption.** For a 24-word source the construction has the structure of honey encryption in
the sense of Juels and Ristenpart [43], with a uniform message model and the identity as its
encoder: every password recovers an equally likely phrase, so only external information, above all
the use of the real wallet, identifies the right one. Whether MHFE meets the formal security
definition of honey encryption is not claimed; that also depends on what external information is
available. Part II's remark that MHFE has no such model refers to wallet entropy in general. A short
source is different: its verifier deliberately rejects wrong passwords, which is why Theorem 2 needs
an adversary who does not know the source length.

#### Suite 4: the same analysis at every length

The experiments, Lemmas 1 to 3 and the proofs apply to the length-preserving suite 4 with `ENT`-bit
states in place of 256-bit ones. Every `ENT`-bit state is valid entropy for a phrase of the source's
length, so Lemma 1 holds at every length, and Lemmas 2 and 3 do not depend on the width. Both
disclosures read the container at the source's own length, so the honestly disclosed phrase has that
length instead of 24 words. With these changes:

- **Theorem 1 for suite 4 (exact, every length).** For a suite 4 source of 12, 15, 18 or 21 words
  with uniformly random entropy and the independence and password-sampling conditions of the
  experiments, and ignoring the refusal of fixed points and the redrawing of `Q`, the random
  oracles, the container, the disclosed password, the disclosed phrase and its wallet's record have
  exactly the same joint distribution in both experiments. The proof is that of Theorem 1.
- **Theorem 2 for suite 4.** Under the same source and password-sampling conditions, in the
  random-oracle model the advantage is at most
  `(k + 2) * p_1 + (l + 2) * 2^-ENT + 12 * (q + 12) * 2^-256`. The proof is that of Theorem 2. The
  two fixed-point terms become `2^-ENT`, because the permutation acts on `ENT` bits, while the keys
  `K_i` remain 256-bit Argon2id outputs. The condition on the source length is not needed: the
  container shows the length in both experiments alike.

For a 12-word source the fixed-point term and each lookup term are `2^-128`, a small absolute
probability; how they compare with `p_1` depends on the password distribution, and the full bound
above applies. Both theorems need freshly uniform source entropy independent of the oracle tables,
passwords and adversary's prior information; a phrase generated with chosen words or known public
oracle answers, for example, is not covered. Like a 24-word suite 3 source, a suite 4 source has the
structure of honey encryption with a uniform message model at every length. As for suite 3, these
results hold for one container and one disclosure in the stated model; they do not cover related
containers of both suites for one phrase (see
[Suite 4: what the narrower state changes](#suite-4-what-the-narrower-state-changes)), and they have
not been independently reviewed.

**Limits of the guarantee.**

- In suite 3, both theorems compare a prepared disclosure with an honest owner of a 24-word source,
  and in suite 4 with an honest owner of a phrase of the same length. An adversary who knows that
  the original seed phrase of a suite 3 container has fewer than 24 words, for example from the
  device or software that created it, sees that a 24-word reading cannot be the original seed
  phrase.
- The decoy password must be drawn like a real one. A noticeably weaker or differently formed
  password is evidence outside the experiments.
- The decoy wallet must follow the same usage scenario as an honest wallet. Its phrase cannot be
  chosen, so it is a new wallet, and its use has to begin as early and look as ordinary as an honest
  owner's would. A transfer between the real and the decoy wallet links their records.
- The bounds include the probability of guessing the real password, but not of learning it in
  another way. If it leaks, the decoy does not help.
- A phrase created with the source check `MHFE-WALLET-CHECK-SEED-1` is not uniformly random, and the
  theorems do not automatically cover it. Every 24-word reading is checked against it. A decoy
  phrase passes it only in about one case in 65,536, so an adversary who knows that the owner used
  the check sees the difference.
  [The analysis of that check](#a-check-for-new-24-word-and-suite-4-sources-by-choosing-the-entropy)
  discusses decoys for such phrases.
- Several containers of one phrase, two different passwords named for one container, a BIP39
  passphrase and side channels are not covered. The paragraphs below discuss the first two.
- Cryptography cannot promise that a particular person will believe a disclosure; the theorems only
  bound what the adversary can learn from the information in the experiments. Where the two
  disclosures have exactly the same distribution, as in Theorem 1, a disclosure leaves the
  adversary's belief that a decoy is in use where it was before. It removes evidence of deception,
  but whether the adversary stops depends on what it expects to gain and what continuing costs it,
  not on the cryptography. The bound of Theorem 2 limits the average advantage, not the change of
  belief after every rare observation.

**Repeated disclosures and wallet checks.** The theorems cover one disclosure. Naming the same decoy
password again adds no cryptographic information: an honest owner repeats the real password, and the
second answer equals the first. The same holds for answers computed only from the disclosed phrase
and a public challenge, such as an address or an extended public key at a given derivation path, or
a message signed with a key of the disclosed wallet. A decoy phrase is a genuine BIP39 phrase whose
keys the owner controls, and the adversary, who can recover the phrase from the container and the
disclosed password, could compute such answers itself, so they cannot increase its advantage; where
the computation calls a function whose queries the bounds count, for example HMAC-SHA-256 when a
signature nonce is derived with it, those calls count among its queries. A challenge tied to a known
address of the real wallet, such as a request to sign with it, is different: the decoy wallet cannot
answer it, and knowing that address, like any other external record, is evidence outside the model.
What can add information is what changes between demands: the decoy wallet's later history, unless
it continues as an honest wallet's would, and evidence that appears in the meantime. Naming two
different passwords for one container, both opening funded wallets, falls outside the model of an
honest owner with one password per container. That does not make several decoys for one container
useless in every situation, for example when different adversaries are involved, but the present
analysis says nothing about it.

**Several containers of one phrase.** Copies of one container made with the same password and
settings are identical, so one decoy password opens all of them in the same way, and the copies give
no new cryptographic distinguisher, although each copy is another place where it can be found. Two
containers `Y_1` and `Y_2` of one phrase made with different passwords or settings behave
differently. An honest disclosure opens both to the same wallet, but decoy passwords `Q_1` and `Q_2`
normally open them to two different phrases. For two containers of the same suite and word count,
let `b` be the state width: 256 bits for suite 3 and `ENT` bits for suite 4. If each fresh password
trial gives an independent uniform candidate state, the probability of hitting a fixed decoy phrase
after `t` distinct normalized password trials is `1 - (1 - 2^-b)^t`, approximately `t * 2^-b` when
`t` is much smaller than `2^b`. Thus the scale is `t * 2^-256` for suite 3 and, for example,
`t * 2^-128` for a 12-word suite 4 container. This is a heuristic under the stated independence
assumption, not a proven bound for related MHFE containers. An adversary who knows that the
containers hold one phrase then sees two wallets where an honest owner shows one. Theorems 1 and 2
concern a single container and do not cover this case: they do not compose for containers whose
sources are related. Where deniability matters, further copies of a backup should therefore be made
by copying one verified container word for word, with the same password and settings, not by
encrypting the phrase again. This also avoids copies that are only as strong as the weaker of two
passwords or the cheaper of two settings.

**Evidence outside the model.** The theorems bound only what the experiments show. The hidden
volumes of a deniable file system were exposed by traces that the operating system and applications
left, not by their encryption [48], and other records can likewise expose a decoy:

- an unencrypted record of the phrase, such as a paper copy, or a hardware wallet that the owner can
  be made to unlock, once the adversary finds it and links it to the container, which is immediate
  if it is kept next to the container phrase;
- extended public keys, output descriptors, saved addresses or watch-only wallets that identify the
  real wallet;
- notes, photographs, password-manager entries or labels about the backup, including a note that
  marks a password as a decoy;
- exchange, tax and payment records that link the real wallet to the owner.

Deniability therefore requires every record that the adversary can obtain and link to the container
to be consistent with the disclosure, a limit that is not specific to MHFE. Blockchain analysis of
the two wallets is likewise outside the cryptographic guarantee.

### Parameter rationale

**Cold storage.** MHFE is meant for long-term offline backups that are created once and recovered
rarely. Waiting a couple of minutes for such an operation is acceptable, while the attacker repeats
the work for each password guess, at a speed that depends on the hardware. The parameters are chosen
for that use and not for everyday unlocking.

**Memory and passes follow RFC 9106.** The first option that RFC 9106 recommends is Argon2id with 2
GiB of memory, four lanes and one pass [4]. Its general procedure is to choose the largest amount of
memory the application can afford and then to increase the number of passes until the available time
is used. MHFE applies that procedure: 2 GiB and four lanes as recommended, and twelve passes because
a cold-storage operation can afford several seconds per round. The twelve passes are this project's
choice under that procedure, not a value the RFC prescribes. On the author's mid-range laptop from
2022 (Intel Core i7-1260P, 16 GB) one such call took about 4.6 to 5.0 seconds with the reference C
code and about 10 seconds with OpenSSL, using four threads (see
[Performance measurements](#performance-measurements)), so a recovery takes about one to two minutes
and a creation, which ends with a full recovery as its check, about twice as long. Newer computers
are faster and commonly have far more memory.

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
as a known address. For a phrase created with `MHFE-WALLET-CHECK-SEED-1`, every 24-word reading also
gets its 16-bit check, which a wrong setting passes in about one case in 65,536. A strong password
remains the better investment; a secret setting is an optional extra with its own risk of being
forgotten.

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

This idea is not part of suite 3; it is recorded because it answers a real wish. The container would
end with the same word as the original 24-word seed phrase, so that an owner who remembers the last
word of each wallet could tell which container phrase belongs to which wallet: an 11-bit check of
the container phrase, not of the password. It would work by cycle walking, applying the permutation
again and again until the last word matches, during creation and, in the inverse direction, during
recovery. An unreleased suite 2 draft specified it as an optional profile.

It is not used because of what it costs and reveals. A match is expected after about 2,048 complete
permutations, with a long tail: with the suite 3 parameters and the measured 70 seconds per
recovery, about 1.7 days on average on the reference laptop and about 8 days at the 99th percentile
(see [the detailed analysis](#final-word-preserving-cycle-walking-for-24-word-sources)), and about
twice as long for a creation with its check, which also makes trying variants of a half-remembered
password impractical. The last word reveals about 11 bits of information about the source, three of
them directly; it does not confirm the password; the walk length gives a timing signal; and the
owner must remember that the profile was used. The cheaper variants that come to mind do not avoid
these costs. Part II gives the rules, the cost distribution, the cheaper variants, a variant on 253
bits and the known-pair analysis under
[Final-word-preserving cycle walking for 24-word sources](#final-word-preserving-cycle-walking-for-24-word-sources).

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
   OpenSSL 3.5.5 replay of all 17 positive transcripts and seven negative recovery cases, one of
   them under the current length rules; this is independent primitive-level reproduction, not an
   independently authored MHFE implementation.
6. Review the Unicode 17.0.0 assignment check in a real implementation.
7. Review the deniability proofs, and extend the experiments to containers whose sources are
   related, to adaptive demands repeated while the wallet history develops, to challenges and
   evidence from outside the disclosure, such as records that link a wallet to its owner, to a BIP39
   passphrase, and to phrases created with the source check `MHFE-WALLET-CHECK-SEED-1`.
8. Determine when a decoy changes the decision of a rational adversary, as a Bayesian signalling
   game in which the decoy wallet's balance and history are costly signals and the adversary has a
   prior belief about the owner's wealth, comparing pooling, separating and semi-separating
   equilibria. This is a separate research question beyond the scope of this document.
9. Analyse suite 4 in its own right: review the extension of the deniability theorems to
   length-preserving decoys, and check whether its narrower halves allow any filter or multi-target
   saving beyond those described in its section.

## Suite 4: what the narrower state changes

Suite 4 keeps the source's length: its state is the source entropy, `ENT` = 128, 160, 192 or 224
bits, split into halves of `h = ENT/2` = 64, 80, 96 or 112 bits, and it has no verifier. This
section examines what the narrower halves change compared with suite 3. It is an analysis in the
same spirit as Part I, not a proof. The deniability theorems of Part I extend to suite 4, as stated
in [the suite 4 extension](#suite-4-the-same-analysis-at-every-length); the conjectures on attack
cost are not asserted for it.

**Salt diversity.** For fixed settings and round index a salt is a function of one `h`-bit half, so
it takes at most `2^h` values, `2^64` for a 12-word source; this is an upper bound on its diversity,
not a guarantee of `h` bits of randomness. RFC 9106 permits a 64-bit salt length under space
constraints [4]. This provides context, not a security justification for suite 4: its salts remain
128 bits long but are derived from an `h`-bit state half, and their distribution, correlations and
reuse require construction-specific analysis.

**Containers that share a salt.** In a model where only containers are known, the salt of the last
round comes from the container's left half `L_12`, which anyone holding the container can read. For
containers with the same `ENT` and settings whose halves are independent and uniformly random, the
expected number of pairs with equal left halves among `N` containers is `N(N - 1) / 2^(h+1)`: about
one half for `N = 2^32` containers of 12 words, with a probability of about 39 % that at least one
such pair exists, and correspondingly fewer for longer sources. An ideal random permutation maps any
fixed source to a uniform container, but the actual construction's bijectivity alone does not
establish this distribution: a fixed permutation maps uniform source entropy to uniform container
entropy, while nonuniform or related sources require an additional argument. Testing one password
guess on both containers of such a pair by full recovery takes 23 Argon2id calls instead of 24, and
a group of `g` containers with the same left half saves `g - 1` calls for that round. Coincidences
of the salts of other rounds depend on states that change with every password; they cannot be found
in advance, but they can be detected during a search, and with a known source the salt of the first
round is known as well. Whether such coincidences allow a larger saving across many containers has
not been shown either way.

**Precomputation.** A table that covers every possible input for likely passwords is not feasible:
for a 12-word container, covering every possible half-state requires evaluating `2^64` inputs for
each password at fixed settings and round index. Each Argon2id call uses the selected memory and
pass settings, with 2 GiB at the default memory level. Partial tables for chosen passwords and
observed salts are possible; their value depends on how often salts repeat, as in the previous
paragraph.

**Known pairs.** The filter of [Observation 2](#known-pairs) works for any width: with an original
seed phrase and its container, it tests a guess with 11 Argon2id calls. Its comparison now covers
`h` bits; in the model of independent uniform round functions a wrong password passes it with
probability `2^-h`. For an exhaustive search over five EFF words, `7776^5` candidates, the expected
number of false matches is then about 1.5 for 12 words. A candidate passing the filter is checked by
computing the skipped round, one more Argon2id call if the states were kept, and comparing the other
half.

**Generic Feistel bounds.** The results for ideal Feistel networks, such as Patarin's [29], bound an
adversary that obtains values of the permutation through an encryption or decryption oracle without
knowing the key, under that theorem's assumptions and for `q` much smaller than `2^h` queries. In
the scenario of one stolen container no oracle is assumed, and known pairs exist only where a
password was reused or a source leaked; these query bounds therefore cannot be read directly as a
number of password guesses. The random-function assumptions behind any such bound remain as open for
suite 4 as for suite 3.

**Deniability.** Every `ENT`-bit state is valid entropy for a phrase of the source's length, so the
reasoning of the consistency and uniformity lemmas of Part I applies in the smaller space: every
password opens a suite 4 container to a valid phrase of the same length, and the permutation for
that password maps it back. A decoy therefore keeps the source's length, which removes the suite 3
objection that a known short original seed phrase exposes a 24-word decoy. The experiments and both
theorems of Part I extend to suite 4 at every length, as stated in
[the suite 4 extension](#suite-4-the-same-analysis-at-every-length). They do not carry over to
related containers of different suites: if one phrase is encrypted under both, an adversary who
finds the short suite 4 container learns the length of the original seed phrase, which can expose a
decoy disclosure of the suite 3 container that relies on a 24-word reading. Where deniability
matters, further backups should be exact copies of one container.

**Copying errors.** A short container has a BIP39 checksum of `ENT/32` = 4, 5, 6 or 7 bits. A word
replaced at random during copying still passes it in about one case in 16, 32, 64 or 128, and the
container then recovers a different valid wallet without any error. Checking the finished backup
against a known address matters more than in suite 3.

**What follows.** The narrower state reduces the number of possible salts. A full recovery uses
twelve Argon2id calls, and the known-pair filter above uses eleven; these are costs of the stated
procedures, not lower bounds on all attacks against suite 4. Provided that no cheaper attack on the
construction exists, the protection against password guessing is set, as in suite 3, by the password
and the cost of Argon2id. The analysis has not been independently reviewed.

## Part II. Detailed design discussion

The sections below develop the design in more detail; the introduction gives their history. Unless a
statement names suite 4, it concerns suite 3; suite 4 is covered by
[Suite 4: what the narrower state changes](#suite-4-what-the-narrower-state-changes).
Cross-references such as "**Reference Implementation**" refer to sections of this Part. Citation
numbers refer to the single reference list in [`README.md`](../README.md#references).

For the requirements, use the [specification](../README.md#specification); Part I gives the main
analysis.

One statement applies to the whole of Part II, so the sections below do not repeat it: the cited
Feistel results assume independent random round functions and do not transfer to MHFE automatically,
the heuristics used are modelling assumptions rather than proofs, and nothing here has been reviewed
by an independent cryptographer. The consolidated list is under **Status and security claim**.

### Motivation

The specification's [Motivation](../README.md#motivation) gives the practical purpose, and its
[Suite parameters](../README.md#suite-parameters) and
[Application requirements](../README.md#application-requirements) say what recovery needs. This
section adds the background.

#### Practical purpose: protecting a physical backup without expanding it

**The practical goal is to keep a recovery phrase on a familiar, capacity-limited physical backup
while making possession or a photograph of that backup insufficient, by itself, to recover the
original seed phrase.**

Physical seed-backup products such as Cryptosteel, and comparable metal backups or capsules, provide
a finite number of character or word positions. Cryptosteel's own instructions describe storing
longer BIP39 phrases using abbreviated words [5]. Such media cannot accommodate arbitrary expansion
without changing the storage arrangement. A password-encrypted container that remains a valid
24-word BIP39 phrase could use the same word-oriented recording method, subject to the medium's
capacity and supported wordlist. This is the practical reason for investigating a fixed-size format
rather than simply adding more fields to a backup.

The 24-word container also has the ordinary syntax of a valid BIP39 mnemonic and carries no in-band
marker identifying it as encrypted. A casual observer may therefore interpret it as an ordinary
recovery phrase and may not realize that another mnemonic is concealed behind it. This format
ambiguity can reduce opportunistic attention and avoid revealing the encryption workflow itself. The
container's ordinary appearance provides practical concealment; by itself, that appearance is not
the formal plausible-deniability claim analysed in Part I. Storage context, accompanying
instructions, known wallet addresses, repeated containers, or prior knowledge of MHFE may reveal the
record's purpose and permit password candidates to be tested at the construction's KDF cost. Part I
analyses [decoy disclosures](#deniability), which remain possible when the use of MHFE is known.

The password, and a BIP39 passphrase if the wallet uses one, are kept apart from the container,
memorized or recorded in a separate place, possibly in a discreet form meaningful to the owner. This
preserves both confidentiality and the container's ordinary appearance, but a disguised written
password is no substitute for resistance to guessing.

**Author's motivation and hypothesis:** the author considers managing one sufficiently strong,
memorable password potentially easier than memorizing 12 or 24 mnemonic words in their exact order.
A separate, discreet password record may also be easier to manage than another full mnemonic record.
On that basis, the author considers an encrypted physical backup with a separately managed password
potentially safer against accidental viewing or photography than keeping the complete recovery
phrase openly readable. This is an authorial usability and security hypothesis motivating the
research, not a measured user-study result or a claim that the current MHFE construction has proven
security.

#### Prior problem statement and community context

BIP39 provides a compact human-readable representation of wallet entropy [3], but it does not define
an in-place encryption format for an existing mnemonic. As the specification's Motivation notes, a
Bitcoin Stack Exchange discussion in May 2021 posed almost the same goal and linked an experimental
AES-CTR prototype [8], [10];
[Earlier BIP39 backup-encryption and obfuscation proposals](#earlier-bip39-backup-encryption-and-obfuscation-proposals)
analyses that prototype. The available public record stops short of a complete, reviewed,
interoperable proposal: it does not provide a stable format, a memory-hard KDF profile,
comprehensive test vectors, or a construction-specific security analysis. This unresolved discussion
is the closest historical anchor for presenting MHFE to technical forums such as Delving Bitcoin.
MHFE treats it as evidence that the use case predates this specification, not as validation of the
present construction.

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

The specification states what recovery needs: with the default settings, only the container and the
password; a non-default PIM or memory level must be remembered, and in a rare case the word count of
the original seed phrase (see [Suite parameters](../README.md#suite-parameters) and
[Recovering a mnemonic](../README.md#recovering-a-mnemonic)). A BIP39 passphrase, if the wallet uses
one, is not part of MHFE and cannot be reconstructed from the container. Because the container does
not identify itself as MHFE, recovery also needs compatible software and the knowledge that the
record is a container; [Losing access](#losing-access) discusses what this means for heirs. Before
the backup of the original seed phrase is retired, the specification asks for a rehearsal from the
finished backup and a comparison with known wallet data (see
[Application requirements](../README.md#application-requirements)).

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

RFC 9106's first and second recommended Argon2id options both use `p = 4`, and its general
parameter-selection procedure likewise selects four lanes [4]. Suite 3 therefore selects `p = 4`.
Reducing `p` merely to lengthen wall-clock time is not presumed to improve password-guessing
resistance: an attacker can parallelize independent password candidates, and changing `p` changes
the Argon2 function itself.

Suite 3's default tuple of `m(0)` = 2 GiB, `t(0)` = 12 passes and four lanes is not one of RFC
9106's two recommended tuples. It keeps the memory and the four lanes of the RFC's first recommended
option and deliberately raises its single pass to twelve for an infrequent high-cost backup
operation. With four lanes, 2 GiB is the total Argon2 memory, nominally 512 MiB per lane; it is not
2 GiB per lane.

One MHFE permutation or inverse performs twelve sequential Argon2id calls; an encryption with its
required check performs twenty-four. If one working buffer is reused, its peak Argon2 allocation is
nominally `m(MEM)`, 2 GiB at the default memory level, regardless of PIM. At the default settings,
the nominal full-memory-pass volume of one permutation is `12 * 12 * 2 GiB = 288 GiB`. In general it
is `288 GiB * (PIM + 1) * m(MEM) / 2 GiB`. These values are not runtime predictions or attack-cost
proofs. The mapping is exact for suite 3, but its safety, upper bound, and usability remain
provisional until measured across the stated target systems and reviewed in the full construction.

#### Domain separation

The explicit purpose labels, `BE32(MEM)`, `BE32(PIM)`, and `BE32(i)` separate salt derivation from
mask derivation, different permitted work factors, other protocols, and other rounds. This does
**not** establish security against a named class of Feistel attack; it prevents accidental reuse of
one byte-level domain for different protocol roles.

`SUITE_ID` identifies the complete experimental cryptographic suite, not merely an editorial
revision of this document. Any incompatible change to the Feistel geometry or the round count `N`,
which is 12; state packing or encoding; password normalization or limits; salt derivation; the
Argon2 variant, version, fixed parameters, the permitted ranges or cost mappings of PIM and the
memory level; or `RoundMask` requires a new `SUITE_ID`, `DS_SALT`, and `DS_MASK`. Selecting a
different permitted PIM or memory level under the unchanged mappings does not define a new suite. An
identifier must not be reused for a changed mapping.

#### Mnemonic and seed

A **BIP39 mnemonic** is not itself the BIP39 seed. This construction packs the entropy encoded by a
valid BIP39 mnemonic into a 256-bit state. After decryption, normal BIP39 seed derivation may still
use the separate optional BIP39 passphrase.

#### Only the end salts are public

`S_i` is an actual Argon2 salt input, but it is deterministically derived from the Feistel state. It
does not add entropy and is not guaranteed to be globally unique. Only the salts at the two ends of
the chain can be computed without the password: for a known plaintext, `R_0` and therefore `S_0` are
known; when inversion begins from a ciphertext, `R_{N-1} = L_N` is likewise available from the
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

```text
input:  L_i || R_i
mask:   M_i = F_i(R_i)
output: R_i || (L_i XOR M_i)
```

The right half remains available after the round as the next left half. This property is what allows
a salt derived from `R_i` to be recomputed during decryption.

#### Why twelve rounds

The round count is informed by results for ideal balanced random Feistel schemes, but those results
must be stated with their attack models. Patarin [28] proves near-full-branch security for seven or
more rounds against adaptive chosen-plaintext attacks; the same paper states ten or more rounds for
adaptive chosen-plaintext-and-ciphertext attacks. A later result [29] establishes its stated
chosen-plaintext-and-ciphertext bound for six or more rounds under that paper's conditions.

`N = 12` is therefore the suite 3 choice: it is six rounds above the six-round threshold in [29],
five rounds above the seven-round CPA threshold in [28], and two rounds above the distinct ten-round
CPCA threshold stated in [28]. These differences are engineering margins, because MHFE uses
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
close to `2^-127` for one pair. The corresponding birthday scale is approximately `2^63.5`
comparable invocations. Different settings or round indices make the hash inputs distinct, so only
the approximately `2^-128` truncated-hash collision probability remains in that model. Accidental
collisions are therefore expected to be negligible at any realistic number of containers.

MHFE does not claim conformance to NIST SP 800-132, which requires the randomly generated part of a
PBKDF2 salt to have at least 128 bits [20]. The more direct guide for Argon2id is RFC 9106, which
recommends a 128-bit salt for password hashing and a salt unique for each password [4]. MHFE salts
have 128 bits but are derived from the state instead of being generated at random: for a fixed
password, the permutation must map every 256-bit source to exactly one 256-bit container, which
leaves no room for fresh randomness. Uniqueness is therefore a property to be argued, not one given
by construction. The estimate above, about `2^-127` for one pair of salts at the same settings and
round index under the stated model, covers accidental repetition between containers of independently
generated sources; it does not by itself make derived salts equivalent to independently generated
ones. A reviewer would also ask whether an adversary can force salts to repeat, whether related
states let expensive evaluations be reused, and what changes for identical sources, short sources
and chosen inputs; the threat models below and the open questions of Part I address parts of this.
SLIP-0039 uses the same kind of salt, the right half of the state, for its extendable backups [19],
which shows that the technique is not unusual but does not establish the security of MHFE. Suite 4
keeps a 12-word source at its own length, with 64-bit halves (see
[Shorter BIP39 mnemonics](#shorter-bip39-mnemonics)), and has at most `2^64` possible salt inputs
per round: the hashed salt remains 128 bits long, but its diversity is limited to at most `2^64`
values, not guaranteed 64 bits of randomness. This requires a separate analysis; see
[Suite 4: what the narrower state changes](#suite-4-what-the-narrower-state-changes).

These estimates treat intermediate Feistel branches as independent and uniform. Reprocessing the
same state with the same password, settings and round index repeats the same salt by design; that is
not an accidental collision.

#### Research note: public pre-mixing of the KDF schedule

Public reversible full-state pre-mixing was considered as a way to make the first state-derived KDF
input depend syntactically on the complete source state. It is not selected by any current profile.
For a uniformly random 256-bit source, it has little apparent practical benefit: the original
128-bit right branch already gives a distinct-source pair-collision probability of `2^-128` and a
birthday collision scale of approximately `2^64` independently sampled sources.

Pre-mixing also cannot prevent adversarially constructed branch collisions because the transform
would be public and invertible. Nor would it add entropy or remove the deterministic relation
between the two halves of a packed short source. The idea is retained only as a record of a
considered alternative; it should not add another cryptographic operation to a suite without a
demonstrated benefit and separate analysis.

#### BIP39 checksum semantics

A 24-word BIP39 mnemonic contains 256 entropy bits and an 8-bit checksum, but only `2^256` 24-word
sequences are valid. The checksum does not provide 8 extra payload bits.

Consequently the baseline transform operates only on the 256-bit entropy and recomputes the standard
checksum afterward. This preserves the BIP39 word count but leaves no independent room for an
authentication tag or version field.

For shorter sources, the universal packing of suite 3 uses the otherwise unoccupied part of that
same 256-bit state for `V_r`. This does not alter the outer BIP39 rule: every suite 3 container
still carries the ordinary 8-bit checksum of `Y` outside the 256-bit encrypted payload.

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
`Perm_{P,MEM,PIM}(X) = X` is only `2^-256` in that model. A ciphertext-only observer cannot
determine from `Y` alone whether it is such a fixed point of the unknown permutation parameterized
by the password and the settings, so the existence of fixed points does not supply a generic
password test or key-recovery shortcut.

The rare equality still matters operationally because it defeats concealment for that concrete
state. For a 24-word source, `Y = X` makes the encrypted mnemonic identical to the source mnemonic;
for a shorter source it would expose the complete packed state `X = E || V_r`, even though the word
counts differ. The specification therefore requires creation to compare the input and output states,
refuse to present an unchanged state as an encrypted backup, and ask for a different password, PIM
or memory level. Reapplying the same suite with the same password, settings, and input cannot escape
the same fixed point. These operational checks do not replace analysis of whether the concrete MHFE
construction behaves sufficiently like the idealized permutation.

Applications implementing MHFE must therefore present encrypted mnemonics as a distinct workflow and
must not silently pass them to normal BIP39 seed derivation. Users must retain knowledge that a
backup is MHFE-encrypted; compatible software supplies the exact suite definition rather than
requiring the user to memorize its literal identifier.

With the correct password and compatible suite implementation, MHFE decryption recovers the original
seed phrase for use by unmodified BIP39-compatible software. For a short source, the
recovery-verifier check supplies a failure signal for most incorrect candidates; for a 24-word
source, merely completing decryption does not verify that the inputs were correct. If that wallet
also uses the optional BIP39 passphrase, the BIP39 passphrase remains an independent second input
and is applied only after MHFE decryption.

### Security Considerations

#### Status and security claim

MHFE is an experimental research construction that has not been independently reviewed. No real
funds should depend on it. Principal limits of the current suites include:

- no formal PRP/SPRP proof for the MHFE construction and no proof that twelve rounds are sufficient;
- no proof that the Argon2id-derived round functions satisfy the assumptions of Luby-Rackoff or
  Patarin analyses;
- the per-guess cost arguments in Part I are unreviewed random-oracle sketches;
- no AEAD authentication and no built-in wrong-password detection for a 24-word source; the optional
  source profile adds only a statistical check, with the limits analysed below;
- suite 4 has no built-in verifier at any length and narrower halves with less salt diversity; its
  additional limits are discussed in
  [the narrower-state analysis](#suite-4-what-the-narrower-state-changes);
- no formal honey-encryption [43] guarantee; the plausible deniability of
  [decoy disclosures](#deniability) is analysed in Part I in a stated model, without review.

#### Resource exhaustion and untrusted containers

A checksum-valid input of a word count admitted by the selected suite can force a decoder to perform
every expensive Argon2id operation required by that suite. The outer BIP39 checksum filters
transcription errors but is not authorization to consume unbounded resources. Both suites fix their
KDF parameters for each setting and bound the length of the normalized password; implementations
must additionally enforce a local resource ceiling and fail rather than substitute cheaper
parameters.

Applications should start recovery only after an explicit user action, should keep the interface
responsive during long operations, and should offer cancellation where the execution environment
permits it. A worker or background thread is a responsiveness boundary, not a cryptographic vault.
Implementations must reject unknown suite identifiers, a PIM outside `0..1023`, a memory level
outside `0..21` or above what they support, and any other caller-supplied parameter override before
allocating large amounts of memory. These measures limit denial-of-service and accidental resource
use; they do not reduce the attacker's offline password-guessing cost.

#### Faults during computation

A hardware error, or an attacker able to cause one, may corrupt a round during creation. The
container would then not decrypt to the source, and the backup could be lost. The specification
therefore requires creation to decode the new container again and invert it, with twelve further
Argon2id calls computed afresh, and to report a mismatch; an application may show the container
while this check runs, marked as not yet verified. The check detects many accidental errors,
including a transient fault in either half, since the same fault would have to recur at the matching
place of the inverse. It does not detect a fault that disables the comparison, or a persistent
fault, such as failing memory or a miscompiled build, that affects the permutation and its inverse
in the same way. Decrypting the container on a second computer detects a fault of the first
computer's hardware; decrypting it with an independent implementation detects an error in the
software, including a miscompiled build, which the same build would repeat on any computer.
Resistance to deliberately induced faults, which an attacker controlling the computer could repeat
to collect several faulty results, is not established.

#### Threat models

The following models must be kept distinct. Unless a model states otherwise, the attacker is assumed
to know the suite and the public settings. The original source length may be known, tried
explicitly, or inferred with the same recovery-verifier rules available to the owner. Known wallet
identity data can provide an external password test, especially for a 24-word source.

**T1 — single-container offline guessing.** The attacker has one encrypted entropy `Y`. A baseline
attack evaluates a candidate inverse permutation `Perm_{P',MEM,PIM}^-1(Y)` for each password guess
`P'` and checks a short-source `V_r` relation or any available external evidence. This does not
imply that an optimal attacker must perform a full inversion when a cheaper filter is available.

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
provides no such shared-password test. Related but different passwords, such as a common root with
different endings or a small edit of an old password, select independent permutations in the
random-oracle model, so learning one of them gives no cryptographic shortcut to the others. It does
narrow the attacker's dictionary for them, often drastically; independent passwords for different
containers avoid this.

**T6 — active container modification or substitution.** The attacker can replace or alter a recorded
container and recompute its ordinary BIP39 checksum. Suite 3 provides no cryptographic
authentication. A short-source verifier rejects most incorrect recovered states but does not
authenticate the container or its origin; a 24-word source has no internal verifier at all. This
integrity and availability threat must be analyzed separately from offline password guessing and
confidentiality. The checks that a recovery can use trust different things, and none of them alone
protects against substitution:

| Check                                                               | What it confirms                                                                                                                      | What it does not confirm                                                                                                             |
| ------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------ |
| The container's BIP39 checksum                                      | The words were recorded and read without most accidental errors                                                                       | That the container is genuine: anyone can recompute it                                                                               |
| The recovery verifier of a short source                             | The recovered state satisfies the verifier relation for the detected length                                                           | Authenticity: whoever knows the password can build another passing container                                                         |
| The check at creation, decoding the words and inverting             | This implementation and computer produced a consistent container                                                                      | Anything about a copy that is replaced later                                                                                         |
| A known receiving address                                           | The recovered phrase belongs to the expected wallet                                                                                   | Anything, if the address itself came from an untrusted source                                                                        |
| The BIP32 master key fingerprint                                    | A 32-bit match: a wrong phrase passes with probability about `2^-32`                                                                  | That the match is not deliberate: about `2^32` trials find a phrase with a given fingerprint                                         |
| The 16-bit check of `MHFE-WALLET-CHECK-SEED-1` on a 24-word reading | A 16-bit match, if the phrase was created with that profile: a wrong phrase or BIP39 passphrase passes with probability about `2^-16` | Anything, if the phrase was created without the profile; that the match is not deliberate: about `2^16` trials find a passing phrase |

**T7 — old containers after a change.** A container stays useful to an attacker for as long as its
original seed phrase controls funds. Encrypting the same source again under a new password, higher
settings or a new suite does not neutralize an old container that was copied or stolen: it can still
be attacked with its own password and settings, and it recovers the same wallet. This differs from
T5, because the old and the new passwords may be unrelated. The practical protection is that of the
weakest copy an attacker can obtain; a new password protects the funds only after they are moved to
a new original seed phrase, or after every old copy is destroyed.

**T8 — partly known or weak source.** The analysis assumes a uniformly random source that the
attacker does not know. If part of the source leaks, the remaining uncertainty can be small: when
the first 11 words of a 12-word phrase are known, the last word carries 7 entropy bits and the 4-bit
checksum, so 128 completions remain, and with a known address and no BIP39 passphrase they can be
tested without MHFE at all. A strong container password does not undo a leak of the source itself,
and a source generated with little entropy is weak in the same way. The bounds of Part I describe a
uniform source; extending them to partial leaks would require including that information in the
model explicitly.

**T9 — leaked intermediate values.** The attacker obtains part of a computation: a salt, a state
between rounds, a round key or mask, or a dump of the Argon2id work area, for example from a log, an
error report, a file kept to resume a long operation, or swap.
[Leaks of intermediate values](#leaks-of-intermediate-values) gives the cost of a password test in
each case.

**T10 — dishonest implementation.** The software used for creation or recovery was modified to leak
secrets or to write containers that differ from the specification.
[Determinism as a check on implementations](#determinism-as-a-check-on-implementations) explains
what a second implementation can detect.

**T11 — attacker in the future.** The container is photographed now and attacked years later, with
cheaper hardware or better cryptanalysis. [Attacks in the future](#attacks-in-the-future) estimates
the effect.

**T12 — observer on the same computer.** Another process, or a script in another browser tab, shares
the computer during creation or recovery and measures cache timing.
[Observers on the same computer](#observers-on-the-same-computer) estimates what it gains.

**T13 — password known from elsewhere.** The owner also used the password for another service, or it
appears in a published list of breached passwords. Such lists are tried first, and the attack costs
only as many recoveries as the list is long. In the model of Part I such a password simply has a
very high probability; the practical rule is a password used nowhere else.

**T14 — faults during computation.** A hardware error, or an attacker able to cause one, corrupts a
round during creation or recovery. [Faults during computation](#faults-during-computation) describes
what the check at creation detects.

**T15 — many owners at once.** The attacker collects the containers of many independent owners and
needs to open any one of them. [Many containers of many owners](#many-containers-of-many-owners)
explains why salts derived from the state limit what the population gives the attacker.

#### Where known pairs can come from

A known pair is not free information. Realistic sources include later voluntary disclosure,
inheritance, audit, migration, independent compromise of a plaintext backup, malware observing a
later recovery, or deliberately published test material. The attacker must be able to link a
specific plaintext `X_i` to a specific encrypted container `Y_i`.

#### Many containers of many owners

An attacker who collects many containers may be satisfied with opening any one of them. Consider the
direct password-guessing procedure for independently generated suite 3 containers, under the stated
random-function model. Without coinciding password candidates and salts, that procedure evaluates
Argon2id separately for each container; accidental salt collisions are expected to be negligible at
realistic scales in this model. This is not a proof excluding other ways to share work or a lower
bound on every multi-container attack. Suite 4 has narrower salt diversity and its own
[analysis](#suite-4-what-the-narrower-state-changes).

Suppose that the passwords are drawn independently and uniformly from `2^n` values, and that the
attacker fixes in advance `b_i` distinct guesses for container `i`, `B` guesses in total. Container
`i` is then opened with probability `b_i / 2^n`, so the expected number of containers opened is
exactly `B / 2^n`, however the budget is split, and the probability of opening at least one is at
most the same. An adaptive attacker does better, because after a success it wastes no guesses on an
opened container: with two containers whose passwords take two values each and a budget of two
guesses, testing the first container and, after a success, the second opens 1.25 containers on
average, against 1 for any split fixed in advance. The gain is small while each container receives
only a small fraction of its password space. The real leverage comes from non-uniform passwords.
With passwords that people choose, the attacker spends the budget on the most likely ones across all
containers and opens the weakest, as in the cracking of stored password hashes, and it can prefer
containers that it expects to use cheaper settings or to hold more funds. The protection of a
population is therefore that of its weakest passwords, and the default settings that most owners
keep set its price.

#### Known-plaintext shortcut and KDF cost

`N` Feistel rounds do not by themselves prove a lower bound of `N` expensive Argon2 evaluations per
wrong password guess.

Given a known plaintext/ciphertext pair, an attacker can compute forward from `X` through some
rounds and backward from `Y` through the remaining rounds. At a skipped round, the Feistel relation

```text
L_{i+1} = R_i
```

can be checked without evaluating that round's mask. This provides a password filter when the
compared halves depend on the password guess, while omitting a selected expensive round. For
example, omitting the only round of a one-round network gives no password-dependent filter. The
rejection rate and the best multi-round shortcut require analysis of the full construction.

In a multiround design with earlier password-dependent inexpensive rounds, making only the last
round memory-hard permits an initial known-pair password filter that omits the expensive round. Its
effectiveness still depends on the preceding rounds.

#### Leaks of intermediate values

The attacker always has the container `Y`. A leaked intermediate value gives it an explicit way to
test a password guess `P'` more cheaply than a full recovery, which costs twelve Argon2id calls.
Rounds are numbered from 0 to 11, and `W_k` is the state after `k` rounds, so `W_0 = X` and
`W_12 = Y`. The salts `S_11`, from the container's left half, and `S_0`, when the source is known,
are public in any case. The costs below are those of the explicit tests described; the tests are
filters that reject wrong guesses with overwhelming probability, and they are not lower bounds for
all attacks.

| What leaked                                                                                                                                            | Explicit test of a guess                                                                                                                                                                          | Argon2id calls per guess                                                                                |
| ------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| The initial hash `H_0` of an Argon2id call, or the first blocks of its work area, when the call's salt is known (`S_11`, or `S_0` with a known source) | Compute `H_0` for the guess with BLAKE2b, and the first blocks from it if needed, and compare (RFC 9106, section 3.2 [4])                                                                         | none, only BLAKE2b                                                                                      |
| A salt `S_i`, `1 <= i <= 10`, or the half it comes from                                                                                                | Invert the container down to `R_i` and compare the salt                                                                                                                                           | `11 - i`; 1 for `S_10`                                                                                  |
| The state `W_k`, `1 <= k <= 10`                                                                                                                        | Compute between `W_k` and the container, skipping one round as in the known-pair filter; or, if the recovered source can be checked by its verifier or by wallet data, invert `W_k` to the source | `11 - k`; with a checkable source `min(11 - k, k)`: 1 for `k = 1` or `k = 10`, 5 for `k = 5` or `k = 6` |
| The state `W_11`                                                                                                                                       | Invert the container's last round and compare                                                                                                                                                     | 1                                                                                                       |
| The key `K_11` or the mask `M_11` of the last round                                                                                                    | Compute `Argon2id(P', S_11)`, derive the mask if needed, and compare                                                                                                                              | 1                                                                                                       |
| The key `K_0` or the mask `M_0`, with a known source                                                                                                   | Compute `Argon2id(P', S_0)`, derive the mask if needed, and compare                                                                                                                               | 1                                                                                                       |
| The key or mask of another round `i`                                                                                                                   | Invert the container down to `R_i`, then one call for round `i`                                                                                                                                   | `12 - i`                                                                                                |
| The Argon2id work area of a round, dumped at the end of the call                                                                                       | The dump determines the round's key; test as for that key                                                                                                                                         | as for the key                                                                                          |
| The source mnemonic                                                                                                                                    | The known-pair filter of Part I                                                                                                                                                                   | 11                                                                                                      |
| The normalized password                                                                                                                                | None needed                                                                                                                                                                                       | 0                                                                                                       |
| Round numbers and an ordinary progress indicator                                                                                                       | Nothing about the password: at fixed settings every permutation performs the same twelve rounds; timing observations belong to T12                                                                | 12, unchanged                                                                                           |

The moment of a leak matters as much as its content. Material from the start of an Argon2id call
with a known salt reduces a guess to hashing; the state `W_10` or `W_11`, the last round's key, or,
when the source can be checked, the state `W_1` reduces it to one Argon2id call instead of twelve; a
state in the middle costs no more than five calls when the source can be checked, and `11 - k`
otherwise. At a high PIM one call can take hours, so a state written to disk to resume an
interrupted operation is exactly such a leak; resuming safely means recomputing from the start, or
keeping the state only in the memory of the running process, which is itself exposed if that memory
is swapped to disk. This is why the specification forbids logging, displaying, exporting or
persisting intermediate values, including in error reports.

#### Birthday bounds and password guessing

For a balanced Feistel network with a `2n`-bit state and `n`-bit branches, classical small-round
multi-query analyses contain birthday-scale terms around:

```text
q ~ 2^(n/2)
```

where `q` counts queries or known/chosen pairs under one fixed permutation.

For suite 4's 128-bit same-length state, `n = 64`, giving a birthday scale around `2^32` in those
classical games. That number must **not** be reinterpreted as "the password breaks after `2^32`
guesses". In T1, different password guesses select different password-indexed permutations at the
selected settings, so the guesses do not accumulate as `q` queries to one fixed `Perm_{P,MEM,PIM}`.
For the 256-bit state of suite 3, `n = 128` and the corresponding birthday scale is around `2^64`
queries under one fixed permutation.

The multi-query viewpoint becomes relevant only when many samples genuinely belong to the same
permutation, parameterized by the password and the settings, and the attack has the information
model required by the particular proof or distinguisher.

#### Patarin and beyond-birthday security

The birthday scale is not a universal ceiling for balanced Feistel networks. Patarin's positive
security results show that, with enough rounds and independent random round functions, balanced
Feistel constructions can achieve security far beyond the basic birthday scale and approach the
information-theoretic scale associated with the branch size [28], [29], [49]. Reference [50] instead
develops generic attacks on Feistel schemes and supplies adversarial limits.

These results show that a 64-bit branch does not by itself imply a hard `2^32` security ceiling.

The relevant question for MHFE is whether its effective round functions satisfy assumptions strong
enough to justify any Patarin-style reduction.

#### Effective round function

For fixed password `P`, settings, and round index `i`, define the effective round function:

```text
S_i(R) = Trunc_128(BLAKE2b-256(DS_SALT || BE32(MEM) || BE32(PIM) || BE32(i) || R))

K_i(R) = Argon2id(password = P_enc, salt = S_i(R),
                  memory = m(MEM) KiB, passes = t(PIM), lanes = 4,
                  version = 0x13, type = Argon2id,
                  secret = empty, associated data = empty, output = 256 bits)

G_{i,P,MEM,PIM}(R) = Trunc_128(HMAC-SHA-256(K_i(R),
                     DS_MASK || BE32(MEM) || BE32(PIM) || BE32(i) || R))
```

This is exactly the same 128-bit salt, 256-bit derived key, Argon2id profile, and round-mask
function used in encryption and decryption. No Argon2 parameter or optional input is implicit in
this expanded definition. For fixed settings, `m(MEM)` and `t(PIM) = 12 * (PIM + 1)` are as
specified for suite 3. Here `K_i(R)` is the functional form of the round key; evaluating it at the
actual branch `R_i` gives the normative round key `K_i`.

Although the internal derived subkey depends on `R`, `G_{i,P,MEM,PIM}` is still one deterministic
function from 128-bit inputs to 128-bit outputs. Therefore generic Feistel analysis cannot be
dismissed merely because the internal subkey is input-dependent.

At the same time, attacks that specifically rely on reusing one fixed internal subkey over many `R`
values do not automatically transfer unchanged to this construction.

#### Argon2 salt-separation hypothesis

A potentially favorable heuristic concerns diversification across distinct `(i,R)` inputs. Different
inputs are not guaranteed to produce different 128-bit salts, and distinct salts do not
mathematically guarantee distinct 256-bit Argon2id outputs. In an ideal random-function model, two
distinct salts produce the same 256-bit output with probability `2^-256` per pair, so accidental
output collision is not the principal concern here. Repeated `(MEM,PIM,i,R)` inputs under the same
password and suite necessarily reuse the same salt and key. If, for fixed unknown `P`, fixed
settings (and therefore fixed memory and passes), and all other suite parameters, the mapping

```text
S -> Argon2id(P_enc, S; fixed suite 3 parameters)
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
assumption that must be justified or removed by a future proof or construction [4], [25].

Call this open assumption **A1 — Argon2 salt-separation hypothesis**.

#### Argon2id and side channels

Argon2id combines data-independent and data-dependent memory addressing: slices 0 and 1, the first
half of the first pass, follow the Argon2i-style data-independent strategy, while the remaining
computation uses Argon2d-style data-dependent addressing. It is therefore inaccurate to characterize
Argon2id's memory-addressing pattern as uniformly data-independent or uniformly data-dependent [4].

Implementations should use a well-reviewed Argon2id library, follow its memory-wiping facilities
where available, and separately analyze timing/cache exposure on the target platform. Native desktop
and browser/WASM implementations may have different side-channel constraints even on otherwise
supported high-memory systems.

#### Observers on the same computer

Argon2id computes the first half of its first pass with memory addresses that do not depend on the
data, and the rest with addresses that depend on the memory contents [4]. Suppose that an observer
sharing the computer, such as another process or a script in a browser that can measure cache
timing, recovers the block addresses of the data-dependent phase of one Argon2id call with a public
salt. It can then reject most password guesses by computing only up to that phase, about half a pass
of one call, and comparing the addresses that the guess would produce with the observed ones.
Against twelve calls of twelve passes each, that is roughly 1/288 of the computation of a full guess
in this idealized setting. It is not a measured speed-up: it depends on how precisely real
measurements resolve 1 KiB blocks, false matches must be removed by further checks, and the
password's entropy is unchanged, only the cost of testing a guess falls. The first Argon2id call of
a recovery, and of the check at creation, uses the public salt `S_11`, so a computation on a shared
computer exposes exactly such a call. A separate browser window does not prevent observation through
the shared processor caches; recovery belongs on a trusted offline computer with nothing else
running. [Argon2i on the rounds with a public salt](#argon2i-on-the-rounds-with-a-public-salt)
records how a future suite could reduce this shortcut for the public-salt calls, to about 3.5 bits.

#### Recovery verification is not authentication

A reversible mapping over all `2^256` entropy values consumes the entire 256-bit output domain. A
separate authentication tag cannot be embedded without reserving some outputs, adding external bits,
or giving up full-domain bijectivity.

The ordinary 8-bit BIP39 checksum on the encrypted mnemonic detects many accidental transcription
errors; a uniformly random 264-bit candidate passes that relation with probability `2^-8`. It is not
a cryptographic authentication tag. An attacker can modify the 256-bit entropy and recompute a valid
checksum. Likewise, the checksum recomputed after decryption cannot validate the MHFE password
because every 256-bit candidate entropy has one corresponding valid BIP39 checksum.

Short-source profiles deliberately reserve a strict subset of the 256-bit plaintext domain by
requiring `X = E || Trunc_r(SHA-256(E))`. A uniformly random recovered state satisfies that relation
with probability `2^-r`, so the verifier detects most wrong-password candidates and untargeted
corruption under the corresponding uniform-candidate model. It nevertheless remains an unkeyed
relation inside the encrypted plaintext. It does not provide AEAD authenticity, establish the
container's origin, protect against every maliciously constructed replacement, or conceal from an
offline attacker whether a fully decrypted password candidate passed the same relation.

#### Determinism and equality leakage

For one fixed password, settings, and plaintext entropy, the ciphertext is deterministic:

```text
Perm_{P,MEM,PIM}(X) = Y
```

with no nonce. Re-encrypting the same `X` under the same normalized `P` and the same settings yields
the same `Y`. Because `Perm_{P,MEM,PIM}` is a bijection, the converse also holds within one fixed
suite, password, and settings: equal ciphertexts imply equal packed plaintexts. An observer who
knows that two containers use that same permutation can therefore recognize reuse of one packed
state, although the state itself remains unknown. This normally indicates reuse of one source; the
specification's [Security Considerations](../README.md#security-considerations) say what equal
containers do and do not show.

Ciphertext equality across different passwords, settings, or suites does not establish plaintext
equality because those settings select different permutations. For two independently and uniformly
sampled BIP39 sources of the same `ENT`-bit length, the pairwise source-equality probability is
`2^-ENT`; even the shortest supported 128-bit source therefore has probability `2^-128` for one pair
and a birthday scale near `2^64` sources. Accidental equality is negligible at realistic scales, but
deliberate reuse remains visible under one fixed permutation.

#### Determinism as a check on implementations

A modified implementation could leak or keep the password or the phrase, write a container that only
it can decrypt, or encrypt under a key that its author knows. For a fixed source, normalized
password, suite and settings there is exactly one correct container, so an implementation that
writes anything else is detected by an independent computation of the same container, or by
decrypting it with an independent implementation. A correct implementation has no free choice that
could carry hidden information, so hidden data in a container would make it differ from the correct
one and be detected by such a check. Formats with a random salt or nonce can be recomputed with the
recorded values too, but there the implementation chooses those values, and they can carry data
undetected. Such a check cannot reveal secrets that malicious software kept or sent elsewhere while
producing a correct container, and a check run on the same, possibly compromised computer is not an
independent environment. Offline use, reproducible builds, published checksums and, for significant
funds, a second implementation from an independent source limit these risks; running it on a
separate offline computer gives an independent environment at the price of exposing the secrets to
that computer as well. The OpenSSL-based script that verified the suite 3 vectors is meant only for
public test inputs: it takes the phrase and the password as command-line arguments and is not a tool
for real wallets.

#### Password quality

Memory-hard KDF evaluations are intended to raise offline-guessing cost; they do not create entropy
in a weak human password. Effective guessing cost depends on the unavoidable KDF evaluations,
password quality, available verification, and any structural shortcut that reduces the required
Argon2 work per guess.

Choosing one of at most `K` complete, independent uniform password draws permits a limited
preference for memorable words. For `n` words from a list of size `L`, any selected result has
probability at most `K / L^n`, so its min-entropy is at least `max(0, n * log2(L) - log2(K))` bits.
Five EFF words selected from at most eight draws therefore retain at least about 61.6 bits of
min-entropy. This is a bound, not an exact entropy value or an average guessing-time estimate. The
limit covers the entire selection process, including restarts, and does not permit replacing,
reordering or shortening words. A generator cannot certify choices made outside it. Decoys need the
same selection distribution. A private story can be made after selection without changing the
password.

#### Attacks in the future

A container kept for decades can be photographed now and attacked later, when each guess costs less.
If the cost of a guess halves every `H` years, a container loses `T / H` bits of protection after
`T` years for an attacker with a fixed budget. These rates are assumptions describing a scenario,
not predictions or a guaranteed period of protection; memory bandwidth, which dominates Argon2id,
has improved more slowly than arithmetic.

| Years | Bits lost, halving every 2 years | Bits lost, halving every 3 years | Dice words to compensate |
| ----: | -------------------------------: | -------------------------------: | -----------------------: |
|    10 |                                5 |                              3.3 |               0.3 to 0.4 |
|    20 |                               10 |                              6.7 |               0.5 to 0.8 |
|    30 |                               15 |                               10 |               0.8 to 1.2 |

One extra dice word, about 12.9 bits, offsets roughly 26 to 39 years of such a decline under these
assumptions. The protection of an existing container never grows: higher settings and longer
passwords help only containers created with them, and T7 applies to the old ones. A weakness found
in Argon2id or in the construction would call for re-encryption under a new suite, as the
specification explains; [A second memory-hard function](#a-second-memory-hard-function) records a
hedge that was considered and not adopted. MHFE uses only symmetric primitives. A generic quantum
search in the manner of Grover's algorithm reduces the number of evaluations of an unstructured
search from `O(N)` to `O(sqrt(N))` [51], but each evaluation would have to carry out the chosen MHFE
password test reversibly, including its Argon2id work. This document neither proves that twelve
calls are unavoidable nor estimates the quantum resources required. MHFE does not protect the
wallet's elliptic-curve signature keys against Shor's algorithm [52].

#### Sensitive-memory handling

Implementations should minimize copies of plaintext entropy, encoded password, Argon2 outputs, and
intermediate Feistel states, and should erase such buffers when the language/runtime provides a
reliable mechanism. This is an implementation hygiene requirement, not a substitute for analysis of
the cryptographic construction.

#### Losing access

Losing access is a risk of its own, independent of any attacker. Recovery needs the container, the
password, any non-default settings and software that implements the suite, possibly decades later.
In the rare case that the packed state also passes the verifier of another length, recovery also
needs the word count of the original seed phrase or a receiving address of the wallet. The BIP39
checksum detects most copying errors but corrects none. The optional
[MHFE-REPAIR-1 card](../README.md#optional-repair-words-mhfe-repair-1) can repair unreadable or
wrong words within the code's bound; it is not needed for an intact container and does not replace a
second complete copy. The rehearsal check of the specification, a password recalled from time to
time, a copy of the container in a second place and an offline copy of a compatible release reduce
these risks.

**A recovery plan.** Record what recovery needs and where to find it: which backup is an MHFE
container (and, for a suite 2 container, its suite), compatible offline software, the password
format, any PIM or memory level other than the default, the word count of the original seed phrase
only in the rare case of the specification's [creation step 2](../README.md#creating-a-container),
and how to retrieve a trusted wallet-identity reference and any separate BIP39 passphrase. A note
that shows a suite 3 source has fewer than 24 words removes the decoy option, so keep it apart from
the container, like the password. Check scenarios in which a location is destroyed, the main
container copy is lost, the password is forgotten, the owner cannot help an heir, or the original
computer is unavailable. Instructions, password backups, references and software must be accessible
without first opening this wallet or using the secret whose loss they are meant to remedy. Rehearse
the plan from the finished backup; instructions do not replace missing secrets.

**A damaged backup.** If one word of a container cannot be read and its position is known, about
`1 + 2047 / 256`, roughly nine, of the 2,048 possible words give a valid BIP39 checksum, counting
the right one, and exactly eight if it is the last word. Each candidate needs a full recovery: about
9 to 18 minutes in total at the default settings on the reference laptop, and about 6 to 13 days at
PIM 1023. Two unreadable words give about 16,400 candidates, roughly 11 to 23 days of continuous
computation at the default settings. A short source's verifier will normally reject every wrong
candidate, subject to the false-match probabilities given under
[Source-length identification](#source-length-identification). For a 24-word source, each recovered
phrase has to be compared with a known address or other trusted wallet data. If the phrase was
created with `MHFE-WALLET-CHECK-SEED-1`, the 16-bit check of every 24-word reading rejects almost
every wrong candidate first. For an ordinary phrase with the same damage, the candidates need no
Argon2id work and can be checked against the wallet directly. A second copy of the container is
therefore worth more with MHFE than without it, and it should be an exact copy of the same verified
container, not a second encryption of the phrase, for the reasons given under
[Deniability](#deniability).

**Heirs.** A backup that holds a container looks like an ordinary phrase. An heir who does not know
that it is a container would enter it in a wallet, find an empty wallet or a decoy, and might
conclude that nothing is there. An heir has to learn separately that the backup holds an MHFE
container, which suite and settings it uses, the password, and where to find compatible software.
Marking the backup as an MHFE container helps the heir. It does not weaken the deniability proofs,
which already assume that the adversary knows that MHFE is used, but it reveals that use, can raise
an adversary's suspicion and removes the option of presenting the container as an ordinary phrase.
How these facts are passed on involves the same trade-off.

**An independent emergency route.** A separate threshold backup of the original entropy, retaining
its source length and wordlist, or an encrypted source backup with an independently random,
threshold-shared key could survive loss of all usable MHFE-password knowledge and all container
copies. A sufficient coalition obtains the source without those artifacts; individual holders below
the threshold do not. Any separate BIP39 passphrase still needs a recovery arrangement. This adds
custody and software dependencies, and protection is limited by the weakest complete recovery route.
A forgotten password and a lost main container copy can also be remedied by a secure full-password
backup and another exact container copy through the ordinary route. An independent route is needed
when every means of recovering the ordinary route's required material has been lost. The current
deniability experiments do not cover these additional recovery artifacts.

### Related Work and Alternatives

#### SLIP-0039

SLIP-0039 is especially relevant prior art [19]. Its master-secret encryption already uses a
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

BIP38 specifies passphrase-protected private keys and uses scrypt plus AES [32]. It stores format
information and a 32-bit address hash inside an expanded encoded record. This provides useful prior
art for password normalization, KDF parameterization, test vectors, and wrong-password verification,
but it does not satisfy the zero-expansion 24-word requirement.

#### BIP39 optional passphrase

BIP39 itself already gives every mnemonic/passphrase pair a valid derived seed, without a built-in
passphrase-error signal. This can support deniability in some contexts, but known wallet information
can still verify a guess. That mechanism affects seed derivation, not encryption of the mnemonic
backup [3]. MHFE must not be presented as a replacement for the BIP39 passphrase; the two can
coexist.

#### Honey encryption

Juels and Ristenpart formalize honey encryption for low-min-entropy keys by using a
distribution-transforming encoder so that decryption under wrong keys yields plausible messages
[43]. This is the relevant source for the term, but it does not describe MHFE's present security
claim. MHFE does not define a general encoder for arbitrary, non-uniform distributions of wallet
entropy; known wallet addresses can verify a candidate; and the short-source recovery verifier
intentionally rejects almost all wrong-password candidates. Syntactically valid BIP39 output is
therefore not sufficient to claim honey-encryption security in general. The special case of a
uniformly generated 24-word source, with a uniform model and the identity as its encoder, is
analysed in Part I together with [decoy disclosures](#deniability).

#### Earlier BIP39 backup-encryption and obfuscation proposals

A 2021 Bitcoin Stack Exchange discussion asked directly how an existing BIP39 mnemonic could be
encrypted into another mnemonic without changing the recovered wallet seed and linked a small
AES-CTR prototype [8], [10], [53]. This is direct community history for the problem statement. The
initial prototype derived its AES key as `SHA-256(password)`; a later revision changed that step to
PBKDF2-HMAC-SHA512 with 2,048 iterations and the fixed salt `mnemonic-encryption`. Both revisions
use AES-CTR with an all-zero IV. Reusing one password therefore repeats the CTR keystream, so for
two source entropies `E_1` and `E_2` and their ciphertext entropies `C_1` and `C_2`:

```text
C_1 XOR C_2 = E_1 XOR E_2
```

The relation alone does not recover either of two independently random and otherwise unknown
entropies. If either entropy is known or attacker-controlled, however, it reveals the other one
directly. This is separate from the cost of deriving the password key and violates CTR's
cross-message counter-block uniqueness requirement [11]. Its author also proposed the scheme on the
bitcoin-dev mailing list in May 2021 (see the update below). MHFE avoids this particular relation
through a password-indexed permutation and state-derived round inputs.

`Seedshift`, `bip39_obfuscator`, and `BIP39Colors` are community projects for shifting BIP39 word
indices or re-encoding them as Traditional Chinese wordlist code points or RGB colors [37], [38],
[39]. They illustrate demand for backups that do not visibly expose the English words of the
original seed phrase, but they provide forms of concealment rather than comparable modern
encryption. `bip39_obfuscator` applies a public, deterministic index-for-index mapping with no
secret key; anyone who recognizes the representation can reverse it. `BIP39Colors` likewise uses a
public deterministic encoding that packs the positions of 12 or 24 BIP39 words into 8 or 16
hexadecimal RGB colors and includes enough position information to recover the words even when the
colors are reordered [39]. It has no secret key and therefore provides visual obfuscation rather
than confidentiality against an informed observer. `Seedshift` applies manually computable modular
shifts derived from dates. Its own documentation warns that the result is not cryptographically
secure and can be brute-forced [37]. None of these constructions uses a memory-hard KDF or provides
a security argument for a password-indexed pseudorandom permutation. They should therefore be
treated as public re-encodings, obfuscation, or a simple shift cipher, not as substitutes for
reviewed mnemonic encryption. This comparison does not itself establish the security of MHFE.

`MnemonicCrypt` is a closer implemented comparison: it removes the source BIP39 checksum, applies
configurable Argon2id and AES-CBC with a separate random 128-bit salt, and renders the ciphertext
and salt as word sequences [33]. For a 12-word source it produces a 24-word encrypted mnemonic plus
a 12-word salt mnemonic, or 36 words of total recovery material. For a 24-word source it produces a
36-word encrypted mnemonic plus a 12-word salt mnemonic, or 48 words in total. The KDF parameters
must also be preserved separately. Its padded representation is intentionally an extension of BIP39
rather than an ordinary wallet-generated mnemonic. It therefore addresses password hardening and
word-oriented storage, but not MHFE's fixed 24-word, no-in-band-metadata design constraint.

Other mnemonic encryption systems reserve capacity or change the mnemonic domain. `Mnemonikey`
encodes a 128-bit OpenPGP seed in a custom 4,096-word list; its encrypted 16-word form carries a
version, creation time, random salt, encrypted seed, checksum, and a 5-bit password verifier, and
derives its AES-128 key with Argon2id [34]. `pktseed` defines a custom 15-word PKT seed containing
version, encryption, checksum, birthday, and seed fields [35]. Its current encryption code derives a
19-byte mask from Argon2id with a fixed salt and XORs that mask with the birthday-and-seed payload,
so same-passphrase reuse creates a cross-record XOR relation analogous to the 2021 prototype [10].
These are useful comparisons for compact mnemonic metadata and recovery verification, but neither
transforms an existing BIP39 mnemonic into another BIP39 mnemonic.

`seed-otp` takes a different approach: it adds a separately stored per-word pad modulo 2,048 [36].
This can preserve the source word count and BIP39 wordlist membership and can provide one-time-pad
security when the pad is uniformly random, secret, and never reused. Its ciphertext normally fails
the BIP39 checksum, and the scheme moves the backup burden to another secret of comparable size
rather than deriving protection from a memorable password.

A non-exhaustive search of public GitHub repositories and the cited community discussions, repeated
on 2026-09-22 and extended on 2026-10-03, found many encrypted wallet files, mnemonic obfuscators,
secret-sharing formats, and custom word encodings, but no implementation combining all of the
following properties:

- an existing 12-, 15-, 18-, 21-, or 24-word BIP39 source;
- one ordinary checksum-valid 24-word BIP39 ciphertext container;
- exact recovery of the original entropy under a password;
- for every shorter source, use of all otherwise unused state capacity as one hash-based recovery
  verifier `V_r = Trunc_r(SHA-256(E))`, whose first `ENT/32` bits are exactly the source mnemonic's
  BIP39 checksum and whose 128-, 96-, 64-, or 32-bit width gives uniform-candidate false-acceptance
  probability `2^-128`, `2^-96`, `2^-64`, or `2^-32`, respectively, without expanding the container;
- no mandatory separately stored salt, nonce, authentication tag, or expansion words; the default
  settings are implicit, while deliberately selected non-default settings must be remembered; and
- a memory-hard, state-derived KDF schedule inside a format-preserving permutation.

This search result narrows the known comparison set; it is not an exhaustive prior-art search, a
novelty claim, or evidence that MHFE is secure.

**Update, 2026-10-03: further prior-art search.** A further search of the bitcoin-dev archive,
public GitHub repositories, Monero and Lightning wallet formats, the IACR ePrint archive, arXiv and
Google Patents found these related works. They show that encrypting a mnemonic with a password into
a mnemonic of the same length, and opening a valid decoy wallet under a wrong password, predate
MHFE:

- **The 2021 prototype on bitcoin-dev.** Tobias Kaupat, the author of the prototype above, also
  proposed it on the bitcoin-dev mailing list in May 2021 under the subject "Encryption of an
  existing BIP39 mnemonic without changing the seed" [9]. Replies recommended stretching the
  password with PBKDF2, scrypt or Argon2. The construction is the one analysed above: a
  password-only key, AES-CTR with a zero IV and a repeated keystream.
- **seed-encrypt** [42], since September 2024, encrypts the entropy of a 24-word phrase into another
  24-word phrase. Its key sequence uses Argon2id with 2 GiB, feeding each result into the next call
  and increasing the pass count. Creation uses the latest key after reaching a user-selected time
  limit; the author recommends an hour or more. Balloon hashing appears in comments but is not
  called by the cited implementation. Unlike MHFE it uses one built-in salt for every user, so the
  key sequence for one password and thread count applies to every container; it encrypts the two
  128-bit halves independently with AES-256 and accepts only 24-word sources. Recovery enumerates
  candidate phrases along the key sequence: the time limit is a stopping rule, not a fixed number of
  KDF calls that is portable across hardware. Three optional extra words encode a revision prefix,
  thread count and time-limit setting.
- **Monero's seed offset passphrase** [40], in the Monero wallet since at least 2019, adds
  `cn_slow_hash(passphrase)` to the spend key and shows the result as another 25-word seed. A wrong
  passphrase gives another valid wallet; a guest tutorial in Monero's documentation suggests decoy
  wallets [54]. It is not a BIP39 format, it has no salt, so one hash per passphrase applies to
  every seed, and it has no recovery check.
- **Polyseed** [41], since 2021, a 16-word Monero seed format, can encrypt its secret with a
  password: it XORs a mask from PBKDF2-HMAC-SHA256 with 10,000 iterations and a fixed salt, and sets
  a flag bit. It is a format of its own, its KDF is not memory-hard, and one password gives the same
  mask for every seed.
- **aezeed** [55], in LND since 2018, enciphers a new wallet seed with the AEZ wide-block cipher and
  scrypt into 24 words of the BIP39 list, storing a version, a 5-byte salt and a checksum among
  those words. It defines a new seed rather than encrypting an existing BIP39 mnemonic, and its
  words are not a BIP39 phrase.
- **Seed XOR** [56], 2021, and **BIP39-XOR** [57], 2023, split a phrase into several valid phrases
  of the same length whose XOR is the original seed phrase. Each part is a working wallet and can
  serve as a decoy, but the other parts are secrets as large as the phrase itself; there is no
  password.
- **PhraseCrypt** [58], 2026, includes a honey-encryption mode that XORs BIP39 entropy with a mask
  derived by PBKDF2-HMAC-SHA256 with 200,000 iterations and a random 16-byte salt. A wrong password
  yields a valid phrase of the same length instead of a password error. Its stored form is an
  expanded Base64 container containing a version byte, salt and ciphertext, not a BIP39 phrase. A
  dedicated duress password is listed as an idea for future work, not an implemented feature.

In this non-exhaustive search, no paper or patent describing the encryption of an existing BIP39
mnemonic into another mnemonic was identified in the IACR ePrint archive, arXiv or Google Patents.
The closest patents identified concern turning an encrypted secret into words, or splitting and
storing seed phrases; this does not establish that no closer prior art exists.

These findings narrow MHFE's proposed contribution to a combination of properties rather than any
single element. Among the BIP39-to-BIP39 password-encryption tools examined here, none derives its
salts from the state, avoiding both a separately stored salt and one salt shared by all users; none
fills the free bits of a shorter source with a verifier that begins with its own BIP39 checksum,
inside a universal 24-word container that hides the source length; none runs a memory-hard KDF in
every round of a format-preserving permutation; and none states a model with proofs for its
plausible deniability. This does not make state-derived Feistel salts or a KDF in each round new:
SLIP-0039 already uses both [19], as discussed above. The proposed contribution is the combination
in suite 3, together with the specification, independently reproduced test vectors and reference
implementation. The search remains non-exhaustive and does not establish novelty or security.

#### Luby-Rackoff and Patarin

Luby-Rackoff supplies the foundational theory for constructing pseudorandom permutations from round
functions. Patarin's later work is relevant to generic attacks and beyond-birthday security for
multi-round balanced and unbalanced Feistel schemes. These papers define the PRP/SPRP models and
Feistel bounds against which MHFE should be evaluated. Their proofs assume independent idealized
round functions. MHFE instead derives every effective round function from one password and
state-dependent Argon2id inputs, so their security bounds cannot be claimed for MHFE without a
separate construction-specific reduction [28], [29], [30], [49], [50].

#### Format-preserving encryption

General FPE constructions demonstrate how to build permutations on constrained domains [59], but
they do not by themselves provide memory-hard password guessing or solve the no-metadata salt
problem. Morris, Oberschelp, and Santhakumar construct a no-expansion pseudorandom permutation in
the bounded retrieval model using a large key, random-oracle assumptions, and the Thorp shuffle
[60]. Its hybrid analysis and explicit treatment of uniform distinct messages are relevant
methodology, but its leakage model, key structure, round function, and security game differ
materially from MHFE.

#### Thorp and maximally unbalanced Feistel

Thorp-style constructions are important prior art for very small domains and show that the birthday
behavior of a small balanced branch is not a universal limitation of all Feistel architectures.
Published Thorp bounds [61] use many cheap micro-rounds. Substituting a full Argon2id invocation for
every micro-round can require hundreds or more expensive calls at these state sizes, depending on
the selected bound and target security. This suggests a substantial latency problem, but neither a
practical latency figure nor a universal minimum round count follows without choosing and analyzing
a specific construction. Whether a memory-hard key can safely control a whole pass of cheap
unbalanced rounds without reintroducing a state/salt circular dependency remains an open research
question.

### Theoretical Investigation and Alternative Designs

The following sections explain the packing and the geometry that suite 3 adopted and record the
alternatives that were studied but not adopted. Suite 3 uses the balanced 128|128-bit Feistel
network and the universal packing below. Suite 4 defines the balanced length-preserving
shorter-state construction; its separate analysis appears above. Other shorter-state variants, the
final-word profile and the source-heavy 1:3 family remain research alternatives, not production
recommendations or finalized encodings. Unless explicitly labeled otherwise, sizes in the
construction formulas and tables below are expressed in bits.

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
automatically imply a `2^32` password security ceiling; classical birthday bounds and password
guessing are different attack models, and Patarin-style results show that multi-round Feistel can
exceed the basic birthday regime in ideal models. Nevertheless, every shorter state size requires
separate analysis; suite 4 defines this mode, and
[its section](#suite-4-what-the-narrower-state-changes) examines what the narrower state changes.

#### Universal 24-word containers for shorter sources

Suite 3 packs every standard BIP39 source length with one formula:

```text
ENT = bit length of source entropy E
r   = 256 - ENT

V_r = Trunc_r(SHA-256(E))
X   = E || V_r
```

When `ENT = 256`, `r = 0`, `V_r` is the empty bitstring, and `X = E`. For every shorter source, the
source entropy is retained exactly and every remaining position in the 256-bit state is filled by
deterministic recovery-verifier bits. No independent checksum field, second custom check, tag,
padding rule, or random filler is added.

| Source words | `ENT` | `r` | Packed state `X`                       | Uniform-candidate verifier acceptance |
| -----------: | ----: | --: | -------------------------------------- | ------------------------------------: |
|           12 |   128 | 128 | `E_128 \|\| Trunc_128(SHA-256(E_128))` |                              `2^-128` |
|           15 |   160 |  96 | `E_160 \|\| Trunc_96(SHA-256(E_160))`  |                               `2^-96` |
|           18 |   192 |  64 | `E_192 \|\| Trunc_64(SHA-256(E_192))`  |                               `2^-64` |
|           21 |   224 |  32 | `E_224 \|\| Trunc_32(SHA-256(E_224))`  |                               `2^-32` |
|           24 |   256 |   0 | `E_256`                                |                  No internal verifier |

This construction exploits a direct relationship with BIP39. For a source entropy of length `ENT`,
the ordinary BIP39 checksum is:

```text
CS = Trunc_(ENT/32)(SHA-256(E))
```

Because `V_r` is a longer prefix of that same digest for every short source, its first `ENT/32` bits
are exactly the original BIP39 checksum. The remainder extends the same check:

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

For each short source length, recovery parses `X` into `E || V_r` and accepts that reading only if:

```text
V_r = Trunc_r(SHA-256(E))
```

All `r` bits are compared. For uniformly distributed candidate `X`, the set of states satisfying
this relation has exactly `2^ENT` members among `2^256`, because each possible `E` determines one
and only one `V_r`. Its acceptance fraction is therefore exactly `2^-r`; this counting statement
does not require treating SHA-256 as a random oracle. Applying that fraction to actual
wrong-password decryptions does require an appropriate assumption about the MHFE permutation's
candidate distribution.

`V_r` is an unkeyed **recovery verifier**, not AEAD, and does not authenticate the container or its
origin. Anyone can alter `Y` and recompute the visible outer BIP39 checksum. Without the password,
however, that party cannot in general choose the resulting decrypted `X` or recompute a valid
verifier inside the encrypted plaintext; under the uniform-candidate model, an altered candidate
passes with probability `2^-r`. A party that knows the password can construct a different valid
container. Both the owner and an offline attacker testing password candidates can evaluate `V_r`
after candidate decryption. The intended cost control is that obtaining the candidate requires the
MHFE inverse and its memory-hard Argon2id evaluations; whether the structured state permits a
shortcut using fewer KDF evaluations is an explicit open research question.

The verifier does not add source entropy. A 12-word source still has 128 bits of source entropy, not
256, even though its packed state is 256 bits wide. Its remaining 128 bits are completely determined
by `E`.

##### Fixed 128|128 state structure

The packing gives every source length the same 256-bit balanced Feistel geometry:

```text
L_0 = E[0:128]
R_0 = E[128:ENT] || V_r
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
`Ent(A | B)` denote the Shannon entropy of `A` given `B`, in bits. Write `E = L_0 || T_t`, where
`t = ENT - 128`. The packing copies `T_t` verbatim into `R_0` and appends a deterministic hash
prefix. For each fixed `L_0`, different `T_t` values therefore produce different `R_0` values, so:

```text
Ent(R_0 | L_0) = Ent(T_t | L_0) = t
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
value, the probability that this verifier suffix remains unchanged is `2^-r`: `2^-128`, `2^-96`,
`2^-64`, or `2^-32` for 12-, 15-, 18-, or 21-word sources respectively. If `R_0` changes, the
subsequent 128-bit salt hash is also expected to change except for its own collision probability.

This property comes with a structured plaintext domain. For each short source length, valid packed
states form the set:

```text
Packed_ENT = { E || Trunc_(256-ENT)(SHA-256(E)) : E in {0,1}^ENT }
```

`Packed_ENT` contains exactly `2^ENT` states and occupies the fraction `2^(ENT - 256)` of the
complete 256-bit domain. It is a structured subset, specifically the graph of a deterministic
truncated-hash function; it is not generally a linear subspace.

That restricted size is not a special price paid for early whole-source sensitivity. It is
mathematically unavoidable for any deterministic lossless encoding of an `ENT`-bit source into a
256-bit container: there are only `2^ENT` distinct sources to place in `2^256` possible states. The
hash-based construction chooses how those states are distributed and simultaneously supplies
recovery verification and early whole-source sensitivity.

A permutation satisfying full-domain PRP security remains indistinguishable when an adversary
restricts its queries to a structured subset. The existence of `Packed_ENT` is therefore not by
itself evidence of a weakness. Because MHFE's KDF schedule depends on the evolving state, analysis
must still determine whether the public relation defining `Packed_ENT` enables related-input,
known-pair or reduced-KDF password tests.

###### Collision-diversity hypothesis for the first state-derived salt

The mixed raw-and-hash construction may give `R_0` close to 128 bits of collision diversity across
distinct independently sampled source entropies, even though the hash suffix adds no independent
entropy. Reuse of the exact same source is excluded from this statement because the construction is
deterministic and necessarily reproduces the same `R_0`.

For the 21-word profile:

```text
R_0 = E[128:224] || Trunc_32(SHA-256(E))
      96 bits       32 bits
```

Two distinct independent sources must first have the same 96-bit entropy tail and then the same
32-bit hash prefix to produce the same `R_0`. Under the heuristic that the SHA-256 prefix behaves
independently for distinct full inputs sharing that tail:

```text
Pr[R_0^(1) = R_0^(2)] ~ 2^-96 * 2^-32 = 2^-128
```

The same heuristic pattern holds for every supported source length:

| Source words | `R_0` construction                          | Heuristic distinct-source pair-collision probability |
| -----------: | ------------------------------------------- | ---------------------------------------------------: |
|           12 | `Trunc_128(SHA-256(E_128))`                 |                               approximately `2^-128` |
|           15 | `E_{tail,32} \|\| Trunc_96(SHA-256(E_160))` |               approximately `2^-32 * 2^-96 = 2^-128` |
|           18 | `E_{tail,64} \|\| Trunc_64(SHA-256(E_192))` |               approximately `2^-64 * 2^-64 = 2^-128` |
|           21 | `E_{tail,96} \|\| Trunc_32(SHA-256(E_224))` |               approximately `2^-96 * 2^-32 = 2^-128` |
|           24 | `E_{tail,128}`                              |             `2^-128` for independent uniform sources |

The `2^-128` entries describe the probability that one distinct independently sampled pair has the
same `R_0`; they do not mean that collisions require `2^128` samples. The corresponding birthday
scale is approximately `2^64` independent sources.

The first state-derived salt is:

```text
S_0 = Trunc_128(BLAKE2b-256(DS_SALT || BE32(MEM) || BE32(PIM) || BE32(0) || R_0))
```

Its dependence on `R_0` may provide close to full-width diversification across containers. For two
distinct containers using the same suite and settings, an idealized random-function calculation
allows pairwise equality of `S_0` to arise either from equal `R_0` values or from a hash collision
between unequal values. Using the preceding `2^-128` heuristic for equal `R_0`, the combined
probability is `2^-128 + (1 - 2^-128) * 2^-128 = 2^-127 - 2^-256`, which is close to `2^-127` rather
than exactly `2^-128`. Conditional on `L_0`, the source entropy remaining in `R_0` is still only 0,
32, 64, 96 or 128 bits as shown above: the effect may reduce accidental salt reuse, but it adds no
entropy.

##### Source-length identification

A decoder infers a short source length without stored metadata. Every recovery checks all four short
relations, also when the user states a length, and the detected length takes precedence over a
stated one. After decrypting the container to one 256-bit candidate `X_{candidate}`, it tests:

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

A single passing relation gives a strong probabilistic indication of that source length. Which
readings are given, in which order and with which labels, how a stated length is used, and the
16-bit source check of every 24-word reading are defined only in
[Recovering a mnemonic](../README.md#recovering-a-mnemonic); this section gives the probabilities
behind those rules.

Perfect self-description is impossible while the 24-word source mode covers all `2^256` plaintext
states. Every packed short state is also a possible 256-bit entropy value for some 24-word source.
Therefore failure of all short checks means only "no short profile was verified"; the 24-word
reading of the state remains unverified and is not proof of a correct password. For a uniformly
distributed 256-bit candidate, including an independently generated 24-word source under the model
above, the individual accidental verifier-relation match rates are:

| Short relation tested | Probability |                                    Approximate frequency |
| --------------------- | ----------: | -------------------------------------------------------: |
| 21 words              |     `2^-32` |                                       1 in 4,294,967,296 |
| 18 words              |     `2^-64` |                          1 in 18,446,744,073,709,551,616 |
| 15 words              |     `2^-96` |              1 in 79,228,162,514,264,337,593,543,950,336 |
| 12 words              |    `2^-128` | 1 in 340,282,366,920,938,463,463,374,607,431,768,211,456 |

The probability that at least one short relation passes is bounded by:

```text
2^-32 <= Pr[at least one short relation passes] <= 2^-32 + 2^-64 + 2^-96 + 2^-128
```

The `2^-32` term from the 21-word profile dominates, so the probability of at least one accidental
short-relation match is approximately `2^-32`, or about one in 4.29 billion. This is strong
probabilistic screening for accidental uniform candidates, not exact type information. A
deliberately constructed 24-word entropy can equal a valid packed short state with certainty. Under
the uniform-candidate heuristic, a wrong-password candidate passes no short relation unless it
produces one or more accidental short matches. Because every recovery checks all four relations,
this bound of about `2^-32` applies even when the user states a length. A stated length still helps:
a wrong password matches a stated 12-word length only with probability `2^-128`, and a match at
another length is reported as differing from the stated one.

##### Final-word-preserving cycle walking for 24-word sources

An unreleased suite 2 draft defined and implemented the optional profile
`MHFE-BIP39-256-EXPERIMENTAL-2-CYCLE-WALK-FINAL-WORD`. It preserves the complete final word of a
24-word source while leaving the permutation unchanged. It is not part of suite 3; this subsection
describes the same construction over the suite 3 permutation, the research idea of Part I. Such a
profile would be separate from standard encryption and would have to be selected explicitly during
both creation and recovery. The 24-word container does not encode which profile was used, so the
owner would have to remember that it was used: standard recovery would silently produce a different
24-word wallet. Its purpose would be to let an owner who remembers the last word of each wallet tell
which container phrase belongs to which wallet without decrypting anything, and to catch a container
phrase whose last word was copied wrongly: an 11-bit check of the container phrase, not of the
password or of the other 23 words.

Let `FW(E)` be the 11-bit index of the final BIP39 word obtained from 256-bit entropy `E`: the final
three entropy bits followed by the eight-bit BIP39 checksum. Let `Perm_{P,MEM,PIM}` be the suite 3
permutation. Creation applies the permutation at least once and continues until the complete
final-word index matches:

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

The encrypted container visibly reveals the source's final BIP39 word: three bits of the source
entropy directly and, through the eight-bit checksum, about 11 bits of information about the source
in total, which confines the source to a class of about `2^245` values. This preserved word is not
an authentication tag or password verifier: a successful recovery under a wrong password returns a
different 24-word candidate with that same final word. The correct password and settings still
recover the exact source.

Under an ideal-permutation heuristic, a final-word class has density `2^-11`, giving a match
probability of approximately 1 in 2,048 per complete permutation. The iteration count is therefore
modeled geometrically, but this is an estimate rather than a strict latency bound. Using the
measured command-line recovery time of about 70 seconds per permutation under
[Performance measurements](#performance-measurements) only as an illustration:

|       Statistic | Complete permutations | Approximate sequential time |
| --------------: | --------------------: | --------------------------: |
|          Median |                 1,420 |                  27.6 hours |
|  Expected value |                 2,048 |                  39.8 hours |
| 95th percentile |                 6,134 |                 119.3 hours |
| 99th percentile |                 9,430 |                 183.4 hours |

There is no small deterministic bound. The distance to the next member of a class can be vastly
larger than 2,048, and the input- and password-dependent runtime creates availability and timing
side-channel concerns. Cancellation and progress reporting keep an application responsive but do not
reduce the cryptographic work. Each password guess has a similarly large expected cost under this
model, although individual walk lengths vary, so trying many variants of a half-remembered password
is generally impractical.

**Why the proposed cheaper variants do not solve the problem.** Three cheaper variants come up
naturally. The first is a walk with a fast permutation and only one expensive Argon2id call to
derive its key. The difficulty is the salt of that call. It must be computable from the original
seed phrase during creation and from the container during recovery, and the only thing the two share
is the last word itself: 11 bits. There would therefore be only 2,048 possible salts in the world.
An attacker could compute Argon2id for a password dictionary once per salt and then test every such
container almost for free, which is exactly the shared dictionary that state-derived salts exist to
prevent. The second, doing the expensive part first and a cheap walk afterwards, fails differently:
during recovery the backward walk has no way to recognise where the expensive part ended. The third
is to find a matching container cheaply with light parameters and then look for a way to reach it
with the real ones, which does not help either: for a given password and settings, the expensive
permutation sends the source to exactly one container, fixed but unpredictable until it is computed.
Any search for a password, setting or tweak that makes that container land on the right last word
succeeds with probability about 1 in 2,048 per attempt, so it costs as many expensive evaluations as
cycle walking itself. The variant on 253 bits below would need about 256 expensive permutations
instead of 2,048, but requires a new permutation and its own analysis.

###### Preserving the complete final word by excluding three bits

A 24-word BIP39 mnemonic's final word contains the last three source-entropy bits followed by the
eight-bit BIP39 checksum. A hypothetical new profile could preserve the three entropy bits unchanged
and apply a newly defined permutation only to the other 253 bits. Cycle walking would then need to
match only the eight-bit checksum. Under the same ideal-permutation heuristic, each iteration would
succeed with probability approximately `1/256`, so the expected work would fall from 2,048 to 256
applications of the new permutation while preserving the complete final word. Using the measured
command-line time of about 70 seconds per permutation under
[Performance measurements](#performance-measurements) only as an illustration gives:

```text
256 * 70 s = 17,920 s ~ 4 h 59 min
```

This is not a shortcut that can be applied after the current 256-bit permutation. The BIP39 checksum
depends on all 256 entropy bits, including the final three, so changing those bits after a checksum
match generally invalidates the checksum. Restricting the existing 256-bit permutation to one fixed
three-bit suffix by an inner cycle walk would itself cost approximately eight permutation
applications and would restore the overall `8 * 256 = 2,048` expected-work factor. A direct
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

```text
W_0 = X
W_j = Perm_{P,MEM,PIM}(W_{j-1})
tau = min{ j >= 1 : FW(W_j) = FW(W_0) }
Y   = W_tau
```

Under threat model T3, an attacker may know the cycle-walking endpoints `(X,Y)`. Except when
`tau = 1`, those endpoints are not an adjacent pair `(W_{j-1}, W_j)` for one application of
`Perm_{P,MEM,PIM}`. Unless exposed through timing or instrumentation, the intermediate states and
`tau` remain hidden. The single-permutation Feistel shortcut described above therefore cannot simply
be applied independently `tau` times: each application would require an adjacent internal pair that
the attacker does not initially possess.

The opposite assumption is also unjustified. All iterations reuse the same `Perm_{P,MEM,PIM}`,
password, settings, and suite; they are not independently keyed layers. The stopping rule also
reveals a structured transcript condition:

```text
FW(W_j)   != FW(X)   for 1 <= j < tau
FW(W_tau)  = FW(X)
```

A construction-specific analysis must determine whether a meet-in-the-middle computation, a Feistel
invariant spanning several applications, repeated state-derived salts, or the final-word
non-membership conditions can test a password while omitting expensive rounds in more than one
application. Any such saving must be analyzed jointly with the number of cycle-walking iterations;
neither multiplying the one-permutation shortcut by 2,048 nor charging 2,048 independent full
attacks is a justified cost model.

Timing can expose an additional filter even before such a shortcut is found. In the idealized
geometric model with final-word-match probability `p_match = 1/2048`, let the observed correct
stopping time be `tau` and the stopping time under an independent wrong-password trajectory be
`tau'`. If an exact iteration count can be associated with `Y`, this timing-only filter does not
require knowledge of `X`: an attacker can inverse-walk from `Y` under each password guess and
compare its first-return count with the observed value. For one concrete observation `tau = t`, with
`Ex` the expected value:

```text
Pr[tau' = t]     = p_match * (1 - p_match)^(t-1)
Ex[min(t, tau')] = (1 - (1 - p_match)^t) / p_match
```

When both stopping times are independently sampled from that geometric model and the result is
averaged over the correct `tau`:

```text
Pr[tau' = tau]     = p_match / (2 - p_match) = 1/4095
Ex[min(tau, tau')] = 1 / (1 - (1 - p_match)^2) ~ 1024.25
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
the underlying block cipher is ideal [31]; applying it to MHFE assumes that MHFE behaves like an
ideal permutation. That theorem applies to the mathematical core, which permits returning the
starting point, before the operational rejection rule is applied.

#### Direction A and Direction B: geometry comparison

Two research directions are retained:

- **Direction A — balanced Feistel, the geometry of suite 3.** Use 128|128 bits for the 256-bit
  container. The formulas of suite 3 describe this direction.
- **Direction B — source-heavy 1:3 Feistel, alternative candidate.** Update one quarter using the
  remaining three quarters, then rotate the state. 32|96 bits describes a 128-bit state; a 256-bit
  container requires 64|192 bits instead.

The following table preserves the earlier comparison of hypothetical original-length states. It is
not the geometry of the universal 256-bit packing that suite 3 uses:

| Source words | Entropy state (bits) | Direction A split (bits) | Direction B split (bits) |
| -----------: | -------------------: | ------------------------ | ------------------------ |
|           12 |                  128 | 64 / 64                  | 32 / 96                  |
|           15 |                  160 | 80 / 80                  | 40 / 120                 |
|           18 |                  192 | 96 / 96                  | 48 / 144                 |
|           21 |                  224 | 112 / 112                | 56 / 168                 |
|           24 |                  256 | 128 / 128                | 64 / 192                 |

For a universal 256-bit outer payload, every source length instead uses 128|128 bits in Direction A
or 64|192 bits in Direction B. Input entropy and permutation state size are different quantities.
Packing a short source together with deterministic verifier redundancy into a longer state does not
create additional source entropy.

##### Evidence and trade-offs

Hoang and Rogaway analyze their unbalanced `Feistel^r[m,n]` construction using independently and
uniformly random round functions [21]. The figure and appendix numbers below are those of the full
version, ePrint revision of November 29, 2018. Figure 4 explicitly compares proven CCA-security
bounds on a 128-bit string for `m = 32`, `n = 96` (bold curves) and the balanced `m = n = 64`
(dashed curves), at 18, 36, 72, and 144 rounds. Their Appendix E comparison, particularly Figure 7
and its surrounding discussion, states that imbalance improves the bounds when enough rounds are
available, while the balanced construction has the stronger bound when rounds are scarce. Their
round counts apply to that paper's idealized construction.

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

```text
(A, B, C, D) -> (B, C, D, A XOR G_i(B || C || D))
```

Across three consecutive rounds, the initial `D` becomes the first output chunk without
modification. Given a known plaintext/ciphertext pair, an attacker can evaluate the rounds outside a
three-round gap and test that equality without evaluating the gap. In an adaptation with one KDF
evaluation per round, a four-round design therefore allows an initial filter using only one KDF
call. Equivalently, the first output chunk after four rounds is `A XOR G_0(B || C || D)`.

In an idealized random-function model the four-round filter has a false-acceptance rate of `2^-w`,
where `w` is the chunk width: 32, 48, or 64 bits for states of 128, 192, or 256 bits. Surviving
guesses require further checks. For balanced Feistel, a related known-pair filter can omit one
round; Part I describes this filter; whether a more efficient one exists is an open question.

Direction B therefore requires a separate round count, round-function definition, and
password-attack analysis. Larger KDF input alone is insufficient justification for choosing it.

### Reference Implementation

The implementation description and performance measurements in this section concern the suite 3
snapshot used for its public corpus and version 0.4.0. The later suite 4 and optional profiles are
part of specification version 0.5.0; their current vector locations are linked under
[Test Vectors](#test-vectors) below.

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
reading when none matches, and report every matching length when detection is ambiguous. They also
accept an explicit source length that replaces detection. The current rules forbid this: a stated
length never replaces detection. In this respect versions 0.4.0 and 0.5.0 do not conform to the
current specification. Creation refuses a container equal to its source. When the implementation
finds too little free memory, or the operating system refuses to reserve the Argon2 memory, it stops
with a typed error, `NOT_ENOUGH_MEMORY` or `MEMORY_ALLOCATION_FAILED`, instead of reducing the
memory; the operating system or the browser can still end the process during the work. The
operational result exposes only the recovered phrase, its word count and whether it passed a
verifier; source entropy, packed states, Argon2 outputs, masks and round traces appear only in the
separate vector code, which works only on the fixed public test inputs. Buffers that the
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
directions and every recovery case through its recovery, including the
[current recovery expectations](../vectors/suite3/README.md#current-recovery-expectations). A toy
reduced-width model must not be used as evidence of production security.

#### Performance measurements

The following whole-operation timings at the default settings were measured on the author's laptop
(Intel Core i7-1260P), each from start to end: on the command line with the release builds of commit
`ac195e8373df24fb11a1b0b241a324575ea09b03`, and in the browser with the MHFE 0.4.0 browser package,
driven in headless Chromium through the MHFE panel of the Wallet Key Derivation Tool. The
[measurement record](https://github.com/hobby-eng/mhfe/blob/b1d83504ba2458681111c14cade52fa0a178ddb4/measurements/README.md),
published in commit `b1d83504ba2458681111c14cade52fa0a178ddb4`, keeps the details:

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
seven recovery cases and 54 fast validation cases. The reference implementation generated them, and
an independent OpenSSL-based verifier replayed every transcript at full cost in both directions and
every recovery case through its recovery, including the
[current recovery expectations](../vectors/suite3/README.md#current-recovery-expectations). Each
transcript records the source mnemonic and entropy, the normalized password bytes, the packed state,
every round's salt and mask input messages, salt, Argon2id output, mask and state, the container and
the recovered result. The corpus notes record provenance and checks, and the specification's
[Test Vectors](../README.md#test-vectors) section states the requirements.

The current suite 4 corpus is in [`vectors/suite4/`](../vectors/suite4/), and the optional
source-check, repair-word and password-check-word examples are in the
[profile vectors](../vectors/profiles/README.md). Each corpus records its own coverage and
verification evidence; the historical suite 3 replay described above does not establish verification
of these later sets. The suite 2 vectors are archived in
[`vectors/archive/suite-2/`](../vectors/archive/suite-2/) and must not be replayed under suite 3.

Following BIP 3's recommendation that test vectors be available under CC0-1.0 or FSFAP in addition
to any other license, the vectors are released under CC0-1.0 so that implementations can copy them
without license friction [1].

### Known Limitations

This section records the present boundaries of both experimental suites and the optional profiles.
It is not a roadmap and does not commit the author to further research or implementation work.

- The selected Argon2id and Feistel parameters are supported by limited measurements on the author's
  laptop.
- Suite 3's short-source recovery verifiers intentionally provide an offline password-checking
  signal, while its ordinary 24-word source mode has no internal wrong-password test and automatic
  source-length detection remains probabilistic.
- Versions 0.4.0 and 0.5.0 of the reference implementation accept a stated source length that
  replaces detection, which the current length rules forbid.
- Suite 4 has no built-in verifier at any supported length. Its narrower states limit salt
  diversity, reveal the source's word count and require separate analysis of password filters and
  shared work; see [the narrower-state analysis](#suite-4-what-the-narrower-state-changes).
- The optional source check for new 24-word wallets is a 16-bit statistical filter, not confirmation
  of wallet identity. It conditions the source distribution, and the deniability theorems for
  uniformly generated sources do not automatically apply. With a nonempty passphrase it checks the
  recovered mnemonic and passphrase together; with the empty passphrase it filters MHFE password
  guesses alone.
- Repair words and the password check word add redundancy, not authentication. They repair only
  within their stated bounds, and disclosure of that redundancy reveals information about the
  container or password respectively. Passing either check does not establish the intended wallet.
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

## Research directions

These directions were first recorded on 2026-10-03, after suite 4 was added, and extended on
2026-10-05. None changes the algorithms of suite 3 or suite 4. The optional source-check,
repair-word and password-check-word profiles are now defined in the specification. This section
keeps the analysis of the source check and the password check word, sets the repair words apart from
the planned container check words, and distinguishes all three profiles from the remaining
proposals, which are not part of the specification. Each is written down with its costs, so that a
later suite or application can take it up or leave it. They cover application aids, possible changes
to the round function and the source, arrangements of the existing suites, and alternative formats
that would use a different cryptographic construction. Container check words are planned application
work; the other proposals remain research directions with the limits stated below.

### Container check words: a hash of the container (planned)

The specification now defines repair words,
[MHFE-REPAIR-1](../README.md#optional-repair-words-mhfe-repair-1): linear Reed-Solomon parity that
corrects unreadable and wrong words. Container check words are a different, planned record: a hash
that recognises a copy and filters repair candidates, but corrects nothing by itself.

A short public digest of the container lets an owner or an heir check a copy and identify candidates
for repairing it without the password and without any Argon2id work. It is computed from the
container alone. Here `Y` is the decoded container entropy, serialized as its raw bytes without the
BIP39 checksum, and `n` is its word count:

```text
C = SHA-256(domain || BE32(n) || Y)
```

Its first 33 bits, written as three English BIP39 words, are the container check words. They must be
labelled as a check: three words are not a valid BIP39 mnemonic length. All 256 bits, written as 64
hexadecimal digits, are the seal. The domain string, the exact layout and test vectors from two
independent implementations are still to be fixed.

Uses:

- **Checking a copy.** Every copy and every new engraving is compared with the check words before a
  password is typed. This matters most in suite 4, whose checksum has only 4 to 7 bits.
- **Repair.** For `e` unreadable words at known positions, the application enumerates candidates,
  keeps those with a valid BIP39 checksum and compares their check words. In an ideal-hash model,
  about `2^(11e - CS - 33)` wrong candidates survive on average, where `CS` is the BIP39 checksum
  length. This excludes the correct candidate and is a probabilistic estimate, not a guarantee of
  unique repair. With a 24-word container (`CS = 8`), the estimates are `2^-30`, `2^-19`, `2^-8` and
  about 8 for one through four unreadable words. For suite 4, three unreadable words leave about
  `1/16`, `1/32`, `1/64` or `1/128` false candidates for 12, 15, 18 or 21 words; four leave about
  128, 64, 32 or 16. Naive enumeration of three missing words in a 24-word container needs about
  `2^33` BIP39 checksum evaluations and `2^25` container-digest evaluations. When the last word is
  missing, its checksum bits can instead be recomputed, reducing the entropy assignments to `2^25`.
  A substituted word at an unknown position requires trying the positions too: up to `n * 2047`
  replacements for one substitution, and approximately `binomial(n, e) * 2047^e` for exactly `e`
  substitutions. Every proposed correction is shown to the user before recovery, and unresolved
  candidates remain explicitly ambiguous.
- **Telling container phrases apart.** Copies of different containers, for example an old one kept
  after a re-encryption, are recognized before a recovery fails for an unclear reason.
- **Detecting a substitution.** The 33-bit check words provide no authentication: a search for
  another valid container matching a fixed set of check words takes about `2^33` digest evaluations
  on average in the ideal-hash model. The full seal can detect a deliberate swap when its original
  value is obtained from an independently trusted record that the attacker cannot also replace.
  Neither digest authenticates a container phrase if the attacker can replace both it and the
  reference.

For an adversary who already has the whole container, the digests add no information about the
password: both can be computed from that container, which the deniability experiments already
provide. This argument applies only to a digest of the container. A digest of the password supplies
a cheap password test; a digest of the source or a recovered phrase supplies a check after recovery,
with the composition losses discussed in
[A check for new 24-word and suite 4 sources by choosing the entropy](#a-check-for-new-24-word-and-suite-4-sources-by-choosing-the-entropy).
A digest of settings alone tests the settings, not the password, but can reveal settings that were
intended to remain secret. The container-check format therefore takes only the container as input.

The digests help an adversary who holds a damaged or partial copy by identifying candidate
containers too. The practical number of words that can be repaired depends on their positions, the
checksum length, measured search throughput and the time budget. Five known missing positions can
require `2^55` checksum evaluations when the last word is not among them: even at a hypothetical
billion evaluations per second this is about 1.14 years. A full seal does not make that enumeration
cheap. Once the container is reconstructed, its password protection is the same as for a complete
copy, subject to the existing attack assumptions. Both digests are therefore kept like a copy of the
container. Written next to a container phrase, they also show that the phrase is a special backup
rather than an ordinary one, so by default they belong on a separate card, kept apart from the
container phrase like the repair card, not on the backup itself. The 256-bit seal is as long as the
entropy of a suite 3 container, and longer than that of suite 4: against complete loss, another
exact container copy preserves more useful recovery information.

### Argon2i on the rounds with a public salt

Every round of suites 3 and 4 uses Argon2id. Two calls can have a salt that is computed without the
password: `S_11`, which every recovery derives first from the container's left half, and `S_0` when
the source is known. As [Observers on the same computer](#observers-on-the-same-computer) explains,
an observer who records the data-dependent memory addresses of such a call can reject a guess after
about half a pass of that call: roughly 1/288 of a full guess, or about 8.2 bits, in an idealized
model.

A future suite could use Argon2i in these two calls and Argon2id in all others. Argon2i chooses its
memory addresses independently of the password and the salt [4], so the recorded addresses of the
round-11 call would be the same for every guess. The next call with data-dependent addresses is
round 10, whose salt depends on the output of round 11. In this trace-comparison procedure, each
guess first computes the whole round-11 call before comparing addresses: about `1/12 + 1/288` of a
full recovery's modeled work, or 3.5 bits instead of 8.2. This is a cost estimate for the described
procedure, not a lower bound for every side-channel attack.

The cost lies in memory hardness: data-independent addressing is more exposed to time-memory
trade-off attacks than data-dependent addressing [4]. In a full recovery, making both Argon2i calls
free would leave ten Argon2id calls. Treating calls as equal-cost units gives a reduction of
`log2(12/10)`, about 0.26 bits of work, for that procedure. This does not bound the loss under
cheaper filters, structural attacks or combined time-memory and side-channel attacks. The margin in
the number of Feistel rounds concerns the permutation; it does not prove a minimum guessing cost for
the proposed mixed construction.

Suites 3 and 4 keep Argon2id in every round. The gain applies only when an observer shares the
computer, which lies outside the assumed trusted recovery environment. The specification strongly
recommends a trusted offline computer; that recommendation does not technically prevent shared-cache
observation. The precision that the observer model assumes is speculative; and one function type
throughout keeps implementations and test vectors simple. The rule is recorded for a suite created
for other reasons: calls whose salt can be computed without the password use Argon2i, and the other
calls use Argon2id.

### A second memory-hard function

A future suite could alternate two independent memory-hard functions, for example Argon2id in odd
rounds and scrypt in even rounds. If a shortcut eliminated the evaluation cost of one function while
leaving the other function and the composition sound, a full recovery would retain six costly calls.
With equally costly calls this halves its modeled work, a loss of about one bit. This is not a proof
that the mixed construction survives an arbitrary break of either primitive: cheaper password
filters, shared weaknesses and the composition need separate analysis. Such a hedge could
potentially help copies taken before a weakness became known, whereas later re-encryption cannot
change the protection of an already copied container.

It is not adopted. It needs two engines and two sets of test vectors; scrypt at 2 GiB to 3 TiB runs
into the memory limits of common implementations and of 32-bit builds and is slow in WebAssembly;
and scrypt includes password-dependent memory accesses, so its rounds would add the side channel
described above. Argon2id is a standardized and widely reviewed function [4], [26]. Against a
partial weakness, one more dice word is the simpler hedge: it adds about 12.9 bits, as
[Attacks in the future](#attacks-in-the-future) shows.

### A hidden wallet behind an honest disclosure

This arrangement uses suites 3 and 4 unchanged. Deriving a second wallet from a container with
another password is already possible, as the [Deniability](#deniability) section explains for
decoys. What is recorded here is the reverse assignment of roles: the disclosed password opens the
owner's genuine wallet, and the hidden wallet is the derived one. It is a way of using the
construction, not a new cryptographic primitive.

1. The owner has a wallet `W` in genuine use: its history, exchange withdrawals and tax records
   belong to it.
2. The owner encrypts it with a password `Q` that they are prepared to disclose: `Y = E_Q(W)`, an
   ordinary creation.
3. With a second, strong password `P`, drawn independently, the owner computes `H = D_P(Y)`, read at
   the state width: 24 words in suite 3, the length of `W` in suite 4. `H` is not written down; the
   container and `P` give it again.
4. `H` is funded only from sources linked neither to the owner nor to `W`.
5. Under coercion the owner discloses `Q`. The container and `Q` open `W`, and its history, the
   records tied to it and, for a short suite 3 source, the verifier all agree, because they are
   genuine.

Compared with the decoy of the Deniability section, four of the
[limits of the guarantee](#deniability) fall away: the disclosed password need not be drawn like the
hidden one, the disclosed wallet's history may begin long before the container, records tied to the
disclosed wallet are consistent with it, and a short suite 3 source passes its verifier. The
argument is shorter than that of Theorem 2. `Y`, `Q` and `W` are produced exactly as by an honest
owner and do not depend on `P`, so everything the adversary sees except the record of `H` has the
distribution of an honest disclosure; only a lookup of `H`, reached by finding `P` or directly
guessing the hidden phrase's entropy, or a fixed point can tell the two apart. The expected bound
has the form `k * p_H + l * 2^-b + 12 * (q + 24) * 2^-256 + 2^-b`, where `p_H` is the largest
probability in the distribution of `P` given `P != Q` and `b` is 256 in suite 3 and `ENT` in suite
4; the proof has still to be written and reviewed. The arrangement resembles the hidden volume of a
deniable file system whose outer volume holds genuine data, and the leaks through the operating
system and applications reported for those [48] apply to it as well.

Its limits:

- `H` protects only money that never touches `W` or anything linked to the owner. Moving the
  existing balance of `W` to `H` links the two records.
- `H` depends on the exact container, suite and settings. A new container for `W`, made for example
  to change `Q` or to move to another suite, does not carry `H` over; the specification's
  [application requirements](../README.md#application-requirements) give every user the warning to
  keep the old container, `P` and the settings until the funds of `H` have been moved. Forgetting
  `P` or losing every copy of the old container loses `H` unless its funds were moved first.
- `W` and `Q` give the container again, and with `P` the hidden wallet: `H = D_P(E_Q(W))`. They must
  be guarded like the container.
- `Q` still protects `W` against theft and must be strong if `W` holds funds.
- An application that offers this shows the receiving addresses of `H` once, for funding, and keeps
  nothing. A watch-only wallet of `H` on an everyday device is evidence outside the model.
- Publishing the arrangement raises the probability an adversary assigns to any owner having a
  hidden wallet. The bound does not depend on that probability, but an adversary's behaviour may.

### Check words for derived wallets in the current suites

A full-state wallet derived from a container under another password, `H = D_P(Y)` in suites 3 and 4,
has no verifier for that opening.

**Check words are entirely optional.** The owner need not generate, remember, record or enter them.
Recovery still uses the container, password, suite and settings, with the BIP39 passphrase applied
afterwards if used. Losing the check words does not prevent recovery; declining this option does not
weaken MHFE encryption. They provide only an additional way to compare the recovered seed with a
previously trusted value. Only the usual independent wallet-identity reference confirms the intended
wallet in the specification's sense. A future interface would leave this option off by default,
place it in additional settings and always allow recovery without the check words.

An application could show two English BIP39 words computed from the final BIP39 seed, including the
wallet's passphrase if one is used, under a fixed tag that also binds the suite and word count. The
owner learns them with the password but types them into a separate field; they never enter the
password or Argon2id. They differ both from the public
[container check words](#container-check-words-a-hash-of-the-container-planned), which hash only the
container, and from the private
[password check word](#a-private-check-word-for-generated-passwords), which repairs one forgotten
password word. This proposal's tag, serialization, mapping to words and independent vectors remain
to be defined by an application profile.

- In an ideal-hash model, a distinct wrong seed matches the two words with probability `2^-22`,
  about 1 in 4.2 million. One word gives 1 in 2,048 and suits only a few manual attempts. These are
  consistency checks, not authentication or bounds on every attack.
- With two words, an application could try bounded typing variants, each ordinarily costing one
  recovery. For 100 wrong candidates the union bound is `100 * 2^-22`, about 1 in 41,900; candidate
  dependence does not invalidate that bound when each candidate has the stated marginal estimate.
- The straightforward test recovers a mnemonic once per MHFE password and derives its BIP39 seed for
  each passphrase candidate. Hashing that seed with an independent passphrase included does not
  itself supply a separate mnemonic check. The pair-search term remains as in
  [Composition with the BIP39 passphrase](#composition-with-the-bip39-passphrase). This describes a
  procedure, not a proof that every attack requires full recovery or an optimal Cartesian-product
  search. Hashing the mnemonic entropy instead would provide a separate mnemonic test.
- With or without the words, the result stays labelled not verified in the specification's sense:
  these words are not one of the rehearsal check's wallet-identity references. A match would be
  reported as a 22-bit check-word match. It does not confirm an address, network or derivation path.
  Whether it may support an additional confirmation workflow is a decision for a future profile.
- The words would be remembered or guarded with the password, such as in an heir envelope, never
  with the container. Leaked check words recognize a candidate seed even for an empty wallet.
  Several records linked to one container may also be evidence of several wallets.
- A password invented without computing its recovery does not normally come with matching check
  words. A prepared decoy needs one recovery and seed derivation to learn them. If recovery is
  available, however, any chosen password produces a seed and its own words; a match to a previously
  trusted reference, rather than a newly computed pair of words, is what confirms the intended seed.
  These operational limits do not extend the existing deniability theorems.

### Derived wallets of a chosen length

A separate operation could instead take the first `ENT` bits of the raw recovered state `D_P(Y)` and
encode them with their own BIP39 checksum, without interpreting the rest as a verifier. The
specification does not define that operation: ordinary recovery gives a short reading only where its
verifier matches, whatever length the user states. The following is a candidate application profile,
not a change to either suite.

- Suite 3's 256-bit state supports all five lengths. For suite 4, a prefix reading could only have
  as many entropy bits as the recovered state contains: a 12-word container permits only 12 words, a
  15-word container permits 12 or 15, and similarly for 18 and 21. Longer readings require another
  construction, rather than truncation. The default full-state reading remains the container's
  width.
- A candidate length signal is a password of the form `12:<secret>`, `15:<secret>`, `18:<secret>`,
  `21:<secret>` or `24:<secret>`. In the explicitly selected derived-wallet operation, the program
  would first apply existing password validation and NFKD normalization, then parse the exact ASCII
  prefix from the normalized result. The entire normalized password, including the prefix, would
  enter Argon2id unchanged. The profile would fix one syntax, require a nonempty strong secret,
  reject malformed or unsupported prefixes before Argon2id, and retain the normalized length limit.
  Ordinary MHFE recovery would treat the prefix as literal password text. Codes such as `1:` to `5:`
  are another possible design, not interchangeable spellings of these passwords.
- The prefix signals the length but adds no secret entropy. Each independent wallet needs an
  independently generated secret core. Its complete normalized prefixed password must differ from
  the normalized main password, regardless of settings. If one secret core is disclosed, changing
  only its public prefix or settings does not protect another wallet.
- Prefix readings of one complete password share the first 128 entropy bits: their first eleven
  words are identical and their twelfth words share seven bits. A disclosed 12-word reading reveals
  all 128 bits, leaving only `160 - 128 = 32` unknown bits in its 15-word reading. Searching these
  bits against wallet data needs no further Argon2id work. One complete password must therefore be
  assigned one reading length only.
- A chosen-length reading would be unverified by construction. Confirmation would use an
  independently known wallet-identity reference; the proposed check words could report a weaker seed
  match. A separately generated BIP39 passphrase remains additional protection and must be supplied
  when checking the actual wallet. The main wallet retains its normal source-verifier rules.
- For a hidden suite 3 opening, the candidate profile would refuse a password whose full recovered
  state accidentally passes any short-source verifier, an event of probability about `2^-32` in the
  uniform-state model. This prevents ordinary detection from presenting it as a consistent short
  source. This rule does not apply to suite 4, which has no such verifier. Nor does it apply to
  ordinary decoy preparation, whose password-selection rules must remain those of the stated
  deniability experiment. The refusal conditions the hidden opening's distribution and needs its own
  analysis; the existing theorems do not cover it automatically.
- Such a short hidden reading cannot claim to be the source of the original suite 3 container. In an
  idealized lookup model its entropy-width term would be `l * 2^-ENT` instead of `l * 2^-256`; this
  is a proposed analysis term, not an established extension of the hidden-wallet bound.
- When the complete password is known and only the reading length was forgotten, one recovery
  supplies all prefix readings that fit the state. Comparing all five in suite 3 gives a modeled
  union bound of `5 * 2^-22`, about 1 in 839,000, for wrong check-word matches. If the password's
  length prefix itself was forgotten, each candidate prefix is a different password and requires a
  full recovery; the one-recovery saving does not apply.
- A new container does not carry these wallets over; the specification's
  [application requirements](../README.md#application-requirements) give every user the warning to
  keep the old container until their funds have been moved. Re-encrypting such a wallet as a source
  falls under the specification's rule for a reading without a verifier: the ordinary short-source
  verifier cannot confirm these projections, and encrypting a short projection under its old
  password does not recreate the original container. The specification does not define the proposed
  reading operation.

### Nested containers

A container is itself a valid phrase, so the complete creation procedure can encrypt it again.
Creation with `P_1` produces the inner container; creation with `P_2`, treating that container as
its original seed phrase, produces the outer one. Recovery first uses `P_2` to recover the inner
container, then `P_1` to recover the original seed phrase. The backup shows only the outer
container. When both stages use 256-bit states this is `Y_1 = E_{P_1}(X)` followed by
`Y_2 = E_{P_2}(Y_1)`. With a shorter suite 4 inner container and a suite 3 outer layer, the outer
procedure first packs `Y_1` with its short-source verifier; its raw permutation input is therefore
`Y_1 || V_(256-ENT)(Y_1)`, not `Y_1` alone. Each stage retains its own suite, settings and
fixed-point refusal.

One use is a separation of people. The owner keeps `P_1` and a custodian keeps `P_2`, and neither
learns the other's password. The custodian removes the outer layer on their own offline computer and
returns `Y_1`, and can first check the owner's identity or wait for an agreed period. It gives no
lasting control over spending: once `Y_1` is returned, the owner alone can open the wallet. Nor does
it revoke anything: older copies of the container keep working with the passwords they were made
with.

Two layers do not establish a multiplication of password security. A full recovery performs two
recoveries, while joining two independent password parts into one ordinary password needs one. With
a known original seed phrase and outer container, a meet-in-the-middle attack enumerates inner
passwords forward and outer passwords backward, matching the complete intermediate representation.
Its work is roughly the sum of the full search spaces, but storing the intermediate records needs
memory proportional to one of those spaces; smaller-memory strategies have different costs. This
known-source attack does not establish the same cost for a container-only adversary.

For a suite 4 inner container of 12 to 21 words and a suite 3 outer layer, the outer layer has an
`r = 256 - ENT` bit verifier. This separates the password searches only when false outer matches are
rare. With independently uniform spaces of `N_1` inner and `N_2` outer passwords, equally costly
recoveries `C`, and only a wallet-identity reference for the original seed phrase, a sequential
search has modeled expected work

```text
C * (N_2 / 2 + N_1 / 2 + N_1 * N_2 / 2^(r+1))
```

The last term searches the inner-password space for each false outer match. For two four-word EFF
passwords, `N_1 = N_2 = 7776^4`, false matches are negligible for inner lengths 12, 15 and 18. The
sum of the full spaces is then about `2^52.7`, with expected work about `2^51.7` recoveries, instead
of a full pair space of about `2^103.4`. With 21 words (`r = 32`), about 426,000 false outer matches
precede the correct one on average, and the described sequential procedure instead needs about
`2^70.4` recoveries. These are estimates for specified attacks, not security lower bounds or a proof
of optimality.

A failed outer verifier shows an inconsistency in the outer recovery before the inner password is
used. If no such verifier is available, a final wallet mismatch may leave the failing layer unclear.
The layer order and both sets of settings must remain available, the custodian must retain `P_2`,
and the deniability theorems do not cover layered containers. Threshold sharing of the finished
container, or a multisignature wallet, may serve a custody goal more directly. Seed XOR [56] can
provide an all-shares-required split, but is not a general threshold arrangement.

### A check for new 24-word and suite 4 sources by choosing the entropy

The specification defines the
[optional source profile for new 24-word phrases](../README.md#optional-source-profile-a-recovery-check-for-new-24-word-phrases),
including its exact seed-check bytes, generation and recovery procedure, empty-passphrase option and
public vectors. This section analyses that profile and compares it with entropy-only checks and
possible checks for shorter suite 4 sources; those alternatives are not defined profiles.

**Entropy-only alternative.** A 24-word source and every suite 4 source have no built-in verifier: a
wrong password gives another valid phrase. An application that generates a new wallet could offer an
alternative creation mode that builds a check into the source itself. The generator draws uniformly
random entropy `E` again until `SHA-256(tag || E)` begins with `k` zero bits, for a fixed public
domain tag. In an ideal-hash model this takes `2^k` hash trials on average and leaves approximately
`ENT - k` bits of generation entropy. For `k = 16`, the expected count is 65,536; a 24-word source
retains about 240 bits, while suite 4 sources retain about 112, 144, 176 or 208 bits. This is
hash-only setup work, whose elapsed time needs an implementation-specific measurement. The trials
can be derived deterministically from one random seed, so that a generator fed with dice stays
verifiable. If wrong recoveries are uniform candidate entropies, each passes the check with
probability about `2^-k`; that is a model estimate, not authentication or a proof about every
attack. A recovery of a wallet created in this mode then tells the owner or an heir that the
password or a setting was wrong, without a wallet-identity reference. Suites 3 and 4 do not change:
the container is made from the source as usual, and the check is a property of how the source was
generated. The mode thus gives a 24-word source a recovery filter without stored check words, while
keeping about 240 bits of entropy. Its 16-bit filter is weaker than suite 3's 32- to 128-bit
built-in verifiers for short sources, and the latter do not require conditioning the source entropy.

For a new 24-word wallet, an application may offer the defined seed-check profile as an explicit
choice. An analogous choice for shorter suite 4 sources would require a separate profile and
analysis. The two source-generation approaches compared here are:

1. **An ordinary random phrase**, as today: no meaningful check after recovery (the 16-bit check is
   still evaluated and passes only by chance), the strongest combination with a BIP39 passphrase,
   and the deniability theorems as stated.
2. **A phrase with a source check**: a check after recovery, as a short source has in suite 3, with
   the costs listed below.

The specification requires applications offering the defined profile to explain its trade-offs
before the owner's choice; it also permits offering it only with a nonempty passphrase. Every
implementation evaluates the check on every 24-word reading, with the passphrase the user enters or
the empty one, whether or not it offers the profile, because the container carries no sign of it.
The defined profile uses a check over the seed with `k = 16`, with the wallet's BIP39 passphrase or
the empty string when the wallet has none. Its recommended use with a strong, independent passphrase
is explained in the specification. The following comparison first considers the entropy-only
alternative, then the check over the seed.

The costs of the entropy-only alternative:

- **BIP39 passphrase.** Like the built-in verifiers of short sources in suite 3, this alternative
  filters MHFE password guesses without a BIP39 passphrase; the filter widths and generation costs
  differ. Without a passphrase and with an identifiable public wallet history, a candidate phrase
  can already be compared with that history, and both comparisons are negligible beside the Argon2id
  work of a guess. With an independent passphrase, the check filters MHFE password guesses
  separately, and the pair search is no longer a product: in the example of
  [Composition with the BIP39 passphrase](#composition-with-the-bip39-passphrase), the expected time
  falls from about 12,195 years to about 17.2 years with `k = 16`, close to the roughly 17.0 years
  for a 12-word source. Roughly 8,192 false mnemonic matches still require their own passphrase
  searches, adding about 68 days beyond the MHFE password search in that model; the costs do not
  separate completely. A 24-word source created without the mode keeps the strongest combination
  with a passphrase; with the check over the seed described below, the search still runs over pairs.
- **Decoys.** If the adversary knows that this source profile was used, a recovered decoy must
  satisfy it too. The described independent password search takes about `2^k` recoveries on average:
  about 53 days at `k = 16` if run sequentially at the measured 70-second recovery time on the
  reference laptop, and about five hours at `k = 8`, where a wrong password passes once in 256. This
  is neither a fixed completion time nor a lower bound on every way to prepare a decoy. Both
  conditioning the source entropy and selecting a decoy by its recovered phrase change the
  assumptions of the existing theorems. Those theorems do not establish deniability for this mode;
  that would need a separate experiment and proof.
- **Recognition.** For a fixed MHFE-specific tag, a passing source is statistical evidence of
  preparation, not proof of provenance: an ordinary uniformly random source passes with probability
  about `2^-k` too.
- **New wallets only.** An arbitrary existing source cannot be made to satisfy this fixed predicate
  without changing its mnemonic and wallet, although it may already pass by chance. A recovery tool
  can always report whether the recovered phrase passes; a failure indicates a wrong input only for
  a wallet created in this mode.

**A check over the seed with the passphrase.** With a BIP39 passphrase, the check can instead be
computed over the BIP39 seed that the phrase and the passphrase give together: the generator draws
`E` again until a digest of the seed begins with `k` zero bits. The owner then gets a check after
recovery of the MHFE password, the settings and the passphrase together. A pass is statistical
evidence, not proof: a wrong password or passphrase passes with probability about `2^-k`, about one
in 65,536 at `k = 16`, and a pass never identifies the wallet. A failure means something only for a
wallet created with this check.

In the search described under
[Composition with the BIP39 passphrase](#composition-with-the-bip39-passphrase), a password guess
can be tested only together with a passphrase guess, because the check needs both. That search still
runs over pairs, as without any check, and its modeled expected time in that example stays at about
12,195 years instead of falling to about 17.2 years. This describes that procedure, not a lower
bound on every attack. Testing a pair costs about as much as comparing it with the wallet's
addresses. Without a passphrase, this variant filters MHFE password guesses alone, like the check
over the entropy. Its own costs:

- For a given passphrase, about `ENT - k` bits of entropy remain: about 240 of 256 for a 24-word
  phrase at `k = 16`.
- Each trial at creation needs one PBKDF2-HMAC-SHA512 with 2,048 iterations, about 0.76 ms on one
  core of the reference laptop in a quick measurement, so `k = 16` takes about a minute on average
  on one core and `k = 12` a few seconds; a browser is slower. This is not a promised completion
  time.
- The passphrase is fixed at creation: changing it normally loses the check, though another
  passphrase can pass by chance or after a search.
- Another passphrase normally fails the check, but anyone who searches for a passphrase that passes
  with a given phrase finds one after about `2^k` trials. A decoy passphrase is therefore a separate
  strategy, and the check neither rules one out nor makes one safe.
- If the adversary knows that this profile was used, a disclosed decoy must also pass with its
  disclosed passphrase. For a fixed decoy passphrase, the described independent MHFE password search
  takes about `2^k` recoveries on average; this is not a lower bound on every preparation strategy.
- The deniability theorems assume a uniformly random phrase. They do not by themselves cover a
  phrase drawn to pass this check; that would need a new experiment or proof.
- For a wallet with a nonempty passphrase, the check gives a meaningful result only when that
  passphrase is entered with it. The empty-passphrase variant needs no second secret and offers only
  the MHFE password's protection, with no BIP39 passphrase layer.

**Relation to suite 3's short-source checks.** With the empty passphrase, the profile gives the
owner and the attacker a recovery filter without a wallet-identity reference, as do suite 3's
built-in verifiers. This is the shared convenience, not an equivalence of strength or cost: the
profile uses 16 bits, conditions the source entropy and requires a seed search at creation. Its
exact definition and recommended use are in the specification, rather than repeated here.

The entropy-only and shorter-source alternatives would each need their own profile. For wallets
created without a check, a trusted reference for the actual wallet confirms recovery without
restricting the source's entropy. When a BIP39 passphrase is used, that reference must be derived
with the same passphrase to preserve the composition comparison; a reference derived without it
would itself supply a separate mnemonic check.

### A private check word for generated passwords

The specification now defines this rule as the optional profile
[MHFE-PASSWORD-CHECK-1](../README.md#optional-password-check-word-mhfe-password-check-1), with five
words and a check word only; the analysis below explains its choices. A generator draws five words
independently and uniformly from the EFF large list [6] and appends a private check word. For word
indexes `d_1` through `d_5` from 0 to 7,775, the defined rule is

```text
c = (d_1 + 5*d_2 + 7*d_3 + 11*d_4 + 13*d_5) mod 7776
```

The specification fixes the list ordering, coefficients and exact password serialization for this
profile. The full string, including the sixth word, is the MHFE password. Since each coefficient is
coprime to 7,776, any single substitution by a different list word is detected, and one erased word
at a known position is recovered uniquely from the remaining words. This includes recovery of the
check word when only that word is missing. A single substitution at an unknown position cannot be
corrected uniquely: each position admits a possible repair.

Transpositions are not always detected. For independent uniform data words, swapping positions with
weights `u` and `v` passes with probability `gcd(u-v, 7776) / 7776`, including swaps of identical
words; conditioned on different words, it is `(gcd(u-v, 7776)-1) / 7775`. With the profile's
weights, adjacent data-word swaps therefore pass with probabilities `3/7775`, `1/7775`, `3/7775` and
`1/7775` when the words differ. The check-word position has coefficient `-1`, so its exchange with
the preceding word uses the weight difference 14 and passes with probability `1/7775` under the same
condition. These are averages for random words, not measured human-error rates; exchanging indexes 0
and 1944 at the first two positions is a concrete undetected swap.

The generation entropy remains `5 * log2(7776)`, about 64.6 bits. The check word adds redundancy,
not randomness, and adds a word to remember. It must remain secret: publishing it removes one word's
worth of uncertainty, about 12.9 bits. Passing this check confirms the password's form, not that it
opens the intended container. Recovery still needs the exact password form and the usual verifier or
wallet-identity reference. Decoy passwords must follow the same generation and selection rules. The
profile changes neither suite's password encoding.

The profile does not define six random words with a seventh check word: such a variant would give
about 77.5 bits, the length EFF itself suggests [6], but it would need its own coefficients, because
with a fifth coefficient of 13 the sixth cannot keep both of its neighbouring transpositions as rare
as above. This password check is separate from the
[check words for derived wallets](#check-words-for-derived-wallets-in-the-current-suites): those
compare the recovered seed with a previously trusted value, while this one shows only that the typed
words fit together. A check word computed from the wallet would not provide the same cheap, unique
password repair: testing one missing word could require up to 7,776 expensive recoveries, and the
checksum rule would no longer establish a unique answer.

### Alternative formats for multiple password openings with recovery checks

The question is whether one checksum-valid, 24-word BIP39 container can support several different
passwords, each opening a wallet and passing an internal recovery check. This is a natural research
question next to MHFE: it keeps the physical backup constraint and addresses the lack of a verifier
for additional full-width openings. The proposals below replace the construction rather than extend
the algorithms of suites 3 and 4. They have no assigned suite identifier, conformance vectors or
reviewed implementation; the MHFE security arguments and deniability theorems do not apply to them.

#### Shared constraint and password-derived wallets

A 24-word BIP39 container has 256 payload bits; its eight checksum bits are determined by that
payload [3]. One candidate layout is a fresh public salt `S` of 64 bits and a coded record `Z` of
192 bits. For each password, Argon2 derives key material. HKDF with separate context labels could
derive the masks, equation coefficients, verification keys and wallet outputs [62]. The eventual
format would bind the role, word count and settings into the relevant derivations and checks.
Independent access requires independently generated strong passwords; changing only a public role
prefix does not isolate wallets if their random password core is reused.

An arbitrary existing 12-word wallet requires 128 bits of source entropy. Three recovery checks of
16 bits each give the illustrative information budget `64 + 128 + 3*16 = 240`, leaving 16 bits
beyond those constraints. This budget alone does not establish that an encoding always exists. Two
arbitrary existing 12-word wallets already require 256 bits at fixed independent passwords, leaving
no room for this salt and checking budget.

An additional wallet need not store its entropy. It can instead be computed from its own password
and `S`, with a distinct wallet-output context, and encoded as 12, 15, 18, 21 or 24 BIP39 words. For
example, one existing 12-word wallet and two newly derived 24-word wallets need not store another
512 bits. The record confirms the intended opening, while the derived wallet can be recovered
without that record if the password, salt and derivation profile survive. Losing the salt loses this
property; changing it changes the derived wallets. A longer output does not create additional secret
entropy: with public `S`, password guessing remains a recovery route. A 16-bit check is only a
consistency filter, with a modeled accidental acceptance probability of `2^-16`, not authentication
or a guarantee of wallet identity.

#### Affine equations and Gaussian elimination

For opening `i`, password-derived coefficients and a separately derived offset could impose
equations over `GF(2)` of the form

```text
A_i * Z = b_i XOR payload_i
```

For the existing wallet, the payload includes its entropy and check bits. For a password-derived
wallet, only the check constraints need to be encoded. Stacking the equations and solving them by
Gaussian elimination avoids an exponential search. With one 128-bit stored wallet and three 16-bit
checks, the illustrative system has 176 equations on 192 unknown bits. If the rows are independent,
it has 16 free variables, which are sampled uniformly. Independently pseudorandom offsets are
essential: homogeneous checks alone would accept an all-zero record for every password.

Linear oblivious key-value stores (OKVS) provide a relevant foundation [63]. Section 2.1, Definition
2 compares encodings of two key sets of the same cardinality with uniformly random values. Section
2.2 explains how uniformly random right-hand sides and uniform sampling of a full-rank linear
system's solutions yield a uniform encoding. Thus linearity is compatible with formal key hiding,
and this route is a reasonable first candidate for a prototype and proof. It is not necessary to
invent a new block-cipher primitive to investigate it.

The proposed application is not already covered by that definition. Its checks have known expected
values, an existing wallet can be fixed, and a disclosure reveals correlated password and wallet
information. Separate offsets might mask these payloads into pseudorandom right-hand sides, but
their independence from the coefficients needs an explicit assumption. Hidden numbers of openings,
rank failures and retry rules, and security after disclosures need a separate experiment. A useful
proof target is that, after specified openings are disclosed, the record's distribution is
independent of additional undisclosed openings. Several records sharing a salt and constraints may
reveal their common affine subspace; affine combinations can also preserve checks. Single-record
uniformity therefore establishes neither security for several versions nor authentication. If every
valid container necessarily contains a stored main wallet, disclosing a visibly derived opening
would itself reveal that another opening exists. A deniable format would therefore also need to
permit an honest container without an undisclosed stored main wallet.

#### XOR masks and nonlinear HMAC checks

A comparison candidate derives separate XOR masks and HMAC keys after the expensive password KDF. In
the simplest 12-word sketch, the raw block is `E_i || U_i || T_i`: 128 bits of wallet entropy, 48
bits of free padding and a 16-bit tag. A candidate check is

```text
T_i = Trunc_16(HMAC-SHA-256(V_i, domain || S || E_i || U_i))
Z = (E_i || U_i || T_i) XOR Mask_i
```

The existing wallet `E_1` is held fixed. Its tag is computed for each trial padding, and the same
record is tested under the other passwords. Once keys are derived, this search uses HMAC rather than
another Argon2 call per trial. For `n` total openings and `t`-bit tags, independent ideal check
functions suggest `2^((n-1)*t)` trials on average. With three openings, `t = 16` and a 48-bit tail,
this is `2^32` candidates and an expected `2^16` solutions. Each candidate needs at least two HMAC
evaluations; later checks can be skipped after an earlier failure. These estimates are
model-dependent and do not guarantee a completion time or prove a lower bound on every method.

In this original sketch, another wallet's entropy is determined by `E_1` and the mask difference;
varying the padding does not let the owner select an arbitrary second existing wallet. The sketch
also does not automatically give a 24-word wallet or one recoverable from the password and salt
alone. Adding the separate wallet-output derivation described above requires its own definition of
roles, checking and decoding. HMAC's nonlinearity does not by itself prove greater security than
affine coding. The search must avoid a publicly recognizable padding rule, and the resulting record
distribution needs analysis. Reusing the same salt and password mask to encrypt different raw
payloads exposes their XOR; changes and retained versions need explicit rules.

#### A worked research sketch of the affine route

A design-and-attack exercise on 2026-10-05 developed the affine route into a detailed research
sketch, called MHFE-MW here. Three AI-assisted review passes within the same exercise attacked an
earlier version, and a revision addressed their findings. The intended development is a separate
program and publication, with its own format and analysis. It would not be integrated into MHFE or
added as a suite of the current specification. This outline records the research; it is not an
interoperable format definition or an expert-reviewed construction.

- **Layout.** The 256 bits hold 54 bits of public salt material `S`, a 10-bit tweak `T` and 192 bits
  `Z` solved over `GF(2)`. The exact serialization and the salt bytes passed to Argon2 still need a
  complete definition.
- **Nominal recovery work.** The sketch derives a key through twelve sequential Argon2id calls with
  the suite 3 work parameters, using salts derived from `S` and prior outputs. Ordinary recovery
  therefore has the same nominal call count and profile as suite 3. This is not a lower bound on
  every password test or a claim of equal cryptographic security: suite 3's state-derived salts and
  its known-pair filter differ from this chain. One candidate chain can serve the cheap tests of all
  opening roles. With `w` independent passwords from the same uniform space, an attack seeking any
  one of them can gain about `log2(w)` bits compared with one target: about 2.6 for six and 3.6 for
  twelve. These are conditional multi-target estimates, not general security deductions. The first
  call has a public salt; the trace-comparison procedure under
  [Observers on the same computer](#observers-on-the-same-computer) gives about 8.2 bits of modeled
  work reduction, or 3.5 bits if that call uses Argon2i and the next uses Argon2id. Neither estimate
  bounds all side-channel attacks.
- **Salt and reuse.** Independent uniform 54-bit salt material has a birthday collision scale near
  `2^27` containers. At a fixed password and settings, versions or containers sharing `S` reuse the
  same expensive chain; changing `T` alone does not restore separate KDF work. This needs analysis
  alongside deliberate salt retention when preserving derived wallets.
- **Rows and checks.** Password-derived, domain-separated material and `T` select equation rows and
  offsets. Each opening has a `t_H`-bit header encoding its role and word count. If a wrong opening
  produces a uniform header in the model, seven accepted codes give probability `7 * 2^-t_H` per
  trial. This is consistency checking, not authentication. For `Q` wrong trials the union bound is
  `Q * 7 * 2^-t_H`, capped at 1; automatic searches need a stated budget and must not silently
  choose one of several survivors.
- **Check size and capacity.**
  - With `t_H = 32`, a modeled wrong opening passes about once in 614 million, or `2^-29.2`, seven
    times more often than a single 32-bit check. A million independent wrong trials give about
    0.163% probability of a false match. A pass does not establish wallet identity. The capacity
    budget permits one stored 12-word wallet and one derived wallet, one stored 15-word wallet, or
    six derived wallets.
  - With `t_H = 16`, the per-trial estimate is about 1 in 9,400; a thousand independent wrong trials
    give about 10.13% probability of a false match. The capacity budget permits one stored 12-word
    wallet and three derived wallets, one stored 15-word wallet and one derived wallet, or twelve
    derived wallets. This later parameter choice was not examined by the earlier review passes.
  - The maxima are full-rank capacity limits with no free solution bits. A stored wallet of 18 to 24
    words does not fit either layout. Both check sizes require a defined search limit and an
    independent wallet-identity reference when confirmation of the intended wallet is needed.
    Written references linked to hidden wallets may be external evidence; remembering them or
    guarding them separately has different operational costs.
- **Rank and version selection.** A uniform square binary matrix of this size has full rank with
  probability about 0.2888, so the capacity limits require retries. The sketch proposes evaluating
  all 1,024 tweaks in eight classes of 128, selecting a usable class cyclically from a start class,
  and a full-rank tweak within it by a priority derived from the owner's dice. Creation would choose
  the start class from the dice; an update would start after the current class. A first-
  successful-tweak rule in a publicly fixed order can leak the layout: an almost-surely full-rank
  layout selects the first tweak, whereas a square system does so with probability about 0.2888, a
  difference near 0.711. The proposed class rule needs fully defined ordering, ties, exhaustion and
  class-reuse behavior. The claimed eight-version guarantee is a proof target, not established by
  this summary.
- **Covert-channel mitigation.** A dishonest encoder can choose a salt or solution so that a public
  function of the container reveals a password hash tag, enabling a cheap filter before Argon2. The
  proposed mitigation makes all random choices reproducible from at least 50 fresh, private rolls of
  the owner's fair six-sided dice, about 129.25 bits of input entropy. The canonical generator,
  salt-retention rules, equation ordering, priorities and solution sampling must all be fixed. A
  trusted implementation from an independent source must reproduce the entire container from the
  same inputs; checking the funding addresses with it also guards output substitution. Matching
  results do not establish that either program retained no secrets or that a shared computer was
  trustworthy. Retained dice can help distinguish additional openings by reproducing a
  disclosed-only encoding, so their retention and disclosure need analysis. Erasing the record
  cannot undo a copy already made by compromised software.
- **Passphrase protection.** For new wallets, the intended separate application's profile would
  require a strong BIP39 passphrase generated independently of the opening password before funding.
  Finding the mnemonic would then still leave that passphrase to guess. An existing wallet keeps its
  original BIP39 passphrase: adding or changing one creates a different wallet and requires
  migration. The header supplies an early opening-password filter, so protection need not equal a
  product of the two search spaces. In a full-space search containing `w` genuine openings and
  `N_wrong` wrong passwords, let `N_P = w + N_wrong`. Assuming equally sized passphrase spaces, a
  straightforward procedure is modeled by `N_P * C_chain + (w + 7*N_wrong/2^t_H) * N_Q * C_BIP39`:
  false survivors also require passphrase searches. This is a procedure estimate, not an
  optimal-attack bound. Separated search does not remove the passphrase's protection against
  disclosure of the mnemonic itself.
- **Disclosure and changes.** A password invented without preparation normally fails the header;
  accepted accidental openings can be searched for, and credible wallet history still needs
  preparation. Demonstrating a custom MW opening identifies its use, but a password alone does not
  prove the format or another hidden opening. A header match is not certain identification of a
  correct hidden password. Ordinary re-encoding that preserves chosen openings needs their
  constraints, derived within a trusted workflow; passwords may be supplied sequentially rather than
  simultaneously. Retaining derived constraints instead creates sensitive recovery data. If `S`
  changes, all wallets derived from it change even if their passwords do not.
- **Partial loss.** With the password, settings and profile known, a derived wallet can be computed
  from `S` alone. Knowing container words 1 to 3 exposes 33 of its 54 bits, leaving at most `2^21`
  salt candidates for the described chain search. For a known stored 12-word role with a 32-bit
  header, four missing words wholly within `Z`, at known positions, leave about 16 candidates after
  header and BIP39-checksum constraints in the ideal model; that estimate assumes the relevant
  constraint ranks and is not guaranteed unique recovery. Once its password chain is derived, these
  candidate tests need no further Argon2 calls, unlike the repair of a suite 3 container without an
  MHFE-REPAIR-1 card, where each remaining candidate needs a full recovery. The first five words
  cover all of `S`; losing every recoverable copy of that salt removes password-only recovery of
  derived wallets. Another verified backup can preserve them.
- **Status and prior art.** The earlier review exercise reported no attack on its modeled core but
  found serious operational issues, including the covert channel. No independent cryptographer has
  reviewed the revision. The exercise proposed a residual deniability estimate near `2^-45` for
  `2^80` BLAKE2b queries, excluding hidden-password guesses, with fresh erased dice, independent
  passwords, explained changes and an appropriate honest-owner comparison. That estimate and the
  eight-version claim remain unverified here: this document contains neither their complete game and
  generator nor their proof. Fifty rolls alone do not establish either bound, and the model must
  also cover rank selection, conditioned layouts and disclosures. The first steganographic
  file-system construction of Anderson, Needham and Shamir [64] stores files as password-selected
  XOR combinations, adds them by solving linear equations and permits partial disclosure. Linear
  OKVS [63] give related formal hiding definitions, not a proof of this wallet application. Aezeed
  [55] already stores salt and a password-checked seed using 24 words from the BIP39 list with a
  different encoding. A limited literature search does not establish novelty.

Both routes need a complete format, independent vectors and analysis of password guessing, salt
collisions and reuse, multiple disclosures, and records of funded wallets. The 64-bit salt and
16-bit checks of the first two sketches are capacity examples, not recommended security parameters,
and the worked sketch's sizes are not frozen either. Its stored salt material has only 54 bits of
diversity. RFC 9106's allowance for a 64-bit salt under space constraints [4] concerns byte-string
length, not the safety of this distribution or the new construction. Neither that comparison nor
collision estimates establish its security. These alternatives are recorded to investigate the
trade-offs without changing current MHFE recovery or claiming that a new construction is ready to
protect funds.

## References

Citation numbers refer to the single reference list of the specification,
[`README.md`](../README.md#references). Numbering follows first citation in the specification, then
first citation of additional sources in this supplement; previously cited sources retain their
numbers.
