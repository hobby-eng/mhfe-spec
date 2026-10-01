# MHFE: Memory-Hard Feistel Encryption for BIP39 Mnemonics

<p align="center">
  <img src="assets/mhfe-mascot-v3.png" alt="MHFE penguin mascot guarding a mnemonic backup plate" width="240">
</p>

<p align="center"><sub>The penguin lives in the cold, like the backups MHFE is made for. It holds a
steel plate with 24 words and waddles from side to side, much as a Feistel network swaps its two
halves in every round.</sub></p>

**Archived version 0.4.0:**
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23074882.svg)](https://doi.org/10.5281/zenodo.23074882)

> **MHFE specification version 0.4.0, experimental suite 3 (`MHFE-BIP39-256-EXPERIMENTAL-3`).**
> Released as [v0.4.0](https://github.com/hobby-eng/mhfe-spec/releases/tag/v0.4.0) and archived
> under DOI [10.5281/zenodo.23074882](https://doi.org/10.5281/zenodo.23074882). Suite 3 is
> implemented in version 0.4.0 of the reference implementation. Its current public test corpus is in
> [`vectors/suite3/`](vectors/suite3/), with full-cost independent replay, input-validation
> coverage, provenance and verification limits recorded there. The previous version 0.3.0, which
> defines suite 2, is available as a
> [tagged release](https://github.com/hobby-eng/mhfe-spec/releases/tag/v0.3.0) with its
> [DOI](https://doi.org/10.5281/zenodo.22902450).

```
  BIP: ?
  Layer: Applications
  Title: Memory-Hard Feistel Encryption for BIP39 Mnemonics
  Authors: Sergei Semenov <mr.ssv@protonmail.com>
  Status: Draft
  Type: Specification
  Assigned: ?
  License: CC-BY-4.0
  Version: 0.4.0
  Requires: 39
```

This document is the specification of MHFE suite 3, `MHFE-BIP39-256-EXPERIMENTAL-3`. It uses the
format of Bitcoin Improvement Proposals [7], [8]. Detailed analysis, security arguments, cost
estimates, related work and research alternatives are collected in the supplement
[`docs/DESIGN-NOTES.md`](docs/DESIGN-NOTES.md).

## Contents

- [Abstract](#abstract)
- [Motivation](#motivation)
- [Conventions and Terminology](#conventions-and-terminology)
- [Specification](#specification)
- [Rationale](#rationale)
- [Backward Compatibility](#backward-compatibility)
- [Security Considerations](#security-considerations)
- [Reference Implementation](#reference-implementation)
- [Test Vectors](#test-vectors)
- [Appendix: Suite 2](#appendix-suite-2)
- [AI Assistance and Acknowledgments](#ai-assistance-and-acknowledgments)
- [Changelog](#changelog)
- [Copyright](#copyright)
- [References](#references)

## Abstract

MHFE turns an existing 12-, 15-, 18-, 21- or 24-word BIP39 mnemonic [2] into a password-protected
24-word container that is itself an ordinary, checksum-valid BIP39 mnemonic. With the password, the
container is turned back into the exact original mnemonic, so the wallet, its addresses and any
BIP39 passphrase stay unchanged. No salt or metadata is stored in the container.

The source is packed into a 256-bit state whose free bits, for a short source, hold a recovery
verifier. The state is transformed by a 12-round balanced Feistel permutation. Every round derives
its key with Argon2id [13], using 2 GiB of memory by default and a salt of its own, computed from
the half of the Feistel state that the round leaves unchanged, the round number and the chosen
settings. Salts of containers made from independently generated sources therefore differ except with
negligible probability. Each round depends on the result of the previous one, so a recovery performs
twelve memory-hard calls in sequence. For a short source, no practical way is known to screen a
password guess against the container alone with fewer calls; a 24-word source has no internal check,
and confirming a guess needs external information such as a known address. MHFE is designed for cold
storage and is experimental: it has not been independently reviewed and must not be used to protect
real funds.

## Motivation

**A password to remember and a backup on the usual media.** Without MHFE the phrase itself is the
secret: it must be hidden, or learned by heart as 12 to 24 words in their exact order. With MHFE the
owner remembers a password instead, and the container, a valid 24-word BIP39 phrase, goes on the
same paper or metal backup, such as a Cryptosteel capsule that holds a fixed number of words [1].
Reading or photographing the container does not directly reveal the original mnemonic, so it needs
less secrecy than the original, but it must not be published: anyone who has it can try passwords
offline. The password must therefore be strong and independently generated, for example at least
four, better five, words chosen with dice from a published list such as the EFF large wordlist [42];
the estimate below shows what such a password costs an attacker.

**Protection of the phrase itself, alongside a BIP39 passphrase.** A BIP39 passphrase changes the
wallet derived from a phrase; it does not hide the phrase. Anyone who reads the phrase holds the
wallet unless a passphrase is used, and a passphrase is protected only by a fast key derivation.
MHFE encrypts the phrase itself with a memory-hard derivation, so each guess of its password is far
more expensive, as shown below. The two combine: the original phrase is recovered with MHFE first,
and the passphrase is then used as before.

**Nothing changes in the wallet.** MHFE encrypts the phrase the user already has. No funds move, and
hardware wallets need not support MHFE: after recovery the original phrase is entered through their
normal recovery procedure.

**Plausible deniability through decoy wallets.** The container is itself a valid BIP39 phrase and
can serve as a decoy wallet; nothing in its words shows that MHFE was used. A different MHFE
password also yields a valid phrase, read as 24 words, which like every 24-word result has no
internal check and stays unverified unless the user supplies a reference to its wallet; the
permutation for that password maps the phrase back to the same container. Its wallet can be funded
and used beforehand, providing a working alternative disclosure even when MHFE use is known. The
[supplement](docs/DESIGN-NOTES.md#deniability) analyses this in a stated model and, under the
conditions stated there, bounds the adversary's advantage in telling such a disclosure from an
honest one by essentially the probability of guessing the real password; the analysis has not been
independently reviewed. A second password does not convince an adversary who knows that the original
has fewer than 24 words.

**Slow on purpose, for cold storage.** A container is created once and recovered rarely, perhaps
years later, on a trusted offline computer. Each operation therefore deliberately needs 2 GiB of
memory by default. On the reference laptop a recovery takes about one to two minutes natively, and a
creation, which ends with a full recovery as its check, about twice as long; both take longer in a
browser without threads. An attacker repeats the work for each password tried. Two optional settings
raise the cost further as hardware improves, without changing the format.

**Why not simply a longer passphrase?** A longer passphrase helps and can be combined with MHFE, but
it cannot protect the phrase, cannot be added to an existing wallet without moving funds, and each
of its guesses is cheap. The difference can be measured in bits of password strength, where each bit
doubles the number of guesses an attacker has to try:

- A BIP39 passphrase uses PBKDF2 with 2,048 iterations; the supplement's cost model uses roughly 1.5
  million candidates per second, extrapolated from a generic PBKDF2 graphics-card benchmark [45],
  not a measured complete wallet attack.
- One MHFE guess performs twelve Argon2id calls with 2 GiB each; the model assumes roughly one
  candidate per second for the comparison. This MHFE graphics-card rate has not been measured.

One MHFE guess therefore costs about 1.5 million, or about `2^20`, times as much: in this model the
same password is about 20 bits more expensive to find, although its entropy does not change. A
random word from a 7,776-word dice list carries about 12.9 bits, so this equals roughly one and a
half extra words. For example, at those assumed rates, a password of four random words would take
about 39 years to find as a BIP39 passphrase, but about 58 million years as an MHFE password, on
average. These are order-of-magnitude estimates at the default settings, with their assumptions in
the [supplement](docs/DESIGN-NOTES.md#what-a-guess-costs); a higher PIM or memory level adds more.

The problem itself is not new: in 2021 a Bitcoin Stack Exchange question asked how to encrypt an
existing mnemonic into another mnemonic [3], and the linked prototype reused one AES-CTR keystream
for every mnemonic encrypted under the same password [4], although CTR mode requires that counter
blocks never repeat under one key [23]. MHFE aims at a reviewed, interoperable answer with a
memory-hard KDF and test vectors.

## Conventions and Terminology

The key words **MUST**, **MUST NOT**, **REQUIRED**, **SHALL**, **SHALL NOT**, **SHOULD**, **SHOULD
NOT**, **RECOMMENDED**, **NOT RECOMMENDED**, **MAY** and **OPTIONAL** are to be interpreted as
described in BCP 14 when, and only when, they appear in all capitals [5], [6].

Sizes are in bits unless stated otherwise; Argon2id memory is in KiB, as in RFC 9106. Bit offsets
count from the most significant bit of the first byte, and bits `Z[8j:8j+8]` form byte `j`. Digests
keep their standard byte order; `Trunc_n(Z)` is the leftmost `n` bits of `Z`, read most significant
bit first as in BIP39 checksum extraction. `BE32(v)` is the unsigned 32-bit big-endian encoding of
`v`, `||` is concatenation and `XOR` is bitwise exclusive-or. Implementations MUST NOT use host byte
order, hexadecimal text, mnemonic words or string terminators at any cryptographic boundary.

| Symbol              | Meaning                                                                   |
| ------------------- | ------------------------------------------------------------------------- |
| `E`, `ENT`          | source BIP39 entropy and its length: 128, 160, 192, 224 or 256            |
| `r`, `V_r`          | verifier length `256 - ENT` and verifier `Trunc_r(SHA-256(E))`            |
| `X`, `Y`            | 256-bit packed state `E \|\| V_r` and encrypted state (container entropy) |
| `P_enc`             | normalized UTF-8 password                                                 |
| `PIM`, `MEM`        | pass multiplier `0..1023` and memory level `0..21`; omitted means `0`     |
| `L_i`, `R_i`        | 128-bit halves before round `i`; `L_12`, `R_12` are the final halves      |
| `S_i`, `K_i`, `M_i` | round salt (128), Argon2id output (256), round mask (128)                 |
| `Perm`, `Perm^-1`   | forward and inverse permutation for one password, PIM and memory level    |

## Specification

### Suite parameters

| Component                        | Value                                                       |
| -------------------------------- | ----------------------------------------------------------- |
| Suite identifier                 | `MHFE-BIP39-256-EXPERIMENTAL-3` (ASCII, case-sensitive)     |
| Wordlist                         | English BIP39 wordlist, for source and container            |
| State                            | 256 bits, balanced Feistel with two 128-bit halves          |
| Rounds                           | 12                                                          |
| Salt hash                        | BLAKE2b with a 256-bit digest [11], truncated to 128 bits   |
| KDF                              | Argon2id version 1.3 (`0x13`), 4 lanes, 256-bit output [13] |
| Argon2id memory                  | `m(MEM)` KiB, 2 GiB by default (see Work factor)            |
| Argon2id passes                  | `t(PIM) = 12 * (PIM + 1)`, 12 by default                    |
| Argon2id secret, associated data | empty                                                       |
| Round mask                       | HMAC-SHA-256 [9], [12], truncated to 128 bits               |
| Recovery verifier                | SHA-256 [9]                                                 |

```text
SUITE_ID = ASCII("MHFE-BIP39-256-EXPERIMENTAL-3")
DS_SALT  = SUITE_ID || ASCII("/ROUND-SALT")
DS_MASK  = SUITE_ID || ASCII("/ROUND-MASK")
```

The strings have no terminating NUL. These values are frozen; only the PIM and the memory level can
be chosen by the user.

The container has no room for a version field, and nothing in it identifies the suite: recovering a
container under the wrong suite gives a different valid mnemonic, with no error at all for a 24-word
source. Applications MUST therefore show the suite identifier when they create a container. If the
PIM or the memory level differs from its default, applications SHOULD offer the user to record it,
because recovery needs exactly the same value. With the default settings nothing besides the
container and the password needs to be kept: the suite is fixed by the software that implements it,
and the source length is detected automatically, except in the rare case described in step 2 of
Creating a container. For long-term storage, users SHOULD also keep an offline copy of a release of
compatible software. Any incompatible change to the geometry, round count, packing, password
encoding, salt or mask derivation, Argon2id parameters or the range or mapping of either setting
MUST use a new suite identifier and therefore new domain strings. Implementations MUST NOT reuse an
identifier for a changed definition or silently substitute one suite for another.

### Password encoding

The MHFE password and the optional BIP39 passphrase are different secrets and MUST NOT be
substituted for one another. The password `P` MUST be a well-formed sequence of Unicode scalar
values and is encoded as `P_enc = UTF8(NFKD(P))`, using the Normalization Process for Stabilized
Strings of UAX #15 [41] with the Unicode 17.0.0 character database: normalization MUST fail if `P`
contains a code point with `General_Category=Unassigned` (`Cn`) in Unicode 17.0.0. This includes the
noncharacters, such as U+FDD0; Private Use characters are assigned and accepted. `P` MUST NOT
contain a control character (`General_Category=Cc`, for example U+0000 NUL, U+0009 TAB, U+000A LINE
FEED, U+000D CARRIAGE RETURN and U+0085), U+2028 LINE SEPARATOR or U+2029 PARAGRAPH SEPARATOR, and a
password that contains one MUST be rejected, never cleaned. The check applies to `P` before
normalization; NFKD maps no other character to any of them, so it holds for `P_enc` as well. This is
a compatibility rule, not a strength rule: excluding controls and line separators avoids common
line-ending and input-control problems. Other valid Unicode characters can still be invisible or
require suitable input and display support. Implementations MUST NOT apply case folding, trimming or
any other transformation. `P_enc` MUST contain 1 to 1024 bytes; longer or empty results MUST be
rejected before any Argon2id call, never truncated. Recovery MUST accept every password that is
valid under these rules, whatever strength policy an application applies at creation.

### Reading words

When reading a source mnemonic or a container, implementations SHOULD ignore letter case and extra
whitespace and SHOULD accept words abbreviated to their first four letters, because metal backups
often store only those letters [1]. Each input word is then resolved as follows: if it equals a word
of the English list, it is that word; otherwise, if it has at least four letters and is the
beginning of exactly one word, it is that word. Anything else MUST be rejected. The first four
letters identify every word of the list uniquely [2], but some three-letter words, such as `act`,
also begin longer words, which is why an exact match comes first. Applications SHOULD show the full
words they have read back to the user.

### Packing

1. Decode the source with the English wordlist. It MUST have 12, 15, 18, 21 or 24 words and a valid
   BIP39 checksum.
2. Set `r = 256 - ENT`. If `r > 0`, set `X = E || Trunc_r(SHA-256(E))`; otherwise `X = E`.

For a short source the first `ENT/32` bits of `V_r` are exactly its BIP39 checksum; the rest extend
the same hash.

### Permutation

For round index `i` and a 128-bit right half `R`, `RoundMask(i, R)` returns:

```text
S_i = Trunc_128(BLAKE2b-256(DS_SALT || BE32(MEM) || BE32(PIM) || BE32(i) || R))
K_i = Argon2id(password = P_enc, salt = S_i, memory = m(MEM) KiB, passes = t(PIM),
               lanes = 4, version = 0x13, secret = empty, associated data = empty,
               output = 32 bytes)
M_i = Trunc_128(HMAC-SHA-256(key = K_i,
                             message = DS_MASK || BE32(MEM) || BE32(PIM) || BE32(i) || R))
```

`R` is the raw 16-byte half; `K_i` is the HMAC key as is. `BLAKE2b-256` is BLAKE2b with its output
length parameter set to 32 bytes, as defined in RFC 7693 [11]; it is not a truncated BLAKE2b-512
digest, which would give different bytes.

```text
Perm (forward):                     Perm^-1 (inverse):
  L_0 = X[0:128], R_0 = X[128:256]    L_12 = Y[0:128], R_12 = Y[128:256]
  for i = 0 .. 11:                    for i = 11 .. 0:
      M_i     = RoundMask(i, R_i)         R_i = L_{i+1}
      L_{i+1} = R_i                       M_i = RoundMask(i, R_i)
      R_{i+1} = L_i XOR M_i               L_i = R_{i+1} XOR M_i
  Y = L_12 || R_12                    X = L_0 || R_0
```

### Creating a container

1. Ask for the password twice and stop if the two entries differ; a mistyped password would make the
   container unrecoverable with the intended one. Encode the password and validate the PIM and
   memory level before allocating Argon2id memory.
2. Pack the source.

   Before the expensive computation, an application SHOULD check whether the packed state also
   passes the verifier of another short-source length. This costs a few SHA-256 computations. If it
   does, automatic recovery would report a shorter reading or an ambiguity, so the application
   SHOULD tell the user to record the word count of the original and select it manually during
   recovery. The format does not change.

3. Compute `Y = Perm(X)`.
4. If `Y = X`, refuse the result and ask for a different password, PIM or memory level. This is a
   fixed point, with probability `2^-256` for a given input in the ideal-permutation model. The
   check mainly catches a faulty implementation that returns its input unchanged, which would
   otherwise expose the source.
5. Encode `Y` with its ordinary 8-bit BIP39 checksum as 24 English words.
6. Decode the words again, compute `Perm^-1` of the result and compare it with `X`. This MUST be
   done; it repeats the full computation, but it catches many faults, such as a memory error during
   the long computation, that would otherwise produce a container that cannot be recovered, and
   starting from the words also covers their encoding. A mistake shared by the forward and inverse
   computations survives the round trip; independent test vectors are needed to catch it. On a
   mismatch the result MUST be discarded and the error reported.

An application MAY show the container to a person while the check runs, so that writing it down
overlaps the check. It MUST then mark the container clearly as not yet verified, ask the user not to
rely on it until the check ends, and report the outcome: that the container is verified, that it is
wrong and must not be used, or, if the check was cancelled, that it remains unverified. A result
passed to another program instead of a person MUST NOT be released before the check has passed.

### Recovering a mnemonic

1. Decode the container. Anything other than exactly 24 words with a valid checksum is a
   transcription error and MUST be rejected before any Argon2id work.
2. Compute `X = Perm^-1(Y)`.
3. If the user selected a source length in the manual mode, parse `X` as `E || V_r` and compare all
   `r` verifier bits; a mismatch rejects the candidate. Otherwise test the 12-, 15-, 18- and 21-word
   layouts: one match is the detected length; no match yields the 24-word interpretation, labelled
   as not verified. Several matches MUST be reported as ambiguous, and the application MUST then
   show every matching candidate with its word count, together with the 24-word interpretation
   labelled as not verified; it MUST NOT pick one silently.
4. Encode each accepted candidate `E` with its BIP39 checksum and its word count.

Applications SHOULD show the detected length. They MUST also offer a manual mode in which the user
selects any of the five source lengths instead of relying on detection. A selected short length is
accepted only if its verifier matches, and otherwise an error is reported; a selected 24-word length
is always accepted, because it has no verifier. Manual selection is necessary when automatic
detection reports exactly one matching short layout for a genuine 24-word source. A random 24-word
source matches at least one short layout with probability about `2^-32`. For a short source, a wrong
password normally ends in the unverified 24-word result, and applications SHOULD say so. For a
correctly recovered random 12-, 15- or 18-word source, an additional match occurs with probability
about `2^-32` (the 21-word layout), and for a 21-word source about `2^-64`; the user then identifies
the right candidate by comparing public wallet data or by selecting the known length in the manual
mode. A mismatch does not reveal which input was wrong; a 24-word recovery has no internal check at
all.

Every 24-word result, including one selected manually, MUST be labelled as not verified unless it
has matched a wallet-identity reference supplied by the user, as described in the rehearsal check
below. A short-source verifier match MUST NOT be described as confirmation of the wallet's identity.

### Work factor

```text
m(MEM) = (2 + MEM mod 2) * 2^(20 + floor(MEM / 2))   KiB     MEM in 0..21
t(PIM) = 12 * (PIM + 1)                                      PIM in 0..1023
```

The memory level gives 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64 GiB and so on up to 3 TiB at level 21,
multiplying by 1.5 and 4/3 in turn so that every value is a whole number of GiB. It MUST be computed
with integers. PIM `k` multiplies the time roughly by `k + 1`, so PIM 1023 turns a recovery of one
to two minutes into roughly 17 to 34 hours, and a creation, which includes a recovery as its check,
into about twice that.

- Out-of-range values MUST be rejected before memory allocation. An environment that cannot provide
  the memory MUST fail clearly and MUST NOT reduce it.
- Implementations MUST state which memory levels they support and refuse the others before starting.
  The reference C implementation of Argon2 limits memory to 2 GiB when pointers are 32 bits wide, so
  builds for 32-bit WebAssembly support only level 0.
- Applications MUST show both defaults as `0` or as empty fields and SHOULD state the expected time
  and memory before accepting non-zero values.
- Non-zero values MUST be remembered for recovery, and applications MUST tell the user so when a
  value other than the default is chosen. Like part of the password, they MAY be kept secret.
- Implementations MUST NOT search settings automatically unless each candidate is checked by the
  verifier or by a reference as in the rehearsal check below.

### Application requirements

- **Distinct workflow.** A container MUST NOT be passed silently to BIP39 seed derivation, and
  software MUST NOT guess from the words alone that a mnemonic is a container. The BIP39 passphrase
  is applied after recovery. No original backup should be destroyed only because a container exists;
  the user SHOULD first rehearse recovery and compare a known receiving address of the wallet,
  derived with the right network, address type and derivation path.
- **Checking the finished backup.** The rehearsal SHOULD read the container from the finished backup
  rather than from the screen: the check at creation covers the words that the application produced,
  not the copy. If one word is replaced at random, the BIP39 checksum still passes in about one case
  in 256; for a 24-word source such a container then recovers a different, unverified wallet without
  any error from the protocol, and the comparison with a known address is what reveals it.
- **Rehearsal check.** Applications SHOULD offer a check that runs a full recovery and reports only
  "matches" or "does not match". It MUST NOT display, copy to the clipboard, export or persist any
  part of the recovered mnemonic, or report how close a wrong password was. Temporary values needed
  for the computation are subject to the sensitive-memory requirements below. For a short source the
  verifier confirms that the password and settings recover a consistent phrase; it does not show
  that this is the same wallet, and it says nothing about a BIP39 passphrase. The built-in check
  SHOULD use the length the owner knows: with automatic detection, a wrong password passes with
  probability about `2^-32` through the 21-word layout even when the original has 12 words. For a
  24-word source, and whenever the identity of the wallet matters, the user supplies a reference at
  check time, optionally with the passphrase: a known receiving address with its network, address
  type and derivation path, or the BIP32 master key fingerprint [40] as a quicker but weaker 32-bit
  check. Such a reference SHOULD NOT be stored next to the container. The check belongs on the same
  trusted offline computer as a recovery.
- **Recovery assistance.** Applications MAY try local variants of a half-remembered password, such
  as other letter case, separators or keyboard layout, each costing one full recovery.
- **Resources.** Recovery SHOULD start only after an explicit user action and SHOULD be cancellable
  at any moment, not only between rounds, because one round can take hours at a high PIM; stopping
  the worker or process that runs Argon2 is acceptable. Applications SHOULD check available memory
  before accepting a memory level: a graphical application SHOULD NOT offer levels the computer
  cannot provide with a margin, a command-line application SHOULD refuse them with an explanation,
  and a user choosing a level above `0` SHOULD be reminded that recovery needs a computer with the
  same amount of memory, and that one must still be available years later.
- **Parallel lanes.** Implementations MUST compute the four Argon2id lanes in parallel where threads
  are available; otherwise they SHOULD warn that the operation will take longer. The output does not
  depend on the order of lane computation.
- **Passwords.** Applications SHOULD recommend at least four, better five or more, words chosen with
  dice from a published list such as the EFF large wordlist [42], and SHOULD warn about weak
  passwords. They SHOULD advise a different password for each encrypted phrase, used nowhere else;
  further copies of a backup are exact copies of the same container, with the same password and
  settings. They SHOULD also say that, after the required NFKD normalization, letter case and the
  characters between words are significant; a fixed form, such as lowercase words separated by
  single spaces, is the easiest to reproduce years later.
- **Offline use and no secrets on the network.** Creating and recovering containers for real
  recovery phrases on a trusted offline computer is strongly RECOMMENDED; a page served from the
  internet is suitable for demonstration. In every case, implementations MUST NOT send the password,
  the source or recovered mnemonic, or any value derived from them over a network.
- **Sensitive memory.** Implementations SHOULD minimize and erase copies of the entropy, states,
  salts, password, Argon2id outputs and masks where the runtime allows it. Apart from test vectors
  made from public inputs, they MUST NOT log, display, export or write to persistent storage any
  intermediate value, such as states, salts, Argon2id outputs, masks or Argon2id working memory,
  including in error reports and in files kept to resume an interrupted operation: depending on what
  leaks and when, a password can then be tested with a single Argon2id call, or with hashing alone,
  instead of twelve calls.

## Rationale

The design decisions are explained here; the [supplement](docs/DESIGN-NOTES.md) develops the
security arguments, cost models and research alternatives in detail.

**Why a Feistel network with state-derived salts?** Encrypting 256 bits without stored data is easy
with one key `Argon2id(password, constant)`, but then the salt is the same for everyone and a
dictionary computed once attacks every container at once. The only material unique to a container is
the container itself, so the salt must come from the encrypted state and be recomputable during
decryption. A Feistel network keeps one half unchanged in each round, which is exactly what allows a
different salt in every round. SLIP-0039 uses the same idea with PBKDF2 [20]. MHFE does not claim
conformance to NIST SP 800-132, which requires a randomly generated salt part of at least 128 bits
for PBKDF2 [48]: its salts are derived from the state so that the container keeps its fixed size
without stored data. Their suitability is examined in the
[supplement](docs/DESIGN-NOTES.md#why-state-derived-salts); the 128-bit length and the estimate of
accidental collisions do not by themselves make them equivalent to independently generated salts. An
unbalanced Feistel network [36], Lai-Massey [37], [38] and swap-or-not [39] could also work, but
they need, respectively, more rounds, an extra mixing step between rounds, or hundreds of rounds.

**Why Argon2id?** It is specified in RFC 9106, an Informational RFC of the IRTF Crypto Forum
Research Group, which names Argon2id its primary variant [13]. Argon2 won the Password Hashing
Competition, an open competition with 24 candidates [19], [43], and Argon2id is the first choice of
the OWASP password-storage recommendations [44]. During the first half of its first pass Argon2id
accesses memory independently of the password, which resists cache-timing side channels; afterwards
it uses password-dependent access, which raises the cost of trading memory for time. Its memory,
passes and parallelism are separate parameters, while PBKDF2 and bcrypt need little memory. Several
independent implementations exist, including the reference code, OpenSSL and RustCrypto, which
matters for a backup that may have to be decrypted many years later. Its optional secret and
associated data, which RFC 9106 defines, stay empty: many Argon2 interfaces take only a password and
a salt, MHFE defines no additional secret, and the suite, the settings and the round index already
enter through the salt and mask messages.

**Why Argon2id in every round, and why twelve rounds?** Each round's salt depends on the previous
round, so a recovery makes the twelve Argon2id calls in sequence; for a short source, no cheaper
practical way to screen a password guess against the container alone is known. With a known source
and container, the best known shortcut skips one of the twelve rounds, a discount of one twelfth;
twelve rounds give natural progress and cancellation points, and exceed the round counts for which
Patarin proves strong bounds for ideal Feistel networks [14], [15], building on the construction of
Luby and Rackoff [31]. Twelve rounds are a conservative design choice, not a proven security margin:
MHFE's round functions are not independent random functions. The round count and the Argon2id
parameters jointly determine the waiting time, so the time budget alone does not justify twelve
rounds.

**Why BLAKE2b for salts and HMAC-SHA-256 for masks?** The salt is computed without a key from the
half of the state that the round leaves unchanged, so a fast unkeyed hash suffices. Only the first
salt of a recovery can be computed from the container, and the first salt of an encryption from the
original; the other salts depend on the password and are as sensitive as the states. BLAKE2b is used
so that salt derivation shares no function with the SHA-256 verifier. The mask must depend on the
secret Argon2id output, so it needs a keyed function, and HMAC-SHA-256 is the standard choice. The
mask also uses SHA-256, but only inside HMAC keyed with that secret output and a distinct domain
string. The domain strings also separate salts from masks.

**Why 2 GiB and twelve passes?** RFC 9106's first recommended option is Argon2id with 2 GiB, four
lanes and one pass, and its selection procedure takes the largest affordable memory and then the
largest number of passes that fits the available time [13]. The twelve passes are this project's
choice under that procedure, because a cold-storage operation can afford several seconds per round.
For the same time, more memory would, in an area-time cost model and for an attacker limited by
memory capacity, cost an attacker more than more passes, but 2 GiB is the most that the reference C
implementation of Argon2 accepts in a 32-bit WebAssembly build, a limit of that implementation
rather than of the WebAssembly address space, and the most that many computers can spare, so the
rest of the time goes into passes. On a 2022 mid-range laptop (Intel Core i7-1260P) one such call
took about 5 to 10 seconds depending on the Argon2 implementation, so a recovery takes about one to
two minutes and a creation with its check about twice as long.
[What a guess costs](docs/DESIGN-NOTES.md#what-a-guess-costs) gives the attacker cost model and its
assumptions.

**Why two settings, and why these limits?** Memory must fit the computer that will perform recovery,
possibly years later, while waiting time is a matter of patience; one number could not serve both.
PIM stops at 1023 because a factor of 1,024 adds only ten bits while recovery takes roughly 17 to 34
hours on the reference laptop; one more dice word adds 12.9 bits for free. The memory level stops at
21 because level 22 would exceed the Argon2id limit of `2^32 - 1` KiB. An owner may keep a setting
secret, but that helps only to the extent that its value is unpredictable to the attacker, and it
gives no fixed additional margin; a forgotten setting must also be searched during recovery. A
strong, independently generated password remains the primary protection. The
[parameter rationale](docs/DESIGN-NOTES.md#parameter-rationale) estimates the effect of a secret PIM
under stated assumptions.

**Why a verifier for short sources and none for 24 words?** A short source leaves free bits in the
256-bit state, and filling them with a hash of the source adds no storage and lets recovery screen
the password and detect a likely length, subject to false matches. A 24-word source has no free
bits. Both behaviours are useful, and the user chooses by the length of the original:

| Original       | Recovery                                                                                                                         | With a BIP39 passphrase                                                                               |
| -------------- | -------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| 12 to 21 words | screens the password and detects a likely length; the 32-bit verifier of a 21-word source admits false matches in large searches | the costs add up only while work on false matches is negligible                                       |
| 24 words       | cannot confirm; a wrong password gives another valid wallet                                                                      | independent secrets require a search over pairs if no separate check identifies the original mnemonic |

A 24-word original gives the strongest combination when the two secrets are independent and no
separate check identifies the original mnemonic. A 12- to 21-word original provides an internal
recovery check, but false matches may require additional passphrase searches, especially with a
21-word source. Without a passphrase, a funded 24-word wallet lets a guesser confirm a password
through the blockchain anyway. The
[composition analysis](docs/DESIGN-NOTES.md#composition-with-the-bip39-passphrase) gives the search
costs of both cases, as estimates rather than lower bounds, and explains when work on false matches
dominates. Related or reused secrets lose these gains.

**Why is the final word not preserved?** A 24-word original has no verifier. One conceivable aid
would be a container that ends with the same last word as the original: that word carries the
original's 8-bit checksum, so the owner could at least recognise which plate belongs to which
wallet. Such a container can be found by cycle walking [35], that is, by applying the permutation
again and again until the last word matches. This needs about 2,048 permutations on average, each as
long as a recovery, which with the suite 3 parameters means about one and a half to three days per
recovery on average, about twice that for a creation with its check, and longer in a browser without
threads. It would also reveal the last word, which is three entropy bits directly and about 11 bits
of information about the source in total, and would still not confirm the password, because a wrong
password also walks to a phrase with the same last word. The idea is therefore not used; it is
recorded as [research](docs/DESIGN-NOTES.md#final-word-preserving-cycle-walking-research-idea).

**Why NFKD and Unicode 17.0.0?** NFKD is the normalization that BIP39 applies to mnemonics and
passphrases [2], and it makes compatible variants, such as full-width and ordinary Latin letters,
give the same password. BIP39 support in a library is not enough, however: MHFE also uses the
process for stabilized strings with a pinned Unicode version and rejects the characters listed under
Password encoding. Words are read forgivingly because each resolves to one entry of a fixed list, so
nothing is lost. A password is free text, in which letter case and spacing can be part of what the
owner chose, and any further normalization would have to stay frozen with the suite; it is therefore
used as entered, apart from NFKD. Normalization of assigned characters never changes, so a version
pin only decides which new characters are rejected. Unicode 17.0.0 is implemented by current
libraries, including Rust's. Suite 2 had pinned Unicode 18.0.0, the newest version at the time, for
which Rust had no normalization tables yet, so its reference implementation accepted only ASCII
passwords; suite 3 deliberately returns to 17.0.0 so that full Unicode passwords work with existing
libraries.

**Why only the English wordlist?** Suite 3 reads sources and writes containers with the English
BIP39 wordlist only. BIP39 itself recommends the same: its
[Wordlists](https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki#wordlists) section
strongly discourages other wordlists for generating mnemonics, because the vast majority of BIP39
wallets support only the English one [2]. BIP39 also derives the seed from the words of the
mnemonic, not from its entropy, so the same entropy written with another wordlist gives a different
wallet: a phrase in another language cannot be accepted by re-encoding it in English words, and
recovery could restore the original language only if the user remembered it as one more setting. The
container has no room to record a wordlist, and the rule for four-letter abbreviations under Reading
words is defined and checked for the English list. Support for other wordlists would need its own
suite identifier that fixes the wordlist. Other seed formats, such as Electrum seeds and SLIP-0039
shares, are outside this specification.

**Related work.** SLIP-0039 [20] encrypts a master secret with a Feistel network over PBKDF2 but is
a secret-sharing format. BIP38 [21] protects single private keys with scrypt in an expanded record.
MnemonicCrypt [27], Mnemonikey [28] and pktseed [29] add salts, versions or other fields and change
the mnemonic length or wordlist; seed-otp [30] needs a second secret as long as the mnemonic;
Seedshift, bip39_obfuscator and BIP39Colors [24]-[26] offer obfuscation, not memory-hard encryption.
For a 24-word source MHFE has the structure of honey encryption [16] with a uniform message model,
and plausible deniability is defined as for deniable encryption [46]; both are analysed in the
[supplement](docs/DESIGN-NOTES.md#deniability).

## Backward Compatibility

MHFE changes no Bitcoin consensus, network or wallet rules. A container is a valid 24-word BIP39
mnemonic, so ordinary wallets accept it and derive an unrelated wallet from it; the MHFE workflow
must therefore stay separate from ordinary wallet recovery. That unrelated wallet can serve as a
decoy only against someone who does not know that MHFE was used, and, like any decoy, only if its
balance and history fit what that person knows about the owner. The decoy passwords analysed in the
[supplement](docs/DESIGN-NOTES.md#deniability) remain possible when the use of MHFE is known. After
recovery, the original mnemonic and any BIP39 passphrase work in every BIP39 wallet exactly as
before.

## Security Considerations

The design aims to ensure that:

- for a short source, no practical way is known to screen a password guess against the container
  alone with fewer Argon2id calls than the twelve of a recovery; for a 24-word source, recovery
  alone confirms nothing, and a check with external information, such as a known address, needs the
  fully recovered mnemonic;
- work done for one container does not help with containers of independently generated sources,
  apart from salt collisions of negligible probability;
- with a known source and container, the best known shortcut skips only one of the twelve calls.

These are conjectures supported by arguments in the random-oracle model in the supplement; they are
not proofs and have not been reviewed by a cryptographer. MHFE provides no wrong-password detection
for 24-word sources.

These conjectures are separate from the analysis of plausible deniability. For one container and one
prepared disclosure, the [supplement](docs/DESIGN-NOTES.md#deniability) bounds the adversary's
advantage in telling a prepared disclosure from an honest one by about the probability of guessing
the real password, in stated experiments and, for the general bound, in the random-oracle model. For
a uniformly random 24-word source, everything disclosed, from the container to the disclosed
wallet's record, has exactly the same distribution in both cases if the refusal of fixed points and
the redrawing of the decoy password are set aside; the general bound also accounts for these two
events and for the chance of finding the real wallet.

The guarantee assumes that the adversary does not know that the original has fewer than 24 words,
that the decoy password is drawn like a real one and that the decoy wallet's public history follows
the same usage scenario as an honest wallet's. Where deniability matters, further copies of a backup
should be exact copies of one verified container, and no other record of the phrase that an
adversary could find and link to the container, such as a paper copy or a hardware wallet, should
contradict the disclosure.

The analysis does not cover wallets linked by transfers or other records, what changes between
repeated demands, two different passwords named for one container, several containers of one phrase
made with different passwords or settings, a BIP39 passphrase, a leaked password, side channels or
whether a particular person will believe the disclosure. The analysis has not been independently
reviewed by a cryptographer.

MHFE provides no authentication: anyone can alter a container and recompute its checksum, and the
verifier screens wrong passwords and most accidental corruption but does not authenticate the
container. A replaced plate may be detected during recovery, but confirming the wallet's identity
requires comparison with trusted wallet data, whatever the source length. Keeping an independent
copy of the container in another place and comparing the copies can reveal differences; checking a
known address after recovery confirms the wallet rather than merely a verifier match.

A password shared by several containers is only as safe as the weakest of them: finding it through
any one, including through a leaked original with its container, opens all of them.

MHFE is deterministic: the same source, password and settings always give the same container. Copies
of a backup can therefore be recreated exactly, and identical containers reveal something. Under the
same suite, normalized password and settings they come from identical packed states. If the source
length is also the same, the original mnemonic is identical. A packed state does not by itself fix
the original length, because the 256 bits of a short source's state are also a valid 24-word
entropy. Across different passwords or settings, equal containers establish nothing about the
sources. For fixed inputs there is exactly one correct container, so an independent implementation
can detect a different result by recomputing it; this checks the result, not whether the software
leaked secrets.

If Argon2id or the construction were weakened in future, existing containers could not be upgraded
in place, since they carry no version; they would have to be decrypted and encrypted again under a
new suite.

The password remains the main protection. Use independently chosen random words, such as dice words
from the EFF list [42]; passwords that people make up themselves are usually much weaker than their
length suggests. The supplement's [attack-cost table](docs/DESIGN-NOTES.md#what-a-guess-costs)
compares password choices under explicit assumptions.

Higher settings increase the cost per guess; each extra independently chosen random word multiplies
the password search space by 7,776. For storage over decades, allow for guesses becoming cheaper
over time. The supplement also covers the threat models, farms and botnets, the composition with the
BIP39 passphrase, determinism and side channels.

## Reference Implementation

The Rust library, command-line tool and WebAssembly build
[`hobby-eng/mhfe`](https://github.com/hobby-eng/mhfe) implement suite 3 from version 0.4.0, with the
reference C implementation of Argon2 as their single Argon2 engine for native and browser builds.
Browser builds compile the same reference C code to WebAssembly with Emscripten (or an equivalent
toolchain): one build with threads for cross-origin isolated pages and one without threads for all
other pages; the build script and its flags are in the reference implementation
(`scripts/build-argon2-wasm.sh`). Version 0.4.0 implements only suite 3 and does not support
suite 2. The last release that implements suite 2,
[`v0.3.0`](https://github.com/hobby-eng/mhfe/releases/tag/v0.3.0), remains available. The reference
implementation snapshot used for this specification's public corpus is revision
[`46112d2b4bec0b9eba34cbbb9d632df099e11672`](https://github.com/hobby-eng/mhfe/commit/46112d2b4bec0b9eba34cbbb9d632df099e11672).

## Test Vectors

The suite 3 corpus in [`vectors/suite3/`](vectors/suite3/) contains 17 positive round transcripts,
six negative recovery cases and 54 fast validation cases. The recorded full-cost replay with the
independent OpenSSL 3.5.5 Argon2 engine reproduced every positive transcript in both directions and
all six negative cases. The fast cases cover password encoding, input validation and verifier
serialization without Argon2 work. Companion notes record source, generator and verifier provenance,
validation coverage and remaining limits. These results do not constitute an independently authored
MHFE implementation or a cryptographic security review.

Published suite 3 vector sets MUST cover every source length, the defaults, a non-zero PIM, memory
level 1, a non-zero PIM and memory level together, and a non-ASCII password, with the exact
normalized password bytes and every round's salt and mask input messages, salt, Argon2id output,
mask and state. They MUST be reproduced in both directions by an independent Argon2 implementation,
such as OpenSSL or RustCrypto, with all suite parameters including four lanes. Published vector sets
MUST identify the generator and independent verifier revisions.

Conformance cases MUST include invalid checksums and out-of-range values, and state the expected
recovery outcome for each tested mode: verifier rejection for a mismatching selected short length,
an unverified 24-word result when selected manually or when no short layout matches, and ambiguity
when several short layouts match. Wrong-password and wrong-setting cases MUST distinguish these
outcomes rather than require rejection in every mode.

Password-encoding cases MUST cover an unassigned code point, a noncharacter, a Private Use
character, the rejected characters NUL, TAB, LF, CR, U+0085, U+2028 and U+2029, invalid UTF-8, an
unpaired surrogate at a JavaScript boundary, canonical-equivalent spellings and spaces. They MUST
also cover exactly 1024 and 1025 normalized UTF-8 bytes, an NFKD expansion that crosses the
1024-byte limit and an NFKD contraction from more than 1024 input bytes to a valid result. The
expected normalized bytes or rejection MUST be recorded. Vectors are released under CC0-1.0.

The standard libsodium password-hashing API fixes the lane count at one and cannot reproduce these
four-lane vectors.

The archived suite 2 vectors are in
[`vectors/archive/suite-2/`](vectors/README.md#archived-suite-2), apart from the current corpus in
`vectors/suite3/`. They remain valid for suite 2 and preserve compatibility checks for that format,
but the current implementation no longer replays them.

## Appendix: Suite 2

Suite 2 (`MHFE-BIP39-256-EXPERIMENTAL-2`) is an archived experimental format defined by the
specification published as release
[`v0.3.0`](https://github.com/hobby-eng/mhfe-spec/releases/tag/v0.3.0) and archived under DOI
[10.5281/zenodo.22902450](https://doi.org/10.5281/zenodo.22902450). The following summary is
informative; requirements introduced in suite 3 do not apply retroactively to suite 2, and
implementations of suite 3 are not required to support suite 2. Release
[`v0.3.0`](https://github.com/hobby-eng/mhfe/releases/tag/v0.3.0) of `mhfe` implements it, and its
published vectors are listed under [archived suite 2](vectors/README.md#archived-suite-2). In short,
suite 2 differs from suite 3 in its identifier and domain strings, 512 MiB of Argon2id memory with
no memory level, PIM `0..31` with the same pass formula, salt and mask messages
`DS || BE32(PIM) || BE32(i) || R` without `BE32(MEM)`, and password normalization with Unicode
18.0.0 (UAX #15 revision 58) [10] instead of 17.0.0 [41]. The released text is also kept, marked as
historical, in the [archive](docs/archive/README.md). An optional final-word-preserving profile for
suite 2 was drafted and implemented after that release but never released; the archive notes point
to its text, and the supplement keeps its analysis as a
[research idea](docs/DESIGN-NOTES.md#final-word-preserving-cycle-walking-research-idea).

## AI Assistance and Acknowledgments

Sergei Semenov defined the research direction and practical requirements and made the publication
decisions. This draft was developed through extended interaction with ChatGPT (OpenAI) and Claude
(Anthropic), which contributed substantially to drafting, literature discovery, calculations,
counterarguments and adversarial review. It has not received an independent expert cryptographic
review.

## Changelog

The version history, including the changes in each draft, is kept in [`CHANGELOG.md`](CHANGELOG.md).

## Copyright

Copyright © 2026 Sergei Semenov. This specification and the repository documentation are licensed
under the Creative Commons Attribution 4.0 International License (`CC-BY-4.0`); see
[`LICENSE`](LICENSE). The test vectors in `vectors/` are released under CC0-1.0, following BIP 3's
recommendation [7]. When sharing or adapting this material, credit Sergei Semenov, link to the
license and the source, and indicate changes; attribution must not imply endorsement.

## References

Some entries are cited only in the supplement, which uses the same numbering.

1. Cryptosteel, "How to Use Cryptosteel Capsule." [Online]. Available:
   https://cryptosteel.com/how-to-use-capsule/. [Accessed: Sep. 18, 2026].
2. M. Palatinus, P. Rusnak, A. Voisine, and S. Bowe, "Mnemonic code for generating deterministic
   keys," BIP 39, Sep. 10, 2013. [Online]. Available:
   https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki. [Accessed: Sep. 18, 2026].
3. Tarion, "How to encrypt an existing BIP-39 mnemonic with a password without changing the seed?"
   _Bitcoin Stack Exchange_, May 5, 2021. [Online]. Available:
   https://bitcoin.stackexchange.com/questions/106036/. [Accessed: Sep. 19, 2026].
4. T. Kaupat, _go-bip39_, GitHub repository, rev. `3ab2b81a7576aedbe1e1a347cab359e383dbf248`, Dec.
   17, 2024. [Online]. Available:
   https://github.com/Niondir/go-bip39/blob/3ab2b81a7576aedbe1e1a347cab359e383dbf248/encryption.go.
   Relevant earlier revisions: `6615be49f50a990856ec5a65e7b3d9e985644946`, May 5, 2021, and
   `2a307b8f25e0454ebbe9bbae0fcb7659fafcbba2`, May 10, 2021. [Accessed: Sep. 19, 2026].
5. S. Bradner, "Key words for use in RFCs to Indicate Requirement Levels," RFC 2119, BCP 14, RFC
   Editor, Mar. 1997, doi: 10.17487/RFC2119.
6. B. Leiba, "Ambiguity of Uppercase vs Lowercase in RFC 2119 Key Words," RFC 8174, BCP 14, RFC
   Editor, May 2017, doi: 10.17487/RFC8174.
7. Murch, "Updated BIP Process," BIP 3, ver. 1.4.0, Dec. 9, 2025. [Online]. Available:
   https://github.com/bitcoin/bips/blob/master/bip-0003.md. [Accessed: Sep. 20, 2026].
8. E. Lombrozo, "BIP Classification," BIP 123, Aug. 26, 2015. [Online]. Available:
   https://github.com/bitcoin/bips/blob/master/bip-0123.mediawiki. [Accessed: Sep. 20, 2026].
9. National Institute of Standards and Technology, _Secure Hash Standard (SHS)_, FIPS PUB 180-4,
   Aug. 2015, doi: 10.6028/NIST.FIPS.180-4.
10. K. Whistler, Ed., "Unicode Normalization Forms," Unicode Standard Annex #15, rev. 58, Unicode
    18.0.0, Aug. 12, 2026. [Online]. Available: https://www.unicode.org/reports/tr15/tr15-58.html.
    [Accessed: Sep. 22, 2026].
11. M.-J. Saarinen and J.-P. Aumasson, "The BLAKE2 Cryptographic Hash and Message Authentication
    Code (MAC)," RFC 7693, RFC Editor, Nov. 2015, doi: 10.17487/RFC7693.
12. H. Krawczyk, M. Bellare, and R. Canetti, "HMAC: Keyed-Hashing for Message Authentication," RFC
    2104, RFC Editor, Feb. 1997, doi: 10.17487/RFC2104.
13. A. Biryukov, D. Dinu, D. Khovratovich, and S. Josefsson, "Argon2 Memory-Hard Function for
    Password Hashing and Proof-of-Work Applications," RFC 9106, RFC Editor, Sep. 2021, doi:
    10.17487/RFC9106.
14. J. Patarin, "Luby-Rackoff: 7 Rounds Are Enough for 2^{n(1-epsilon)} Security," in _Advances in
    Cryptology--CRYPTO 2003_, LNCS 2729. Berlin, Germany: Springer, 2003, pp. 513-529, doi:
    10.1007/978-3-540-45146-4_30.
15. J. Patarin, "Security of Random Feistel Schemes with 5 or More Rounds," in _Advances in
    Cryptology--CRYPTO 2004_, LNCS 3152. Berlin, Germany: Springer, 2004, pp. 106-122, doi:
    10.1007/978-3-540-28628-8_7.
16. A. Juels and T. Ristenpart, "Honey Encryption: Security Beyond the Brute-Force Bound," in
    _Advances in Cryptology--EUROCRYPT 2014_, LNCS 8441. Berlin, Germany: Springer, 2014, pp.
    293-310, doi: 10.1007/978-3-642-55220-5_17.
17. J. Patarin, "Generic Attacks on Feistel Schemes," in _Advances in Cryptology--ASIACRYPT 2001_,
    LNCS 2248. Berlin, Germany: Springer, 2001, pp. 222-238, doi: 10.1007/3-540-45682-1_14. Extended
    version: Cryptology ePrint Archive, Paper 2008/036.
18. J. Patarin, "Security of balanced and unbalanced Feistel Schemes with Linear Non Equalities,"
    Cryptology ePrint Archive, Paper 2010/293, May 18, 2010. [Online]. Available:
    https://eprint.iacr.org/2010/293. [Accessed: Sep. 21, 2026].
19. A. Biryukov, D. Dinu, and D. Khovratovich, "Argon2: New Generation of Memory-Hard Functions for
    Password Hashing and Other Applications," in _2016 IEEE European Symposium on Security and
    Privacy_. Piscataway, NJ, USA: IEEE, 2016, pp. 292-302, doi: 10.1109/EuroSP.2016.31.
20. P. Rusnak, A. Kozlik, O. Vejpustek, T. Susanka, M. Palatinus, and J. Hoenicke, "Shamir's
    Secret-Sharing for Mnemonic Codes," SLIP-0039, Dec. 18, 2017. [Online]. Available:
    https://github.com/satoshilabs/slips/blob/master/slip-0039.md. [Accessed: Sep. 21, 2026].
21. M. Caldwell and A. Voisine, "Passphrase-protected private key," BIP 38, Nov. 20, 2012. [Online].
    Available: https://github.com/bitcoin/bips/blob/master/bip-0038.mediawiki. [Accessed: Sep. 21,
    2026].
22. National Institute of Standards and Technology, _Advanced Encryption Standard (AES)_, FIPS PUB
    197, updated May 9, 2023, doi: 10.6028/NIST.FIPS.197-upd1.
23. M. Dworkin, _Recommendation for Block Cipher Modes of Operation: Methods and Techniques_, NIST
    SP 800-38A, Dec. 2001, Appendix B, doi: 10.6028/NIST.SP.800-38A.
24. mifunetoshiro, _Seedshift_, GitHub repository, rev. `853423930e29b388ff936f581d9b692944319d46`,
    Jul. 26, 2025. [Online]. Available:
    https://github.com/mifunetoshiro/Seedshift/tree/853423930e29b388ff936f581d9b692944319d46.
    [Accessed: Sep. 18, 2026].
25. mifunetoshiro, _bip39_obfuscator_, GitHub repository, rev.
    `0d82f4809fe4bec0e53d4487a3dd9e34142af04b`, Oct. 25, 2021. [Online]. Available:
    https://github.com/mifunetoshiro/bip39_obfuscator/tree/0d82f4809fe4bec0e53d4487a3dd9e34142af04b.
    [Accessed: Sep. 19, 2026].
26. EnteroPositivo, _BIP39Colors_, GitHub repository, rev.
    `df3bc100416d8acc48d7cad02050e5eb3ac177ae`, Jul. 15, 2023. [Online]. Available:
    https://github.com/EnteroPositivo/bip39colors/tree/df3bc100416d8acc48d7cad02050e5eb3ac177ae.
    [Accessed: Sep. 22, 2026].
27. JonDerThan, _MnemonicCrypt_, GitHub repository, rev. `d3c9315b483805689fd978b7dc783b0e86676473`,
    Oct. 31, 2025. [Online]. Available:
    https://github.com/JonDerThan/mnemonic-crypt/tree/d3c9315b483805689fd978b7dc783b0e86676473.
    [Accessed: Sep. 20, 2026].
28. kklash, _Mnemonikey_, GitHub repository, rev. `0bd15d84d23ffd7e439eb3217c4215dd8df8894f`, Jan.
    29, 2024. [Online]. Available:
    https://github.com/kklash/mnemonikey/tree/0bd15d84d23ffd7e439eb3217c4215dd8df8894f. [Accessed:
    Sep. 21, 2026].
29. C. J. DeLisle, _pktseed_, GitHub repository, rev. `1ec6b87f6603579bac8b63f38d73710ee8e36425`,
    Aug. 28, 2021. [Online]. Available:
    https://github.com/cjdelisle/pktseed/tree/1ec6b87f6603579bac8b63f38d73710ee8e36425. [Accessed:
    Sep. 22, 2026].
30. B. Matthews, _seed-otp_, GitHub repository, rev. `70b51e05daf054355bd7691188ff7720afc7ca3c`,
    Apr. 30, 2021. [Online]. Available:
    https://github.com/brndnmtthws/seed-otp/tree/70b51e05daf054355bd7691188ff7720afc7ca3c.
    [Accessed: Sep. 18, 2026].
31. M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom
    Functions," _SIAM Journal on Computing_, vol. 17, no. 2, pp. 373-386, Apr. 1988, doi:
    10.1137/0217022.
32. M. Dworkin, _Recommendation for Block Cipher Modes of Operation: Methods for Format-Preserving
    Encryption_, NIST SP 800-38G, updated Aug. 4, 2016, doi: 10.6028/NIST.SP.800-38G. The second
    public draft of Revision 1 was published Feb. 3, 2025; it is not a final publication.
33. B. Morris, H. Oberschelp, and H. S. Santhakumar, "Format Preserving Encryption in the Bounded
    Retrieval Model," arXiv:2307.08158, Jul. 16, 2023, doi: 10.48550/arXiv.2307.08158.
34. B. Morris, P. Rogaway, and T. Stegers, "How to Encipher Messages on a Small Domain," in
    _Advances in Cryptology--CRYPTO 2009_, LNCS 5677. Berlin, Germany: Springer, 2009, pp. 286-302,
    doi: 10.1007/978-3-642-03356-8_17.
35. J. Black and P. Rogaway, "Ciphers with Arbitrary Finite Domains," in _Topics in Cryptology--
    CT-RSA 2002_, LNCS 2271. Berlin, Germany: Springer, 2002, pp. 114-130, doi:
    10.1007/3-540-45760-7_9.
36. V. T. Hoang and P. Rogaway, "On Generalized Feistel Networks," in _Advances in
    Cryptology--CRYPTO 2010_, LNCS 6223. Berlin, Germany: Springer, 2010, pp. 613-630, doi:
    10.1007/978-3-642-14623-7_33.
37. X. Lai and J. L. Massey, "A Proposal for a New Block Encryption Standard," in _Advances in
    Cryptology--EUROCRYPT '90_, LNCS 473. Berlin, Germany: Springer, 1991, pp. 389-404, doi:
    10.1007/3-540-46877-3_35.
38. S. Vaudenay, "On the Lai-Massey Scheme," in _Advances in Cryptology--ASIACRYPT '99_, LNCS 1716.
    Berlin, Germany: Springer, 1999, pp. 8-19, doi: 10.1007/978-3-540-48000-6_2.
39. V. T. Hoang, B. Morris, and P. Rogaway, "An Enciphering Scheme Based on a Card Shuffle," in
    _Advances in Cryptology--CRYPTO 2012_, LNCS 7417. Berlin, Germany: Springer, 2012, pp. 1-13,
    doi: 10.1007/978-3-642-32009-5_1.
40. P. Wuille, "Hierarchical Deterministic Wallets," BIP 32, Feb. 11, 2012. [Online]. Available:
    https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki. [Accessed: Sep. 28, 2026].
41. K. Whistler, Ed., "Unicode Normalization Forms," Unicode Standard Annex #15, rev. 57, Unicode
    17.0.0, Jul. 30, 2025. [Online]. Available: https://www.unicode.org/reports/tr15/tr15-57.html.
    [Accessed: Sep. 28, 2026].
42. J. Bonneau, "Deep Dive: EFF's New Wordlists for Random Passphrases," Electronic Frontier
    Foundation, Jul. 19, 2016. [Online]. Available:
    https://www.eff.org/deeplinks/2016/07/new-wordlists-random-passphrases. [Accessed: Sep. 28,
    2026].
43. Password Hashing Competition, "Password Hashing Competition and our recommendation for hashing
    passwords: Argon2." [Online]. Available: https://www.password-hashing.net/. [Accessed: Sep. 29,
    2026].
44. OWASP Cheat Sheet Series, "Password Storage Cheat Sheet." [Online]. Available:
    https://cheatsheetseries.owasp.org/cheatsheets/Password_Storage_Cheat_Sheet.html. [Accessed:
    Sep. 29, 2026].
45. Chick3nman, "Hashcat v6.2.6 benchmark on the Nvidia RTX 4090," benchmark by blazer, GitHub Gist,
    Oct. 14, 2022. [Online]. Available:
    https://gist.github.com/Chick3nman/32e662a5bb63bc4f51b847bb422222fd. [Accessed: Sep. 30, 2026].
46. R. Canetti, C. Dwork, M. Naor, and R. Ostrovsky, "Deniable Encryption," in _Advances in
    Cryptology--CRYPTO '97_, LNCS 1294. Berlin, Germany: Springer, 1997, pp. 90-104, doi:
    10.1007/BFb0052229.
47. V. Shoup, "Sequences of Games: A Tool for Taming Complexity in Security Proofs," Cryptology
    ePrint Archive, Paper 2004/332, 2004. [Online]. Available: https://eprint.iacr.org/2004/332.
    [Accessed: Sep. 30, 2026].
48. M. S. Turan, E. Barker, W. Burr, and L. Chen, _Recommendation for Password-Based Key Derivation,
    Part 1: Storage Applications_, NIST SP 800-132, Dec. 2010, Section 5.1, doi:
    10.6028/NIST.SP.800-132.
49. A. Czeskis, D. J. St. Hilaire, K. Koscher, S. D. Gribble, T. Kohno, and B. Schneier, "Defeating
    Encrypted and Deniable File Systems: TrueCrypt v5.1a and the Case of the Tattling OS and
    Applications," in _3rd USENIX Workshop on Hot Topics in Security (HotSec 08)_, Jul. 2008.
    [Online]. Available:
    https://www.usenix.org/legacy/event/hotsec08/tech/full_papers/czeskis/czeskis.pdf. [Accessed:
    Oct. 1, 2026].
50. L. K. Grover, "A Fast Quantum Mechanical Algorithm for Database Search," in _Proceedings of the
    28th Annual ACM Symposium on Theory of Computing (STOC '96)_, 1996, pp. 212-219, doi:
    10.1145/237814.237866.
51. J. Proos and C. Zalka, "Shor's Discrete Logarithm Quantum Algorithm for Elliptic Curves,"
    _Quantum Information and Computation_, vol. 3, no. 4, pp. 317-344, 2003. [Online]. Available:
    https://arxiv.org/abs/quant-ph/0301141. [Accessed: Oct. 1, 2026].
