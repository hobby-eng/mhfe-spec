# MHFE: Memory-Hard Feistel Encryption for BIP39 Mnemonics

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22902450.svg)](https://doi.org/10.5281/zenodo.22902450)

**DOI:** [10.5281/zenodo.22902450](https://doi.org/10.5281/zenodo.22902450)

_Experimental construction and design notes in a BIP-inspired document format_

```
  Project: Memory-Hard Feistel Encryption for BIP39 Mnemonics (MHFE)
  Title: MHFE: Memory-Hard Feistel Encryption for BIP39 Mnemonics
  Author: Sergei Semenov
  Status: Research draft
  Type: Experimental specification and design notes
  BIP status: Not a BIP proposal; BIP-inspired structure only
  License: CC-BY-4.0
  Version: 0.3.0
  Date: 2026-09-22
  DOI: 10.5281/zenodo.22902450
  Related standard: BIP39
```

> **Canonical specification.** Mathematical notation in this document uses GitHub-supported LaTeX. Exact protocol strings, byte sequences, pseudocode, and file names remain monospaced. A plain-notation reading copy is available as [`SPECIFICATION-PLAIN.md`](SPECIFICATION-PLAIN.md).

## Contents

- [Abstract](#abstract)
- [Motivation](#motivation)
- [Conventions and Terminology](#conventions-and-terminology)
- [Design Status and Scope](#design-status-and-scope)
- [Specification](#specification)
- [Rationale](#rationale)
- [Backward Compatibility](#backward-compatibility)
- [Security Considerations](#security-considerations)
- [Related Work and Alternatives](#related-work-and-alternatives)
- [Theoretical Investigation and Alternative Designs](#theoretical-investigation-and-alternative-designs)
- [Reference Implementation](#reference-implementation)
- [Test Vectors](#test-vectors)
- [Known Limitations](#known-limitations)
- [Version history](CHANGELOG.md)
- [AI Assistance and Acknowledgments](#ai-assistance-and-acknowledgments)
- [Copyright](#copyright)
- [References](#references)

## Abstract

This document proposes an experimental password-based, fixed-size encryption format for BIP39
mnemonics. Its practical goal is to turn an existing mnemonic into a password-protected 24-word
container that can still be recorded on familiar word-based backup media. A valid 12-, 15-,
18-, 21-, or 24-word source mnemonic is packed into one 256-bit plaintext state, transformed by a
256-bit Feistel permutation, and re-encoded as a valid 24-word BIP39 mnemonic. For a shorter
source with `ENT` bits of entropy `E`, the remaining
$`r = 256 - \mathrm{ENT}`$ bits are filled by one recovery verifier,
$`V_r = \mathrm{Trunc}_{r}(\mathrm{SHA256}(E))`$. The verifier is therefore 128, 96, 64, or 32 bits for a 12-, 15-,
18-, or 21-word source. Its first $`\frac{\mathrm{ENT}}{32}`$ bits are exactly the source mnemonic's ordinary
BIP39 checksum, while all remaining bits extend the same hash-based recovery check. No separate
checksum field is needed. After decryption, the complete `V_r` checks a candidate source entropy;
it is deterministic redundancy rather than authentication. A 24-word source occupies all 256
bits and cannot carry such a verifier. No separate randomly generated salt, nonce, authentication
tag, version field, or other metadata is encoded within or appended to the encrypted mnemonic.
The round salts described below are instead derived deterministically from the evolving state. Reliable
recovery requirements and the limits of automatic source-length detection are described under
**Practical recovery requirements**.

The current construction derives a memory-hard Argon2id subkey from a state-derived salt in
each Feistel round. This is intended to make password guessing expensive while preserving exact
256-to-256-bit reversibility. Version 0.3.0 fixes one exact experimental suite so implementations
and test vectors can be compared, but the construction remains experimental and unaudited. No
claim is made that the suite has a formal security proof, that its selected parameters are safe,
or that it is suitable for protecting real funds.

## Motivation

### Practical purpose: protecting a physical backup without expanding it

**The practical goal is to keep a recovery phrase on a familiar, capacity-limited physical
backup while making possession or a photograph of that backup insufficient, by itself,
to recover the original phrase.**

Physical seed-backup products such as Cryptosteel, and comparable metal plates or capsules,
provide a finite number of character or word positions. Cryptosteel's own instructions describe
storing longer BIP39 phrases using abbreviated words [1]. Such media cannot accommodate
arbitrary expansion without changing the storage arrangement. A password-encrypted container
that remains a valid 24-word BIP39 phrase could use the same word-oriented recording method,
subject to the medium's capacity and supported wordlist. This is the practical reason for
investigating a fixed-size format rather than simply adding more fields to a backup.

Physical durability, confidentiality, and concealment address different problems. An unencrypted
phrase on paper or metal can be read, copied, or photographed by anyone who encounters it, even
without removing the original. MHFE is intended to make recovery from that record require a
password rather than expose the original phrase immediately.

The 24-word container also has the ordinary syntax of a valid BIP39 mnemonic and carries no
in-band marker identifying it as encrypted. A casual observer may therefore interpret it as an
ordinary recovery phrase and may not realize that another mnemonic is concealed behind it. This
format ambiguity can reduce opportunistic attention and avoid revealing the encryption workflow
itself. It is only a practical concealment property, however, not a formal plausible-deniability,
Honey Encryption, or indistinguishability guarantee. Storage context, accompanying instructions,
known wallet addresses, repeated containers, or prior knowledge of MHFE may reveal the record's
purpose and permit password candidates to be tested at the construction's KDF cost.

The MHFE password must therefore be retained independently: memorized or recorded in a separate
location, possibly in a discreet form meaningful to its owner. If the user deliberately selects a
non-zero PIM, or if the original wallet also uses a BIP39 passphrase, those values must likewise be
preserved. They should not be stored beside the container as part of the same exposed backup.
Keeping them separate helps preserve both confidentiality and the container's ambiguous appearance,
but a disguised written password is not a substitute for resistance to guessing. Losing any secret
or non-default recovery input can prevent recovery.

**Author's motivation and hypothesis:** the author considers managing one sufficiently strong,
memorable password potentially easier than memorizing 12 or 24 mnemonic words in their exact
order. A separate, discreet password record may also be easier to manage than another full
mnemonic record. On that basis, the author considers an encrypted physical backup with a
separately managed password potentially safer against accidental viewing or photography than
keeping the complete recovery phrase openly readable. This is an authorial usability and
security hypothesis motivating the research, not a measured user-study result or a claim
that the current MHFE construction has proven security.

### Prior problem statement and community context

BIP39 provides a compact human-readable representation of wallet entropy [2], but it does not define
an in-place encryption format for an existing mnemonic. The optional BIP39 passphrase affects the
512-bit seed derived from the mnemonic; it does not encrypt or alter the mnemonic backup itself.

The problem has a concrete public history. In May 2021, approximately five years before this
draft, a Bitcoin Stack Exchange discussion posed almost the same goal: encrypt an existing BIP39
mnemonic into another mnemonic while preserving recovery of the original wallet seed, and it
linked an experimental AES-CTR prototype [3], [4]. The available public record stops short of a
complete, reviewed, interoperable proposal: it does not provide a stable format, a memory-hard KDF
profile, comprehensive test vectors, or a construction-specific security analysis. This unresolved
discussion is the closest historical anchor for presenting MHFE to technical forums such as
Delving Bitcoin. MHFE treats it as evidence that the use case predates this draft, not as validation
of the present construction.

### Baseline design goals

Conventional password-encryption formats normally store additional information such as a
random salt, nonce, version, and authentication tag. The baseline goal here is narrower:
emit one exact 24-word BIP39 container while making recovery depend on a separate password.

The baseline construction targets the following constraints; research alternatives explicitly
identify which constraints they retain or relax:

- the plaintext is a valid 12-, 15-, 18-, 21-, or 24-word BIP39 mnemonic and the encrypted
  container is a valid 24-word BIP39 mnemonic;
- the underlying transform is a permutation over all 256-bit BIP39 entropy values;
- no per-container bits are available outside that 256-bit space;
- the password is the only user-held secret required by the transform itself;
- password guessing should require memory-hard work;
- short-source recovery verification must be clearly distinguished from AEAD authentication;
- the design must not claim formal security or 24-word wrong-password detection that it does not
  actually provide.

### Practical recovery requirements

For the standard experimental suite 2 workflow, the user is not expected to memorize or separately
record the literal `SUITE_{ID}`, the BIP39 wordlist, the original short-mnemonic length, or a default
PIM. They are supplied or inferred as follows:

- The compatible MHFE implementation fixes the exact suite identifier internally.
- Experimental suite 2 uses the English BIP39 wordlist.
- Omission of PIM means the standard value `0`.
- For a 12-, 15-, 18-, or 21-word source, the encrypted recovery verifier permits automatic
  source-length detection after one inverse permutation.

In that standard workflow, the separately retained user secrets are the **MHFE password** and, only
if the original wallet used one, its distinct optional **BIP39 passphrase**. The BIP39 passphrase is
not part of MHFE and cannot be reconstructed from the container. These two secrets SHOULD NOT be
recorded next to the encrypted container.

A deliberately selected non-zero PIM is the only additional suite parameter the user must retain;
it is public and MAY be written next to the container. Users who keep the default $`\mathrm{PIM} = 0`$ do not need to record it.

The container does not identify itself as MHFE: its intended outward form is an ordinary valid
24-word English BIP39 mnemonic. Recovery therefore still requires compatible MHFE software or
knowledge that the record is an MHFE container, just as any encrypted data requires knowledge of
its format. This does not require the user to memorize the literal suite-identifier string.

Automatic length detection is extremely reliable for short sources but is probabilistic rather
than authenticated. If no short-source verifier matches, the candidate is treated as a 24-word
source. A genuine 24-word source can accidentally satisfy a short-source verifier, dominated by
the 21-word probability near $`2^{-32}`$. Recovery software SHOULD therefore expose the detected length,
MUST permit an explicit 24-word override, and SHOULD allow final comparison with a known public
address or other wallet identity data. Remembering the original length is useful corroborating
information, not a required separately stored field in the standard workflow.

No original backup should be destroyed solely because one MHFE container was created. Before an
implementation presents a container as a replacement backup, the user SHOULD complete a recovery
rehearsal and compare known public addresses or other wallet identity data using maintained wallet
software.

## Conventions and Terminology

The key words **MUST**, **MUST NOT**, **REQUIRED**, **SHALL**, **SHALL NOT**, **SHOULD**,
**SHOULD NOT**, **RECOMMENDED**, **NOT RECOMMENDED**, **MAY**, and **OPTIONAL** are to be
interpreted as described in BCP 14 when, and only when, they appear in all capitals [5], [6].

Unless a unit is explicitly stated otherwise, construction-level cryptographic sizes in formulas
and parameter tables are expressed in bits. Text may still discuss bytes, words, API-specific
units, and human-readable encodings. UTF-8, ASCII, and big-endian integer encodings retain their
standard definitions; implementations must convert units explicitly at library API boundaries.

This document uses the following terminology:

| Term                                                         | Meaning                                                                                             |
| ------------------------------------------------------------ | --------------------------------------------------------------------------------------------------- |
| `E`                                                          | source BIP39 entropy of length `ENT`                                                       |
| `ENT`                                               | source-entropy length: 128, 160, 192, 224, or 256 bits                                              |
| `r`                                                          | recovery-verifier length, $`256 - \mathrm{ENT}`$ bits                                                 |
| `V_r`                                                        | `r`-bit recovery verifier, $`\mathrm{Trunc}_{r}(\mathrm{SHA256}(E))`$; empty when $`r = 0`$ |
| `X`                                                          | 256-bit packed plaintext state, $`E \mathbin{\Vert} V_r`$                                                |
| `Y`                                                          | 256-bit encrypted BIP39 entropy                                                                     |
| `P`                                                          | MHFE password as a Unicode string                                                                   |
| `P_{encoded}`                                       | normalized UTF-8 encoding of `P`                                                                    |
| `PIM`                                               | unsigned MHFE work factor in `0...31`; omission means the default `0`                            |
| `m_{bits}`                                          | Argon2id memory cost in bits, exactly $`2^{32}`$ (512 MiB)                                            |
| `p`                                                          | Argon2id parallelism degree in lanes, exactly 4                                                     |
| `t_{base}`                                          | base Argon2id pass count, exactly 12                                                                |
| `t_{eff}`                                           | effective Argon2id pass count, $`t_{\mathrm{base}} \cdot (\mathrm{PIM} + 1)`$                         |
| `N`                                                          | Feistel round count; exactly 12 in experimental suite 2                                             |
| `i`                                                          | zero-based Feistel round index in $`0\ldotsN-1`$                                                      |
| `L_i`, `R_i`                                                 | 128-bit left and right halves before round `i`                                                      |
| `S_i`                                                        | 128-bit state-derived Argon2id salt for round `i`                                                   |
| `K_i`                                                        | 256-bit Argon2id output for round `i`                                                               |
| `M_i`                                                        | 128-bit Feistel mask for round `i`                                                                  |
| `H`                                                          | BLAKE2b configured for a 256-bit digest, used to derive `S_i`                                       |
| `SUITE_{ID}`                               | exact external suite identifier and base for internal domain separation                             |
| `DS_{SALT}`, `DS_{MASK}` | distinct ASCII domain strings for salt derivation and round-mask derivation                         |
| `RoundPRF`                                                   | HMAC-SHA-256-based keyed function producing a 128-bit mask                                          |
| $`\mathbin{\Vert}`$                                               | concatenation of encoded bitstrings                                                                 |
| `XOR`                                                        | bitwise exclusive-or on equal-length bit strings                                                    |
| `BE32(v)`                                     | unsigned 32-bit big-endian encoding of integer `v`; used for `PIM` and `i`                 |
| `Trunc_{r}(Z)`                                | first `r` bits of bitstring `Z` in digest-output order                                              |
| `Trunc_{128}(Z)`                              | first 128 bits of bitstring `Z`                                                                     |
| `Perm_{P,PIM}`                       | the complete deterministic permutation induced by password `P` and the selected PIM                 |

The 128-bit lengths of `S_i` and `M_i` do not select 128-bit variants of the underlying
cryptographic primitives. `S_i` is truncated from a 256-bit BLAKE2b digest, `K_i` is the full
256-bit Argon2id output, and `M_i` is truncated from a 256-bit HMAC-SHA-256 output. The mask must
be 128 bits because it is XORed with one 128-bit half of the fixed 256-bit Feistel state. Expanding
that mask to 256 bits would require a 512-bit state and would no longer fit a 24-word BIP39
container. Expanding the salt to 256 bits would not add independent entropy because its variable
Feistel-branch input is only 128 bits.

Common abbreviations used below are:

| Abbreviation | Meaning                                       |
| ------------ | --------------------------------------------- |
| **AEAD**     | authenticated encryption with associated data |
| **CCA**      | chosen-ciphertext attack                      |
| **DTE**      | distribution-transforming encoder             |
| **FPE**      | format-preserving encryption                  |
| **KDF**      | key-derivation function                       |
| **PRF**      | pseudorandom function                         |
| **PRP**      | pseudorandom permutation                      |
| **SPRP**     | strong pseudorandom permutation               |

## Design Status and Scope

This document separates one exact experimental suite from unresolved research alternatives.
Normative language makes experimental implementations reproducible; it does not mean that the
suite or its parameters are approved for deployment.

- **Fixed-size BIP39 input/output mapping:** baseline design requirement.
- **Universal short-source packing $`E \mathbin{\Vert} V_r`$:** principal candidate; still requires
  cryptanalysis.
- **Balanced 256-bit Feistel geometry:** baseline candidate.
- **Round count and Argon2id parameters:** fixed mapping with $`N = 12`$, $`m_{\mathrm{bits}} = 2^{32}`$ bits
  (512 MiB), $`p = 4`$, and $`t_{\mathrm{eff}} = 12 \cdot (\mathrm{PIM} + 1)`$; safety still requires analysis and benchmarking.
- **Round-mask function:** HMAC-SHA-256 truncated to 128 bits; fixed for experimental suite 2.
- **External suite identifier:** exact ASCII identifier fixed; physical recovery-card layout
  remains application-specific.
- **PIM work factor:** integer `0...31`, default `0`; it can increase but cannot reduce the
  standard cost.
- **Checksum-class cycle walking:** non-normative research alternative.
- **Source-heavy unbalanced Feistel:** non-normative research alternative.
- **Reference implementation and test vectors:** the initial Rust implementation, five $`\mathrm{PIM} = 0`$
  vectors covering every BIP39 source length, and one $`\mathrm{PIM} = 1`$ vector are available. Fast tests cover
  verifier corruption, byte and bit serialization, password byte boundaries, fixed-point rejection,
  and automatic source-length classification including multiple matches. Full Unicode 18
  normalization, broader machine-readable negative vectors, and a separately written complete
  implementation have not been completed; they would be needed before claiming mature
  interoperability.
- **Production suitability:** explicitly not established.

Readers evaluating the implementable core should start with **Specification**, then read all of
**Security Considerations**. Sections labeled as theoretical investigation or alternative designs
must not be silently combined with the baseline candidate.

This is an independent research document intended for discussion and publication in the project
author's own repository. Its organization and requirements vocabulary are informed by the BIP
process [7], [8] solely because that format is familiar and useful for technical review. **This
document is not a BIP proposal, does not request a BIP number, and does not claim or imply Bitcoin
standardization.** Its use of BIP-inspired formatting must not be interpreted as endorsement by
Bitcoin Core contributors or the BIP editors.

This document is licensed under Creative Commons Attribution 4.0 International (`CC-BY-4.0`).
The full legal text is included in the repository's `LICENSE` file. BIP 3 is cited only as a useful
precedent for document structure and freely reusable test vectors, not as a publication target for
MHFE.

### Intended execution environment

MHFE is intended for infrequent backup creation and recovery on a trusted, offline,
general-purpose computer with substantial memory. Hardware-wallet firmware, constrained embedded
devices, and other low-memory environments are outside the initial execution target. After MHFE
recovers the ordinary BIP39 mnemonic, that mnemonic can be entered into a hardware wallet through
the wallet's standard recovery procedure; the hardware wallet does not need to implement MHFE.

Experimental suite 2 defines exact resource parameters. An implementation that cannot satisfy
them MUST fail clearly and MUST NOT silently reduce the Argon2id memory or time cost. Requiring a
substantial amount of memory is intended to raise the cost of each offline password guess and to
disfavor low-memory guessing hardware. It does not prevent optimized parallel or specialized
attackers, compensate for a weak password, or establish a proven defender advantage.

## Specification

### Scope

The principal packing candidate accepts a valid **12-, 15-, 18-, 21-, or 24-word BIP39 mnemonic**
and always emits a 24-word BIP39 container. Every source length uses the same 256-bit state and the
same balanced $`128 \mid 128`$-bit Feistel core. A **source-heavy rotating unbalanced Feistel
construction (Direction B)**, which would split the same 256-bit state into $`64 \mid 192`$ bits, remains
a separate research direction rather than part of the principal candidate.

A conforming implementation MUST use the exact externally selected MHFE suite and MUST NOT
silently substitute an incompatible suite or version. Because the 256-bit container is fully
occupied, the ciphertext itself cannot carry a version identifier without changing the design
space. Compatible recovery software therefore supplies the suite; the user is not required to
memorize its literal identifier.

Within experimental suite 2, recovery software normally determines the original source length
automatically. It tests the encrypted recovery verifiers for the 12-, 15-, 18-, and 21-word
layouts after one inverse permutation. One matching short layout selects that length; if none
matches, the software falls back to the unverified 24-word interpretation. The user MAY override
automatic detection by selecting the original length explicitly, and the software MUST allow the
24-word interpretation to be forced.

### BIP39 input and output mapping

Encryption MUST begin from a valid 12-, 15-, 18-, 21-, or 24-word BIP39 mnemonic:

1. Decode the words with the English BIP39 wordlist.
2. Recover the `ENT`-bit source entropy `E` and its $`\frac{\mathrm{ENT}}{32}`$-bit BIP39 checksum.
3. Verify the source BIP39 checksum. Invalid input MUST be rejected.
4. Set $`r = 256 - \mathrm{ENT}`$.
5. If $`r > 0`$, compute $`V_r = \mathrm{Trunc}_{r}(\mathrm{SHA256}(E))`$ and set $`X = E \mathbin{\Vert} V_r`$. If $`r = 0`$, set
   $`X = E`$. SHA-256 is the function specified by FIPS 180-4 [9].
6. Apply the MHFE permutation to the 256-bit `X`, producing `Y`.
7. Compute the standard 8-bit BIP39 checksum of `Y`.
8. Encode $`Y \mathbin{\Vert} \mathrm{checksum}(Y)`$ as a 24-word mnemonic with the English BIP39 wordlist.

Decryption first performs the reverse permutation independently of the original source length:

1. Decode the encrypted 24-word mnemonic with the English BIP39 wordlist.
2. Verify its ordinary BIP39 checksum. Invalid input MUST be rejected before Argon2 work.
3. Recover the 256-bit encrypted entropy `Y`.
4. Apply the inverse MHFE permutation, producing the candidate packed plaintext state `X`.
5. If the caller explicitly selected a source length, derive `ENT` and $`r = 256 - \mathrm{ENT}`$, parse `X`
   as $`E \mathbin{\Vert} V_r`$, and verify all `r` bits when $`r > 0`$.
6. Otherwise, test the 12-, 15-, 18-, and 21-word layouts by parsing their respective $`E \mathbin{\Vert} V_r`$
   boundaries and comparing every verifier bit. A unique matching short layout is the detected
   source length. If no short layout matches, return the 24-word interpretation. Multiple matching
   short layouts MUST be reported as ambiguous rather than silently selecting one.
7. Compute the standard $`\frac{\mathrm{ENT}}{32}`$-bit BIP39 checksum of the selected `E`.
8. Encode $`E \mathbin{\Vert} \mathrm{checksum}(E)`$ with the English BIP39 wordlist and the selected word count.

When $`r = 0`$, step 6 provides no check: every 256-bit result is a possible 24-word source entropy.
For a shorter source, `V_r` is an internal **recovery verifier**. It is not an AEAD tag, MAC,
digital signature, or proof that the recovered phrase is uniquely the original phrase. It is
deterministic redundancy encrypted inside `X`; anyone who tries a password can perform the same
check after candidate decryption.

The permutation itself operates on entropy and is independent of human-language words. However,
experimental suite 2 fixes the English BIP39 wordlist for both source and container encoding, so no
wordlist identifier needs to be stored. A future profile supporting another published BIP39
wordlist requires an explicit incompatible suite identifier. BIP39 itself strongly discourages
generation with non-English wordlists [2].

### Password encoding

The MHFE password and the optional BIP39 passphrase are separate concepts and MUST NOT be
implicitly substituted for one another.

The user MUST preserve a password whose `UTF8(NFKD(P))` encoding is identical to the encoding used
at creation time. The original display string does not need to be byte-for-byte identical when two
Unicode strings normalize to the same value. The container contains no password-recovery mechanism,
and recovery-verifier bits cannot reconstruct a forgotten password.

Experimental suite 2 uses the NFKD Normalization Process for Stabilized Strings from Unicode
18.0.0, UAX #15 revision 58 [10]:

```math
\begin{aligned}
P_{\mathrm{encoded}} &= \mathrm{UTF8}(\mathrm{NPSS\text{-}NFKD\text{-}Unicode\text{-}18.0.0}(P))
\end{aligned}
```

`P` MUST be a well-formed sequence of Unicode scalar values. Normalization MUST fail if `P`
contains a code point unassigned in Unicode 18.0.0, as required by NPSS. An implementation MUST NOT
apply locale-dependent case folding, trimming, whitespace collapsing, or any transformation other
than the specified NFKD process.

The normalized UTF-8 result MUST contain from 1 through 1024 bytes inclusive. Creation and recovery
MUST reject an empty result or a result longer than 1024 bytes before any Argon2id call. They MUST
NOT truncate it. The 1024-byte ceiling is an interoperability and resource bound, not a password-
strength claim. Password-strength estimation is not a responsibility of the MHFE cryptographic
library or part of container validation. A user-facing application creating a container SHOULD
warn about weak passwords. That application MUST NOT enforce a creation-time strength policy during
recovery: recovery MUST accept every password valid under the protocol rules above so application
policy cannot strand an existing backup.

### Experimental cryptographic suite 2

The following values define `MHFE-BIP39-256-EXPERIMENTAL-2`. They are frozen for reproducible
experimental implementations and test vectors. Freezing the encoding does not establish its
security or make it suitable for protecting real funds. Any incompatible replacement MUST use a
new suite identifier and new internal domain strings.

| Component                                    | Experimental suite 2 value                                                                                                                                                                                              |
| -------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| State size                                   | 256 bits                                                                                                                                                                                                                |
| Feistel split                                | 128 bits / 128 bits                                                                                                                                                                                                     |
| Round count `N`                              | `12`                                                                                                                                                                                                                    |
| Salt hash `H`                                | BLAKE2b-256 [11]                                                                                                                                                                                                        |
| State-derived salt length                    | 128 bits                                                                                                                                                                                                                |
| KDF                                          | Argon2id, version 1.3 ($`v = \mathtt{0x13}`$)                                                                                                                                                                             |
| Argon2id memory `m_{bits}`          | $`2^{32}`$ bits = 512 MiB; RFC $`m = 524288`$ KiB                                                                                                                                                                           |
| Argon2id base passes `t_{base}`     | `12`                                                                                                                                                                                                                    |
| MHFE PIM                                     | integer `0...31`; an omitted parameter means `0`                                                                                                                                                                     |
| Argon2id effective passes `t_{eff}` | $`12 \cdot (\mathrm{PIM} + 1)`$, therefore `12...384`                                                                                                                                                                  |
| Argon2id lanes `p`                           | `4`                                                                                                                                                                                                                     |
| Argon2id output                              | 256 bits                                                                                                                                                                                                                |
| Argon2 optional secret                       | empty                                                                                                                                                                                                                   |
| Argon2 associated data                       | empty                                                                                                                                                                                                                   |
| Round mask function                          | $`\mathrm{Trunc}_{128}(\mathrm{HMAC\text{-}SHA\text{-}256}(K_i, \mathrm{DS}_{\mathrm{MASK}} \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM}) \mathbin{\Vert} \mathrm{BE32}(i) \mathbin{\Vert} R_i))`$ [9], [12] |

RFC 9106's first and second recommended Argon2id options both use $`p = 4`$, and its general
parameter-selection procedure likewise begins with four lanes [13]. Experimental suite 2
therefore selects $`p = 4`$. Reducing `p` merely to lengthen wall-clock time is not presumed to
improve password-guessing resistance: an attacker can parallelize independent password candidates,
and changing `p` changes the Argon2 function itself.

The experimental suite's default $`m_{\mathrm{bits}} = 2^{32}`$ bits (512 MiB), $`t_{\mathrm{eff}} = 12`$, $`p = 4`$ tuple is not one of RFC
9106's two recommended tuples. It retains the RFC's four-lane baseline, selects a memory cost
between the RFC's 64 MiB and 2 GiB options, and deliberately raises the pass count for an
infrequent high-cost backup operation on the stated high-memory execution target. This is an
experimental engineering choice, not a claim that multiplying passes produces a proportional
security gain against every attacker. With four lanes, 512 MiB is the total Argon2 memory,
nominally 128 MiB per lane; it is not 512 MiB per lane.

One MHFE encryption or decryption performs twelve sequential Argon2id calls. If one working buffer
is reused, its peak Argon2 allocation is nominally 512 MiB regardless of PIM. At the default
$`\mathrm{PIM} = 0`$, the nominal full-memory-pass volume is $`12 \cdot 12 \cdot 512\,\mathrm{MiB} = 72\,\mathrm{GiB}`$. In general it is
$`72\,\mathrm{GiB} \cdot (\mathrm{PIM} + 1)`$. These values are not runtime predictions or attack-cost proofs. The mapping
is exact for experimental suite 2, but its safety, upper bound, and usability remain provisional
until measured across the stated target systems and reviewed in the full construction.

### Domain separation

Experimental suite 2 uses this exact, case-sensitive external identifier:

```math
\begin{aligned}
\mathrm{SUITE}_{\mathrm{ID}} &= \mathrm{ASCII}("MHFE-BIP39-256-EXPERIMENTAL-2")
\end{aligned}
```

It derives two distinct internal domain strings:

```math
\begin{aligned}
\mathrm{DS}_{\mathrm{SALT}} &= \mathrm{SUITE}_{\mathrm{ID}} \mathbin{\Vert} \mathrm{ASCII}("/ROUND-SALT") \\
\mathrm{DS}_{\mathrm{MASK}} &= \mathrm{SUITE}_{\mathrm{ID}} \mathbin{\Vert} \mathrm{ASCII}("/ROUND-MASK")
\end{aligned}
```

None of these byte strings includes a terminating NUL character. For round `i`, derive:

```math
\begin{aligned}
S_i &= \mathrm{Trunc}_{128}( \\
\mathrm{BLAKE2b\text{-}256}(\mathrm{DS}_{\mathrm{SALT}} \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM}) \mathbin{\Vert} \mathrm{BE32}(i) \mathbin{\Vert} R_i) \\
)
\end{aligned}
```

`BLAKE2b-256` means BLAKE2b as specified by RFC 7693 [11], configured for a 256-bit digest,
not a truncation of a BLAKE2b-512 digest. `Trunc128` then selects the first 128 bits of that
256-bit digest. `R_i` is the raw 128-bit right half, not its hexadecimal or mnemonic
representation. `PIM` and the zero-based round index are each encoded as exactly 32 bits.

The explicit purpose labels, `BE32(PIM)`, and `BE32(i)` separate salt derivation from mask
derivation, different permitted work factors, other protocols, and other rounds. This does
**not** establish security against a named class of Feistel attack; it prevents accidental
reuse of one byte-level domain for different protocol roles.

`SUITE_{ID}` identifies the complete experimental cryptographic suite, not merely an editorial
revision of this document. Any incompatible change to the Feistel geometry or round count `N`;
state packing or encoding; password normalization or limits; salt derivation; the Argon2 variant,
version, fixed parameters, permitted PIM range or PIM-to-cost mapping; or `RoundPRF` MUST assign a
new `SUITE_{ID}`, `DS_{SALT}`, and `DS_{MASK}`. Selecting a different permitted PIM value under the
unchanged mapping does not define a new suite. Implementations MUST NOT reuse this identifier for a
changed mapping.

### Bit and byte serialization

Bit offsets are counted from the first, most-significant bit of the first byte. For any bitstring
whose length is a multiple of eight, bits $`Z[8j:8j+8]`$ form byte `j`, with `Z[8j]` as that byte's
most-significant bit. Digest outputs are consumed in the byte order defined by their respective
standards, and truncation always takes the leftmost bits in that order. In particular,
$`\mathrm{Trunc}_{r}(\mathrm{SHA256}(E))`$ denotes the leftmost `r` bits of the SHA-256 digest byte string. Digest bytes
retain their standard output order, and bits within each byte are consumed most-significant-bit
first, matching BIP39 checksum extraction. Implementations MUST NOT use host-native integer byte
order when extracting or comparing `V_r`.

In experimental suite 2, `K_i` is the 32-byte Argon2id output used directly as the HMAC key.
`BE32(PIM)` and `BE32(i)` are each exactly four bytes, `R_i` is exactly 16 bytes in the bit order
above, and the HMAC message is their literal concatenation after `DS_{MASK}`. The first 16 HMAC
output bytes become `M_i`. Implementations MUST NOT use host-endian integer layouts, textual hexadecimal, mnemonic
words, or implicit string terminators at any cryptographic API boundary. Test vectors MUST cover
every serialization boundary.

A **BIP39 mnemonic** is not itself the BIP39 seed. This construction packs the entropy encoded by a
valid BIP39 mnemonic into a 256-bit state. After decryption, normal BIP39 seed derivation may still
use the separate optional BIP39 passphrase.

### Round key derivation

For each round:

```math
\begin{aligned}
K_i &= \mathrm{Argon2id}( \\
\mathrm{password}    &= P_{\mathrm{encoded}}, \\
\mathrm{salt}        &= S_i, \\
\mathrm{memory}_{\mathrm{bits}} &= m_{\mathrm{bits}}, \\
\mathrm{passes}      &= t_{\mathrm{eff}}, \\
\mathrm{lanes}       &= p, \\
\mathrm{version}     &= \mathtt{0x13}, \\
\mathrm{type}        &= \mathrm{Argon2id}, \\
\mathrm{secret}      &= \mathrm{empty}, \\
\mathrm{associated\ data} &= \mathrm{empty}, \\
\mathrm{outlen}_{\mathrm{bits}} &= 256 \\
)
\end{aligned}
```

The names `memory_{bits}` and `outlen_{bits}` are specification-level notation, not literal
library API parameters. Implementations MUST convert them to the units required by the
selected Argon2 library. In RFC 9106 notation [13], $`m = \frac{m_{\mathrm{bits}}}{8192}`$ and
$`T = \frac{\mathrm{outlen}_{\mathrm{bits}}}{8}`$; the results must be integral and satisfy RFC parameter constraints.
This notation change does not change the intended KDF output length or the algorithm.

`S_i` is an actual Argon2 salt input, but it is deterministically derived from the Feistel state.
It does not add entropy and is not guaranteed to be globally unique. It is also not secret. For a
known plaintext, `R_0` and therefore `S_0` are known; when inversion begins from a ciphertext,
$`R_{N-1} = L_N`$ is likewise available from the ciphertext state. The term **state-derived salt** is
used throughout this document instead of "pseudo-salt".

### Round mask

Experimental suite 2 uses HMAC-SHA-256 as specified by RFC 2104 [12]:

```math
\begin{aligned}
M_i &= \mathrm{Trunc}_{128}( \\
\mathrm{HMAC\text{-}SHA\text{-}256}( \\
\mathrm{key}     &= K_i, \\
\mathrm{message} &= \mathrm{DS}_{\mathrm{MASK}} \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM}) \mathbin{\Vert} \mathrm{BE32}(i) \mathbin{\Vert} R_i \\
) \\
)
\end{aligned}
```

`HMAC-SHA-256` follows the HMAC construction in RFC 2104 [12] with SHA-256 from FIPS 180-4 [9].
It returns 256 bits and `Trunc128` selects the first 128 bits in digest-output order. Equivalently,
$`\mathrm{RoundPRF}(K, \mathrm{PIM}, i, R)`$ is the formula above. The explicit mask domain, PIM, and round index are
included even though `K_i` already depends on the salt domain, PIM, round index, and `R_i`; this
makes the round-mask invocation independently unambiguous.

HMAC-SHA-256 is a conventional keyed function, but the complete effective MHFE round function
derives its HMAC key from its own input through Argon2id. Selecting HMAC therefore does not prove
that the effective functions meet the independent-random-function assumptions of classical
Feistel results. That construction-specific question remains open.

### Encryption

Split the 256-bit packed plaintext state `X` into two 128-bit halves. Slice offsets below count bits
in BIP39 entropy order: `X[0:128]` is the first 128 bits and `X[128:256]` the remaining 128 bits.
The same convention applies to `Y` during decryption.

```math
\begin{aligned}
L_0 &= X[0:128] \\
R_0 &= X[128:256]
\end{aligned}
```

For each round $`i = 0, 1, \ldots, N-1`$ (where the final positive round count must fit the
zero-based `BE32` index range):

```math
\begin{aligned}
S_i &= \mathrm{Trunc}_{128}(\mathrm{BLAKE2b\text{-}256}(\mathrm{DS}_{\mathrm{SALT}} \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM}) \mathbin{\Vert} \mathrm{BE32}(i) \mathbin{\Vert} R_i)) \\
K_i &= \mathrm{Argon2id}(P_{\mathrm{encoded}}, S_i; \mathrm{memory}_{\mathrm{bits}} = m_{\mathrm{bits}}, t_{\mathrm{eff}}, p, \mathrm{outlen}_{\mathrm{bits}} = 256) \\
M_i &= \mathrm{RoundPRF}(K_i, \mathrm{PIM}, i, R_i) \\
\\[0.4em]
L_{i+1} &= R_i \\
R_{i+1} &= L_i \oplus M_i
\end{aligned}
```

The abbreviated Argon2id calls in encryption and decryption use every parameter from
**Round key derivation**, including version `0x13`, type Argon2id, and empty optional secret
and associated data. $`\mathrm{outlen}_{\mathrm{bits}} = 256`$ is converted to the actual API units as defined above.

The encrypted state, used as the 256-bit BIP39 container entropy, is:

```math
\begin{aligned}
Y &= L_N \mathbin{\Vert} R_N
\end{aligned}
```

The BIP39 output mnemonic is then generated from `Y` using the ordinary BIP39 checksum rule.

### Decryption

Split the 256-bit BIP39 container entropy `Y` as:

```math
\begin{aligned}
L_N &= Y[0:128] \\
R_N &= Y[128:256]
\end{aligned}
```

For each round $`i = N-1, N-2, \ldots, 0`$:

```math
\begin{aligned}
R_i &= L_{i+1} \\
\\[0.4em]
S_i &= \mathrm{Trunc}_{128}(\mathrm{BLAKE2b\text{-}256}(\mathrm{DS}_{\mathrm{SALT}} \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM}) \mathbin{\Vert} \mathrm{BE32}(i) \mathbin{\Vert} R_i)) \\
K_i &= \mathrm{Argon2id}(P_{\mathrm{encoded}}, S_i; \mathrm{memory}_{\mathrm{bits}} = m_{\mathrm{bits}}, t_{\mathrm{eff}}, p, \mathrm{outlen}_{\mathrm{bits}} = 256) \\
M_i &= \mathrm{RoundPRF}(K_i, \mathrm{PIM}, i, R_i) \\
\\[0.4em]
L_i &= R_{i+1} \oplus M_i
\end{aligned}
```

Recover:

```math
\begin{aligned}
X &= L_0 \mathbin{\Vert} R_0
\end{aligned}
```

The inverse works because `R_i` is available directly as $`L_{i+1}`$ before the unknown `L_i` must
be reconstructed. Therefore the state-derived salt and round key can be recomputed without a
circular dependency.

### Error handling and wrong passwords

A conforming implementation MUST distinguish outer transcription checking from internal recovery
verification:

- an invalid outer BIP39 checksum is an input-format error and MUST be rejected before any Argon2id
  evaluation;
- for a selected 12-, 15-, 18-, or 21-word source profile, the complete inverse transform yields a
  candidate $`E \mathbin{\Vert} V_r`$, and all `r` verifier bits MUST be checked;
- a verifier mismatch rejects that candidate but does not identify whether the password, PIM,
  source length, profile, or recorded data was wrong;
- a verifier match means that the candidate belongs to the selected short-source subset; a
  uniformly distributed wrong candidate passes with probability exactly $`2^{-r}`$, while the rate for
  actual wrong-password outputs depends on the still-unproven MHFE candidate distribution;
- the 24-word source profile has no internal recovery verifier, so any protocol-valid password and
  permitted PIM produce a syntactically valid 24-word candidate after its ordinary checksum is
  recomputed.

The verifier is available to an offline attacker as well as to the owner. The intended design makes
each trial expensive through the complete inverse MHFE computation and its Argon2id evaluations,
but this draft has not proved that no shortened verifier test or reduced-KDF attack exists. Wallet
identity, known addresses, descriptors, xpubs, or transaction history MAY provide additional
external verification, but they are outside the cryptographic container.

### Version and profile handling

The 256-bit permutation occupies the full container payload. No in-band version field is available
without changing the format or reserving part of the domain. Short-source recovery-verifier bits
are fully determined by `E` and MUST NOT be reinterpreted as free version or metadata capacity.

Therefore:

- this draft MUST NOT be used to create long-lived backups;
- experimental implementations MUST use the exact `SUITE_{ID}` defined here;
- the literal `SUITE_{ID}` is an implementation constant and is not a user memory requirement;
- the mnemonic does not self-identify as MHFE, so recovery software MUST NOT guess the format from
  the words alone;
- every incompatible suite revision MUST assign a distinct `SUITE_{ID}`, `DS_{SALT}`, and `DS_{MASK}` as
  required under **Domain separation**;
- implementations SHOULD support automatic short-source length detection as described under
  **Decryption** and MUST allow the caller to force the 24-word interpretation;
- an omitted PIM MUST be interpreted as `0`; every non-zero PIM MUST be preserved as external
  recovery context;
- an incompatible future design SHOULD be specified as a new protocol/BIP or otherwise use a
  distinct external identifier.

### Personal iterations multiplier

Experimental suite 2 includes an unsigned integer `PIM` in the inclusive range `0...31`. An omitted
parameter or an explicitly supplied zero selects the standard configuration:

```math
\begin{aligned}
\mathrm{PIM} &= 0 \\
t_{\mathrm{eff}} &= t_{\mathrm{base}} \cdot (\mathrm{PIM} + 1) = 12
\end{aligned}
```

For a non-zero value:

```math
\begin{aligned}
t_{\mathrm{eff}} &= 12 \cdot (\mathrm{PIM} + 1)
\end{aligned}
```

Thus $`\mathrm{PIM} = 1`$ doubles the default Argon2id pass count to 24, $`\mathrm{PIM} = 2`$ triples it to 36, and
$`\mathrm{PIM} = 31`$ selects the permitted maximum of 384 passes. Memory remains 512 MiB, lanes remain 4,
and the Feistel round count remains 12. The upper bound gives at most 32 times the default pass count;
it is a resource-safety bound for this experiment, not a cryptographic threshold. A PIM outside
`0...31` MUST be rejected before memory allocation.

A user-facing application MUST show the default as either `0` or a blank field that represents an
omitted parameter; a blank field is not a separate PIM value. It MUST NOT require the user to
remember the default value and SHOULD make the increased expected delay clear before accepting a
non-zero value.

The PIM is public recovery context, not a substitute for password entropy. The standard value does
not need to be recorded. A non-zero value MUST be recorded with the backup metadata because using
another value selects a different password-and-PIM-parameterized permutation. This is
especially important for a 24-word source, where the format cannot detect a wrong PIM
internally. Implementations MUST NOT silently search PIM values and describe an arbitrary
24-word result as verified.

## Rationale

### Why Feistel

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

The right half remains available after the round as the next left half. This property is what
allows a salt derived from `R_i` to be recomputed during decryption.

### Why experimental suite 2 uses twelve rounds

The round count is informed by results for ideal balanced random Feistel schemes, but those results
must be stated with their attack models. Patarin [14] proves near-full-branch security for seven or
more rounds against adaptive chosen-plaintext attacks; the same paper states ten or more rounds for
adaptive chosen-plaintext-and-ciphertext attacks. A later result [15] establishes its stated
chosen-plaintext-and-ciphertext bound for six or more rounds under that paper's conditions.

$`N = 12`$ is therefore the exact experimental-suite choice: it is six rounds above the six-round
threshold in [15], five rounds above the seven-round CPA threshold in [14], and two rounds above the
distinct ten-round CPCA threshold stated in [14]. These differences are engineering margins, not
proofs of equivalent MHFE security. All cited proofs assume independently sampled random round functions;
MHFE instead uses password-, PIM-, and state-dependent effective functions
`G_{i,P,PIM}`. Until a reduction or
construction-specific analysis justifies transferring a bound, twelve rounds are an engineering
candidate rather than a theorem-backed security level.

### Why state-derived salts

A conventional password-encryption format stores a random salt. The zero-metadata requirement
removes that option for the full 24-word domain. MHFE instead derives the Argon2 salt from state
that is available in both encryption and decryption.

This does not create new entropy. It provides per-state KDF diversification without storing an
additional field. For two independently sampled states compared at the same PIM and round index,
salt equality can arise either because their 128-bit `R_i` values are equal or because unequal
inputs collide after BLAKE2b-256 is truncated to 128 bits. If the branches are modeled as
independent uniform 128-bit values and BLAKE2b as a random function, the combined probability is
close to $`2^{-127}`$ for one pair. The corresponding birthday scale is approximately $`2^{63.5}`$
comparable invocations. Different PIM values or round indices make the hash inputs distinct, so
only the approximately $`2^{-128}`$ truncated-hash collision probability remains in that model.
Accidental collisions are therefore expected to be negligible at any realistic number of
containers.

These estimates are idealized: MHFE has not proved that all intermediate Feistel branches are
independent and uniformly distributed. Reprocessing the same state with the same password, PIM,
and round index also repeats the same salt by design; that deterministic repetition is not an
accidental collision. The draft therefore does not claim that every Argon2 invocation is unique or
that all forms of cross-container amortization are impossible.

### Research note: public pre-mixing of the KDF schedule

Public reversible full-state pre-mixing was considered as a way to make the first state-derived KDF
input depend syntactically on the complete source state. It is not selected by any current profile.
For a uniformly random 256-bit source, it has little apparent practical benefit: the original
128-bit right branch already gives a distinct-source pair-collision probability of $`2^{-128}`$ and a
birthday collision scale of approximately $`2^{64}`$ independently sampled sources.

Pre-mixing also cannot prevent adversarially constructed branch collisions because the transform
would be public and invertible. Nor would it add entropy or remove the deterministic relation
between the two halves of a packed short source. The idea is retained only as a record of a
considered alternative; it should not add another cryptographic operation to the principal
candidate without a demonstrated benefit and separate analysis.

### BIP39 checksum semantics

A 24-word BIP39 mnemonic contains 256 entropy bits and an 8-bit checksum, but only $`2^{256}`$
24-word sequences are valid. The checksum does not provide 8 extra payload bits.

Consequently the baseline transform operates only on the 256-bit entropy and recomputes the
standard checksum afterward. This preserves the BIP39 word count but leaves no independent room
for an authentication tag or version field.

For shorter sources, the universal packing candidate uses the otherwise unoccupied part of that
same 256-bit state for `V_r`. This does not alter the outer BIP39 rule: every encrypted container
still carries the ordinary 8-bit checksum of `Y` outside the 256-bit encrypted payload.

### Baseline and research alternatives

This document keeps one precisely identified baseline while examining competing directions.
It is not currently constrained to presenting a single finished BIP recommendation. The
research section compares balanced and source-heavy unbalanced Feistel, as well as different
payload-verification choices. Keeping alternatives in one document is intentional; an
interoperable implementation would still need to select and identify a complete profile.

## Backward Compatibility

This construction changes no Bitcoin consensus, peer-to-peer, or RPC rules. Compatibility concerns are
entirely at the wallet/application layer.

An MHFE-encrypted 24-word mnemonic is intentionally syntactically valid BIP39. A legacy wallet
that supports 24-word English BIP39 mnemonics will generally accept the encrypted
mnemonic as an ordinary mnemonic
and generally derive a different wallet from it; the construction does not rule out fixed points.
The encrypted mnemonic contains no in-band flag that says "decrypt me first".

Fixed points are an expected property of the idealized permutation model, not by themselves a
structural failure of the design. A uniformly random permutation on a finite set has exactly one
fixed point in expectation; as the set grows, its fixed-point count approaches a Poisson
distribution with parameter 1. For one particular 256-bit state `X`, however, the probability
that $`\mathrm{Perm}_{P,\mathrm{PIM}}(X) = X`$ is only $`2^{-256}`$ in that model. A ciphertext-only observer
cannot determine from `Y` alone whether it is such a fixed point of the unknown
password-and-PIM-parameterized permutation, so the existence of fixed points does not supply
a generic password test or key-recovery shortcut.

The rare equality still matters operationally because it defeats concealment for that concrete
state. For a 24-word source, $`Y = X`$ makes the encrypted mnemonic identical to the source mnemonic; for a
shorter source it would expose the complete packed state $`X = E \mathbin{\Vert} V_r`$, even though the word
counts differ. A
creating implementation SHOULD compare the input and output states, refuse to present an unchanged
state as an encrypted backup, and require the user to change the password or another explicitly
specified external diversification input. The initial Rust implementation performs this check.
Reapplying the same suite with the same password, PIM, and
input cannot escape the same fixed point. These operational checks do not replace analysis
of whether
the concrete MHFE construction behaves sufficiently like the idealized permutation.

Applications implementing MHFE MUST therefore present encrypted mnemonics as a distinct workflow
and MUST NOT silently pass them to normal BIP39 seed derivation. Users MUST retain knowledge that a
backup is MHFE-encrypted; compatible software supplies the exact suite definition rather than
requiring the user to memorize its literal identifier.

With the correct password and compatible suite implementation, MHFE decryption recovers the
original BIP39 mnemonic for use by unmodified BIP39-compatible software. For a short source, the
recovery-verifier check supplies a failure signal for most incorrect candidates; for a 24-word
source, merely completing decryption does not verify that the inputs were correct. If that wallet
also uses the optional BIP39 passphrase, the BIP39 passphrase remains an independent second input
and is applied only after MHFE decryption.

## Security Considerations

### Status and security claim

MHFE is experimental and unaudited. The present document specifies a research construction, not a
proven password-encryption primitive. No real funds should depend on this draft.

The following are explicit non-claims:

- no formal PRP/SPRP proof for the MHFE construction;
- no proof that the selected twelve rounds are sufficient;
- no proof that the Argon2id-derived effective round functions satisfy the assumptions of
  Luby-Rackoff or Patarin analyses;
- no AEAD authentication in experimental suite 2 and no internal wrong-password detection
  for a 24-word source;
- no formal honey-encryption [16] or plausible-deniability guarantee;
- no proof that an attacker must pay `N` full Argon2id evaluations for every rejected password.

### Resource exhaustion and untrusted containers

A checksum-valid 24-word input can force a decoder to perform every expensive Argon2id operation
required by the selected suite. The outer BIP39 checksum filters transcription errors but is not
authorization to consume unbounded resources. Experimental suite 2 fixes its KDF parameters and
normalized-password bound; implementations MUST additionally enforce a local resource ceiling and
fail rather than substitute cheaper parameters.

Applications SHOULD start recovery only after an explicit user action, SHOULD keep the interface
responsive during long operations, and SHOULD offer cancellation where the execution environment
permits it. A worker or background thread is a responsiveness boundary, not a cryptographic vault.
Implementations MUST reject unknown suite identifiers, PIM values outside `0...31`, and any other
caller-supplied parameter override before allocating large amounts of memory. These measures limit
denial-of-service and accidental resource use; they do not reduce the attacker's offline
password-guessing cost.

### Threat models

The following models must be kept distinct. Unless a model states otherwise, the attacker is
assumed to know the suite and public PIM. The original source length may be known, tried explicitly,
or inferred with the same recovery-verifier rules available to the owner. Known wallet identity
data can provide an external password test, especially for a 24-word source.

**T1 — single-container offline guessing.** The attacker has one encrypted entropy `Y`. A
baseline attack evaluates a candidate inverse permutation $`\mathrm{Perm}_{P',\mathrm{PIM}}^{-1}(Y)`$ for each password
guess `P'` and checks a short-source `V_r` relation or any available external evidence. This does
not imply that an optimal attacker must perform a full inversion when a cheaper filter is
available.

**T2 — same-password multi-container, ciphertext-only.** Many ciphertexts were created under the
same normalized password, PIM, and suite, but their plaintext mnemonics are unknown. This is not
automatically equivalent to a chosen-plaintext or known-pair oracle. Determinism reveals ciphertext
equality when the packed plaintext is repeated, and any attack may also consider the structured
short-source subsets, but unknown plaintexts do not become known pairs merely because many
containers are available.

**T3 — disclosed known pairs.** The attacker knows one or more specific mappings `(X_i, Y_i)`
made under the same password, PIM, and suite, for example because the plaintext mnemonic was later
disclosed or compromised by another channel. Such pairs may be used to filter password guesses or
to attack other containers governed by the same permutation.

**T4 — chosen-input oracle access.** The attacker can obtain forward transformations of chosen
plaintexts, inverse transformations of chosen ciphertexts, or both, under one fixed password, PIM,
and suite. Forward-only access is closest to classical PRP analysis, while access to both complete
directions is closest to SPRP analysis. An interface that reveals only verifier acceptance is a
weaker oracle but may still provide a useful password filter.

**T5 — cross-container aggregation under a shared weak password.** Independently leaked known
pairs from different users or wallets form one password-and-PIM-parameterized permutation only
when the same normalized password, PIM, and suite are shared. If the same weak password is reused
with different PIM values or suites, those samples belong to different permutations and do not form
one classical multi-query transcript, but they may still be combined as evidence in a dictionary
attack on the shared password by evaluating each applicable parameter set. A large corpus created
under unrelated passwords provides no such shared-password test.

**T6 — active container modification or substitution.** The attacker can replace or alter a
recorded container and recompute its ordinary BIP39 checksum. Experimental suite 2 provides no
cryptographic authentication. A short-source verifier rejects most incorrect recovered states but
does not authenticate the container or its origin; a 24-word source has no internal verifier at
all. This integrity and availability threat must be analyzed separately from offline password
guessing and confidentiality.

### Where known pairs can come from

A known pair is not free information. Realistic sources include later voluntary disclosure,
inheritance, audit, migration, independent compromise of a plaintext backup, malware observing a
later recovery, or deliberately published test material. The attacker must be able to link a
specific plaintext `X_i` to a specific encrypted container `Y_i`.

### Known-plaintext shortcut and KDF cost

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
example, omitting the only round of a one-round network gives no password-dependent filter.
The rejection rate and the best multi-round shortcut require analysis of the full construction.

In a multiround design with earlier password-dependent inexpensive rounds, making only
the last round memory-hard permits an initial known-pair password filter that omits the
expensive round. Its effectiveness still depends on the preceding rounds.

### Birthday bounds and password guessing

For a balanced Feistel network with a `2n`-bit state and `n`-bit branches, classical small-round
multi-query analyses contain birthday-scale terms around:

```math
\begin{aligned}
q ~ 2^{n/2}
\end{aligned}
```

where `q` counts queries or known/chosen pairs under one fixed permutation.

For the 128-bit same-length research variant, $`n = 64`$, giving a birthday scale around $`2^{32}`$ in
those classical games. That number must **not** be reinterpreted as "the password breaks after
$`2^{32}`$ guesses". In T1, different password guesses select different password-indexed
permutations at the selected PIM, so the guesses do not accumulate as `q` queries to one
fixed `Perm_{P,PIM}`.

The multi-query viewpoint becomes relevant only when many samples genuinely belong to the
same password-and-PIM-parameterized permutation and the attack has the information model
required by the particular proof or distinguisher.

### Patarin and beyond-birthday security

The birthday scale is not a universal ceiling for balanced Feistel networks. Patarin's positive
security results show that, with enough rounds and independent random round functions, balanced
Feistel constructions can achieve security far beyond the basic birthday scale and approach the
information-theoretic scale associated with the branch size [14], [15], [18]. Reference [17]
instead develops generic attacks on Feistel schemes; it supplies adversarial limits and comparison
context, not a proof of beyond-birthday security.

These results are important because they show that a 64-bit branch does not, by itself, imply a
hard $`2^{32}`$ security ceiling. They do **not** prove equivalent bounds for MHFE.

The relevant question for MHFE is whether its effective round functions satisfy assumptions strong
enough to justify any Patarin-style reduction.

### Effective round function

For fixed password `P`, PIM, and round index `i`, define the effective round function:

```math
\begin{aligned}
S_i(R,\mathrm{PIM}) &= \mathrm{Trunc}_{128}(\mathrm{BLAKE2b\text{-}256}(\mathrm{DS}_{\mathrm{SALT}} \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM}) \mathbin{\Vert} \mathrm{BE32}(i) \mathbin{\Vert} R)) \\
\\[0.4em]
K_i(R) &= \mathrm{Argon2id}\!\left(
\begin{gathered}
\mathrm{password}=P_{\mathrm{encoded}},\quad \mathrm{salt}=S_i(R,\mathrm{PIM}), \\
\mathrm{memory}_{\mathrm{bits}}=m_{\mathrm{bits}},\quad \mathrm{passes}=t_{\mathrm{eff}},\quad \mathrm{lanes}=p, \\
\mathrm{version}=\mathtt{0x13},\quad \mathrm{type}=\mathrm{Argon2id}, \\
\mathrm{secret}=\varnothing,\quad \mathrm{associated\_data}=\varnothing,\quad
\mathrm{outlen}_{\mathrm{bits}}=256
\end{gathered}
\right) \\
\\[0.4em]
G_{i,P,\mathrm{PIM}}(R) &= \mathrm{RoundPRF}(K_i(R),\mathrm{PIM},i,R)
\end{aligned}
```

This is exactly the same 128-bit salt, 256-bit derived key, Argon2id profile, and round-mask
function used in encryption and decryption. No Argon2 parameter or optional input is implicit in
this expanded definition. For fixed PIM, $`t_{\mathrm{eff}} = 12(\mathrm{PIM} + 1)`$ as specified by
experimental suite 2. Here `K_i(R)` is the functional form of the round key; evaluating it at the
actual branch `R_i` gives the normative round key `K_i`.

Although the internal derived subkey depends on `R`, `G_{i,P,PIM}` is still one deterministic
function from 128-bit inputs to 128-bit outputs. Therefore generic Feistel analysis cannot be
dismissed merely because the internal subkey is input-dependent.

At the same time, attacks that specifically rely on reusing one fixed internal subkey over many
`R` values do not automatically transfer unchanged to this construction.

### Argon2 salt-separation hypothesis

A potentially favorable heuristic concerns diversification across distinct `(i,R)` inputs.
Different inputs are not guaranteed to produce different 128-bit salts, and distinct salts do not
mathematically guarantee distinct 256-bit Argon2id outputs. In an ideal random-function model, two
distinct salts produce the same 256-bit output with probability $`2^{-256}`$ per pair, so accidental
output collision is not the principal concern here. Repeated `(PIM,i,R)` inputs under the
same password and suite necessarily reuse the same salt and key. If, for fixed unknown `P`, fixed
PIM (and therefore fixed `t_{eff}`), and all other experimental-suite parameters, the mapping

```math
S \longmapsto \mathrm{Argon2id}(P_{\mathrm{encoded}},S;\text{ fixed suite-2 parameters})
```

behaves with sufficient pseudorandomness and decorrelation over distinct public salts, this
might support a random-function model for the effective functions `G_{i,P,PIM}`. A useful
assumption would need to cover their joint behavior across rounds and inputs, account for salt
collisions and repeated inputs, and incorporate both the guessability of the password and behavior
across attacker-chosen password candidates. Input-dependent keys alone do not establish an
advantage over a conventional keyed round function.

This is **not a proven property used as a security claim**. Argon2id was designed and analyzed
primarily as a memory-hard password hash/KDF and for resistance to time-memory trade-offs. RFC 9106
discusses Argon2 security as a hash function and KDF, but neither cited source establishes the
construction-specific joint-pseudorandomness property that MHFE would require across many salts at
one fixed low-entropy human password. A1 is therefore a separate assumption that must be justified
or removed by a future proof or construction [13], [19].

Call this open assumption **A1 — Argon2 salt-separation hypothesis**.

### Argon2id and side channels

Argon2id combines data-independent and data-dependent memory addressing: slices 0 and 1, the first
half of the first pass, follow the Argon2i-style data-independent strategy, while the remaining
computation uses Argon2d-style data-dependent addressing. It is therefore inaccurate to
characterize Argon2id's memory-addressing pattern as uniformly data-independent or uniformly
data-dependent [13].

Implementations SHOULD use a well-reviewed Argon2id library, follow its memory-wiping facilities
where available, and separately analyze timing/cache exposure on the target platform. Native
desktop and browser/WASM implementations may have different side-channel constraints even on
otherwise supported high-memory systems.

### Recovery verification is not authentication

A reversible mapping over all $`2^{256}`$ entropy values consumes the entire 256-bit output domain. A
separate authentication tag cannot be embedded without reserving some outputs, adding external
bits, or giving up full-domain bijectivity.

The ordinary 8-bit BIP39 checksum on the encrypted mnemonic detects many accidental transcription
errors; a uniformly random 264-bit candidate passes that relation with probability $`2^{-8}`$. It is
not a cryptographic authentication tag. An attacker can modify the 256-bit entropy and recompute a
valid checksum. Likewise, the checksum recomputed after decryption cannot validate the MHFE
password because every 256-bit candidate entropy has one corresponding valid BIP39 checksum.

Short-source profiles deliberately reserve a strict subset of the 256-bit plaintext domain by
requiring $`X = E \mathbin{\Vert} \mathrm{Trunc}_{r}(\mathrm{SHA256}(E))`$. A uniformly random recovered state satisfies
that relation with probability $`2^{-r}`$, so the verifier detects most wrong-password candidates and
untargeted corruption under the corresponding uniform-candidate model. It nevertheless remains an
unkeyed relation inside the encrypted plaintext. It does not provide AEAD authenticity, establish
the container's origin, protect against every maliciously constructed replacement, or conceal from
an offline attacker whether a fully decrypted password candidate passed the same relation.

### Determinism and equality leakage

For one fixed password, PIM, and plaintext entropy, the ciphertext is deterministic:

```math
\begin{aligned}
\mathrm{Perm}_{P,\mathrm{PIM}}(X) &= Y
\end{aligned}
```

with no nonce. Re-encrypting the same `X` under the same normalized `P` and the same PIM yields the
same `Y`. Because `Perm_{P,PIM}` is a bijection, the converse also holds within one fixed
suite, password, and PIM: equal ciphertexts imply equal packed plaintexts. An observer who knows
that two containers use that same permutation can therefore recognize reuse of one packed state,
although the state itself remains unknown. This normally indicates reuse of one source; the rare
case in which one packed state satisfies more than one short-source layout remains subject to the
source-length ambiguity rule.

Ciphertext equality across different passwords, PIM values, or suites does not establish plaintext
equality because those settings select different permutations. For two independently and uniformly
sampled BIP39 sources of the same `ENT`-bit length, the pairwise source-equality probability
is $`2^{-\mathrm{ENT}}`$; even the shortest supported 128-bit source therefore has probability
$`2^{-128}`$ for one pair and a birthday scale near $`2^{64}`$ sources. Accidental equality is
negligible at realistic scales, but deliberate reuse remains visible under one fixed permutation.

### Password quality

Memory-hard KDF evaluations are intended to raise offline-guessing cost; they do not create
entropy in a weak human password. Effective guessing cost depends on the unavoidable KDF
evaluations, password quality, available verification, and any structural shortcut that reduces
the required Argon2 work per guess.

### Sensitive-memory handling

Implementations SHOULD minimize copies of plaintext entropy, encoded password, Argon2 outputs, and
intermediate Feistel states, and SHOULD erase such buffers when the language/runtime provides a
reliable mechanism. This is an implementation hygiene requirement, not a substitute for analysis
of the cryptographic construction.

## Related Work and Alternatives

### SLIP-0039

SLIP-0039 is especially relevant prior art [20]. Its master-secret encryption already uses a four-round
Feistel network in which PBKDF2 acts as the round function and the current right half `R` is included
in the PBKDF2 salt. In its extendable-backup mode the additional salt prefix is empty; the right
half remains part of the PBKDF2 salt.

Therefore the broad idea "Feistel + password KDF + current Feistel half in the KDF salt" is **not
novel to MHFE**. Any novelty claim must be narrower and should focus, if justified, on the exact
combination of a full 256-bit BIP39 entropy permutation, no in-band per-container metadata,
Argon2id memory hardness, and the resulting security/compatibility analysis.

SLIP-0039 differs materially in purpose and format: it is a Shamir mnemonic-sharing standard with
its own identifier, extendable-backup flag, iteration exponent, wordlist, and share structure. It
does not define an in-place 24-word BIP39-to-BIP39 encryption format.

### BIP38

BIP38 standardizes passphrase-protected private keys and uses scrypt plus AES [21]. It stores format
information and a 32-bit address hash inside an expanded encoded record. This provides useful
prior art for password normalization, KDF parameterization, test vectors, and wrong-password
verification, but it does not satisfy the zero-expansion 24-word requirement.

### BIP39 optional passphrase

BIP39 itself already gives every mnemonic/passphrase pair a valid derived seed, without a
built-in passphrase-error signal. This can support deniability in some contexts, but known
wallet information can still verify a guess. That mechanism affects seed derivation, not
encryption of the mnemonic backup [2].
MHFE must not be presented as a replacement for the BIP39 passphrase; the two can coexist.

### Honey encryption

Juels and Ristenpart formalize honey encryption for low-min-entropy keys by using a
distribution-transforming encoder so that decryption under wrong keys yields plausible messages
[16]. This is the relevant source for the term, but it does not describe MHFE's present security
claim. MHFE has no distribution model or encoder for wallet entropy; known wallet addresses can
verify a candidate; and the short-source recovery verifier intentionally rejects almost all
wrong-password candidates. Syntactically valid BIP39 output is therefore not sufficient to claim
honey-encryption security or formal plausible deniability.

### Earlier BIP39 backup-encryption and obfuscation proposals

A 2021 Bitcoin Stack Exchange discussion asked directly how an existing BIP39 mnemonic could be
encrypted into another mnemonic without changing the recovered wallet seed and linked a small
AES-CTR prototype [3], [4], [22]. This is direct community history for the problem statement. The initial
prototype derived its AES key as $`\mathrm{SHA256}(\mathrm{password})`$; a later revision changed that step to
PBKDF2-HMAC-SHA512 with 2,048 iterations and the fixed salt `mnemonic-encryption`. Both revisions
use AES-CTR with an all-zero IV. Reusing one password therefore repeats the CTR keystream, so for
two source entropies `E_1` and `E_2` and their ciphertext entropies `C_1` and `C_2`:

```math
\begin{aligned}
C_1 \oplus C_2 &= E_1 \oplus E_2
\end{aligned}
```

The relation alone does not recover either of two independently random and otherwise unknown
entropies. If either entropy is known or attacker-controlled, however, it reveals the other one
directly. This is separate from the cost of deriving the password key and violates CTR's
cross-message counter-block uniqueness requirement [23]. The prototype was not a bitcoin-dev
mailing-list proposal, and its fixed keystream and lack of a standardized authenticated format do
not make it cryptographic precedent for MHFE. MHFE is intended to avoid this particular relation
through a password-indexed permutation and state-derived round inputs; that contrast is a design
motivation, not a security proof for MHFE.

`Seedshift`, `bip39_obfuscator`, and `BIP39Colors` are community projects for shifting BIP39 word
indices or re-encoding them as Traditional Chinese wordlist code points or RGB colors [24], [25], [26].
They illustrate demand for backups that do not visibly expose the original English words, but they
provide forms of concealment rather than comparable modern encryption. `bip39_obfuscator` applies
a public, deterministic index-for-index mapping with no secret key; anyone who recognizes the
representation can reverse it. `BIP39Colors` likewise uses a public deterministic encoding that
packs the positions of 12 or 24 BIP39 words into 8 or 16 hexadecimal RGB colors and includes enough
position information to recover the words even when the colors are reordered [26]. It has no
secret key and therefore provides visual obfuscation rather than confidentiality against an
informed observer. `Seedshift` applies manually computable modular shifts derived from dates. Its
own documentation warns that the result is not cryptographically secure and can be brute-forced
[24]. None of these constructions uses a memory-hard KDF or provides a security argument for a
password-indexed pseudorandom permutation. They should therefore be treated as public re-encodings,
obfuscation, or a simple shift cipher, not as substitutes for reviewed mnemonic encryption. This
comparison does not itself establish the security of MHFE.

`MnemonicCrypt` is a closer implemented comparison: it removes the source BIP39 checksum, applies
configurable Argon2id and AES-CBC with a separate random 128-bit salt, and renders the ciphertext
and salt as word sequences [27]. For a 12-word source it produces a 24-word encrypted mnemonic
plus a 12-word salt mnemonic, or 36 words of total recovery material. For a 24-word source it
produces a 36-word encrypted mnemonic plus a 12-word salt mnemonic, or 48 words in total. The KDF
parameters must also be preserved separately. Its padded representation is intentionally an
extension of BIP39 rather than an ordinary wallet-generated mnemonic. It therefore addresses
password hardening and word-oriented storage, but not MHFE's fixed 24-word, no-in-band-metadata
design constraint.

Other mnemonic encryption systems reserve capacity or change the mnemonic domain. `Mnemonikey`
encodes a 128-bit OpenPGP seed in a custom 4,096-word list; its encrypted 16-word form carries a
version, creation time, random salt, encrypted seed, checksum, and a 5-bit password verifier, and
derives its AES-128 key with Argon2id [28]. `pktseed` defines a custom 15-word PKT seed containing
version, encryption, checksum, birthday, and seed fields [29]. Its current encryption code derives
a 19-byte mask from Argon2id with a fixed salt and XORs that mask with the birthday-and-seed
payload, so same-passphrase reuse creates a cross-record XOR relation analogous to the Niondir
prototype. These are useful comparisons for compact mnemonic metadata and recovery verification,
but neither transforms an existing BIP39 mnemonic into another BIP39 mnemonic.

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
  uniform-candidate false-acceptance probability $`2^{-128}`$, $`2^{-96}`$, $`2^{-64}`$, or $`2^{-32}`$,
  respectively, without expanding the container;
- no mandatory separately stored salt, nonce, authentication tag, or expansion words; the standard
  PIM is implicit, while a deliberately selected non-zero PIM remains public recovery context; and
- a memory-hard, state-derived KDF schedule inside a format-preserving permutation.

This search result narrows the known comparison set; it is not an exhaustive prior-art search, a
novelty claim, or evidence that MHFE is secure.

### Luby-Rackoff and Patarin

Luby-Rackoff supplies the foundational theory for constructing pseudorandom permutations from
round functions. Patarin's later work is relevant to generic attacks and beyond-birthday security
for multi-round balanced and unbalanced Feistel schemes. These papers define the PRP/SPRP models and
Feistel bounds against which MHFE should be evaluated.
Their proofs assume independent idealized round functions. MHFE instead derives every effective
round function from one password and state-dependent Argon2id inputs, so their security bounds
cannot be claimed for MHFE without a separate construction-specific reduction [14], [15], [17],
[18], [31].

### Format-preserving encryption

General FPE constructions demonstrate how to build permutations on constrained domains [32], but they
do not by themselves provide memory-hard password guessing or solve the no-metadata salt problem.
Morris, Oberschelp, and Santhakumar construct a no-expansion pseudorandom permutation in the bounded
retrieval model using a large key, random-oracle assumptions, and the Thorp shuffle [33]. Its hybrid
analysis and explicit treatment of uniform distinct messages are relevant methodology, but its
leakage model, key structure, round function, and security game differ materially from MHFE. It
therefore supplies related technique, not a security reduction for this proposal.

### Thorp and maximally unbalanced Feistel

Thorp-style constructions are important prior art for very small domains and show that the birthday
behavior of a small balanced branch is not a universal limitation of all Feistel architectures.
Published Thorp bounds [34] use many cheap micro-rounds. Substituting a full Argon2id invocation
for every micro-round can require hundreds or more expensive calls at these state sizes,
depending on the selected bound and target security. This suggests a substantial latency
problem, but neither a practical latency figure nor a universal minimum round count follows
without choosing and analyzing a specific construction. Whether a memory-hard key can safely
control a whole pass of cheap unbalanced rounds without reintroducing a state/salt circular
dependency remains an open research question.

## Theoretical Investigation and Alternative Designs

The following alternatives are part of the research scope of this document. They are not
production recommendations or finalized encodings. Balanced $`128 \mid 128`$-bit Feistel remains
the main 256-bit candidate; the source-heavy 1:3 family is the second direction under study.
Unless explicitly labeled otherwise, sizes in the construction formulas and tables below are
expressed in bits.

### Shorter BIP39 mnemonics

BIP39 entropy sizes are:

| Words | ENT | BIP39 checksum | Full mnemonic bits | Spare bits after storing ENT only |
| ----: | --: | -------------: | -----------------: | --------------------------------: |
|    12 | 128 |              4 |                132 |                               128 |
|    15 | 160 |              5 |                165 |                                96 |
|    18 | 192 |              6 |                198 |                                64 |
|    21 | 224 |              7 |                231 |                                32 |
|    24 | 256 |              8 |                264 |                                 0 |

The last column assumes that the original checksum is discarded and later recomputed. It
does not describe capacity after storing the complete original word bitstring.

A balanced Feistel transform operating directly on each `ENT`-bit source entropy would use
branch sizes of 64, 80, 96, 112, and 128 bits respectively. The 64-bit branch of a 12-word mode does
not automatically imply a $`2^{32}`$ password
security ceiling; classical birthday bounds and password guessing are different attack models, and
Patarin-style results show that multi-round Feistel can exceed the basic birthday regime in ideal
models. Nevertheless, every shorter state size would require separate analysis.

### Universal 24-word containers for shorter sources

The universal packing candidate uses one formula for every standard BIP39 source length:

```math
\begin{aligned}
\mathrm{ENT} &= bit length of source entropy E \\
r   &= 256 - \mathrm{ENT} \\
\\[0.4em]
V_r &= \mathrm{Trunc}_{r}(\mathrm{SHA256}(E)) \\
X   &= E \mathbin{\Vert} V_r
\end{aligned}
```

When $`\mathrm{ENT} = 256`$, $`r = 0`$, `V_r` is the empty bitstring, and $`X = E`$. For every shorter source,
the source entropy is retained exactly and every remaining position in the 256-bit state is filled
by deterministic recovery-verifier bits. No independent checksum field, second custom check, tag,
padding rule, or random filler is added.

| Source words | `ENT` | `r` | Packed state `X`                                                                  | Uniform-candidate verifier acceptance |
| -----------: | -------------: | --: | --------------------------------------------------------------------------------- | ------------------------------------: |
|           12 |            128 | 128 | $`E_{128} \mathbin{\Vert} \mathrm{Trunc}_{128}(\mathrm{SHA256}(E_{128}))`$ |                            $`2^{-128}`$ |
|           15 |            160 |  96 | $`E_{160} \mathbin{\Vert} \mathrm{Trunc}_{96}(\mathrm{SHA256}(E_{160}))`$  |                             $`2^{-96}`$ |
|           18 |            192 |  64 | $`E_{192} \mathbin{\Vert} \mathrm{Trunc}_{64}(\mathrm{SHA256}(E_{192}))`$  |                             $`2^{-64}`$ |
|           21 |            224 |  32 | $`E_{224} \mathbin{\Vert} \mathrm{Trunc}_{32}(\mathrm{SHA256}(E_{224}))`$  |                             $`2^{-32}`$ |
|           24 |            256 |   0 | `E256`                                                                            |                  No internal verifier |

This construction exploits a direct relationship with BIP39. For a source entropy of length `ENT`,
the ordinary BIP39 checksum is:

```math
\begin{aligned}
\mathrm{CS} &= \mathrm{Trunc}_{\frac{\mathrm{ENT}}{32}}(\mathrm{SHA256}(E))
\end{aligned}
```

Because `V_r` is a longer prefix of that same digest for every short source, its first $`\frac{\mathrm{ENT}}{32}`$
bits are exactly the original BIP39 checksum. The remainder extends the same check:

| Source words |       Original BIP39 checksum inside `V_r` | Additional verifier bits | Total `V_r` |
| -----------: | -----------------------------------------: | -----------------------: | ----------: |
|           12 |                                          4 |                      124 |         128 |
|           15 |                                          5 |                       91 |          96 |
|           18 |                                          6 |                       58 |          64 |
|           21 |                                          7 |                       25 |          32 |
|           24 | Not present in `V_r`; recomputed on output |                        0 |           0 |

The important economy is conceptual and structural: the source checksum is not stored twice, and
all remaining capacity becomes one continuous verifier. For example, the 21-word profile does not
store a 7-bit checksum plus a separate 25- or 32-bit field. It stores one 32-bit SHA-256 prefix
whose first 7 bits already are the source checksum and whose remaining 25 bits strengthen recovery
screening.

The full data path is:

```text
source entropy E
    || Trunc_(256-ENT)(SHA256(E))
                    |
                    v
      256-bit packed plaintext X
                    |
              MHFE Perm_{P,PIM}
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
of the encrypted container and detects many recording or transcription errors before decryption.
The outer checksum contributes no additional wrong-password rejection because it is computed from
`Y` and can be recomputed by anyone.

The measurable reasons to continue studying this short-source packing are recovery verification,
probabilistic source-length detection, complete use of otherwise unoccupied payload capacity, and
the hypothesized near-full-width marginal distribution of the first-round KDF context. Its explicit
costs are known redundancy, an offline password oracle after candidate decryption, and a structured
and correlated initial Feistel state. The last property is an analysis requirement; adding another
public hashing or mixing layer would not remove the deterministic relation.

#### Recovery-verifier properties

For one explicitly selected short source length, recovery parses `X` into $`E \mathbin{\Vert} V_r`$ and accepts
the candidate only if:

```math
\begin{aligned}
V_r &= \mathrm{Trunc}_{r}(\mathrm{SHA256}(E))
\end{aligned}
```

All `r` bits are compared. For uniformly distributed candidate `X`, the set of states satisfying
this relation has exactly $`2^{\mathrm{ENT}}`$ members among $`2^{256}`$, because each possible `E` determines one
and only one `V_r`. Its acceptance fraction is therefore exactly $`2^{-r}`$; this counting statement
does not require treating SHA-256 as a random oracle. Applying that fraction to actual
wrong-password decryptions does require an appropriate assumption about the MHFE permutation's
candidate distribution.

`V_r` is an unkeyed **recovery verifier**, not AEAD, and does not authenticate the container or its
origin. Anyone can alter `Y` and recompute the visible outer BIP39 checksum. Without the password,
however, that party cannot in general choose the resulting decrypted `X` or recompute a valid
verifier inside the encrypted plaintext; under the uniform-candidate model, an altered candidate
passes with probability $`2^{-r}`$. A party that knows the password can construct a different valid
container. Both the owner and an offline attacker testing password candidates can evaluate `V_r`
after candidate decryption. The intended cost control is that obtaining the candidate requires the
MHFE inverse and its memory-hard Argon2id evaluations; whether the structured state permits a
shortcut using fewer KDF evaluations is an explicit open research question.

The verifier does not add source entropy. A 12-word source still has 128 bits of source entropy,
not 256, even though its packed state is 256 bits wide. Its remaining 128 bits are completely
determined by `E`.

#### Fixed $`128 \mid 128`$ state structure

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
feeds the first state-derived salt. This makes one fixed implementation possible and avoids
separate 64-, 80-, 96-, and 112-bit balanced cores. It does not create independent entropy or by
itself prove stronger Feistel security. Dependencies among round inputs, repeated salts,
related structured states, and shortened password-testing paths still require analysis.

For a uniformly random source, the final table column is exact rather than approximate. Let
`\mathsf{H}` denote Shannon entropy in bits, distinct from the salt-hash symbol `H`. Write
$`E = L_0 \mathbin{\Vert} T_t`$, where $`t = \mathrm{ENT} - 128`$. The packing copies `T_t` verbatim into `R_0` and appends a
deterministic hash prefix. For each fixed `L_0`, different `T_t` values therefore produce different
`R_0` values, so:

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

##### Early whole-source sensitivity and the structured plaintext domain

The verifier provides one concrete early whole-source-sensitivity property. A conventional
balanced Feistel round function sees only `R_0`, and MHFE likewise forms its first state-derived KDF
input from `R_0`. In each short-source profile here, however, the hash-derived suffix of `R_0` is
computed from all source entropy `E`. Under the hash-prefix heuristic stated below, the first
state-derived salt is therefore sensitive to changes in either original half.

For a change confined to `L_0`, the raw entropy tail in `R_0` remains fixed and sensitivity comes
from `V_r`. Under the heuristic that the relevant SHA-256 prefix behaves like a uniform `r`-bit
value, the probability that this verifier suffix remains unchanged is $`2^{-r}`$: $`2^{-128}`$,
$`2^{-96}`$, $`2^{-64}`$, or $`2^{-32}`$ for 12-, 15-, 18-, or 21-word sources respectively. If `R_0` changes, the
subsequent 128-bit salt hash is also expected to change except for its own collision probability.
These are sensitivity and collision heuristics, not proofs of cipher security.

This property comes with a structured plaintext domain. For each short source length, valid packed
states form the set:

```math
\mathcal{S}_{\mathrm{ENT}} =
\left\{ E \mathbin{\Vert}
\mathrm{Trunc}_{256-\mathrm{ENT}}(\mathrm{SHA256}(E))
\;\middle|\; E \in \{0,1\}^{\mathrm{ENT}} \right\}
```

$`\mathcal{S}_{\mathrm{ENT}}`$ contains exactly $`2^{\mathrm{ENT}}`$ states and occupies the fraction
$`2^{\mathrm{ENT}-256}`$ of the complete 256-bit domain. It is a structured subset, specifically
the graph of a deterministic truncated-hash function; it is not generally a linear subspace.

That restricted size is not a special price paid for early whole-source sensitivity. It is
mathematically unavoidable for any lossless encoding of an `ENT`-bit source into a
256-bit container: there are only $`2^{\mathrm{ENT}}`$ distinct sources to place in $`2^{256}`$ possible
states. The hash-based construction chooses how those states are distributed and simultaneously
supplies recovery verification and early whole-source sensitivity.

A permutation satisfying full-domain PRP security remains indistinguishable when an adversary
restricts its queries to a structured subset. The existence of $`\mathcal{S}_{\mathrm{ENT}}`$ is
therefore not by itself evidence of a weakness. MHFE, however, has not been proven to satisfy that
premise, and its KDF schedule depends on the evolving state.
The structured-domain question is consequently directly relevant to every short-source profile:
analysis must determine whether the public relation defining $`\mathcal{S}_{\mathrm{ENT}}`$ enables
related-input, known-pair, or reduced-KDF password tests. This requirement neither cancels the
early-sensitivity effect nor treats that effect as proof of additional security.

##### Collision-diversity hypothesis for the first state-derived salt

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

| Source words | `R_0` construction                                                                            | Heuristic distinct-source pair-collision probability |
| -----------: | --------------------------------------------------------------------------------------------- | ---------------------------------------------------: |
|           12 | $`\mathrm{Trunc}_{128}(\mathrm{SHA256}(E_{128}))`$                                  |                             approximately $`2^{-128}`$ |
|           15 | $`E_{\mathrm{tail},32} \mathbin{\Vert} \mathrm{Trunc}_{96}(\mathrm{SHA256}(E_{160}))`$ |     approximately $`2^{-32} \cdot 2^{-96} = 2^{-128}`$ |
|           18 | $`E_{\mathrm{tail},64} \mathbin{\Vert} \mathrm{Trunc}_{64}(\mathrm{SHA256}(E_{192}))`$ |     approximately $`2^{-64} \cdot 2^{-64} = 2^{-128}`$ |
|           21 | $`E_{\mathrm{tail},96} \mathbin{\Vert} \mathrm{Trunc}_{32}(\mathrm{SHA256}(E_{224}))`$ |     approximately $`2^{-96} \cdot 2^{-32} = 2^{-128}`$ |
|           24 | `E_{tail,128}`                                                                       |           $`2^{-128}`$ for independent uniform sources |

The $`2^{-128}`$ entries describe the probability that one distinct independently sampled pair has the
same `R_0`; they do not mean that collisions require $`2^{128}`$ samples. The corresponding birthday
scale is approximately $`2^{64}`$ independent sources.

The first state-derived salt is:

```math
S_0 = \mathrm{Trunc}_{128}\!\left(
  \mathrm{BLAKE2b\text{-}256}\!\left(
    \mathrm{DS}_{\mathrm{SALT}}
    \mathbin{\Vert} \mathrm{BE32}(\mathrm{PIM})
    \mathbin{\Vert} \mathrm{BE32}(0)
    \mathbin{\Vert} R_0
  \right)
\right)
```

Its dependence on `R_0` may provide close to full-width diversification across containers. For
two distinct containers using the same suite and PIM, an idealized random-function calculation
allows pairwise equality of `S_0` to arise either from equal `R_0` values or from a hash collision
between unequal values. Using the preceding $`2^{-128}`$ heuristic for equal `R_0`, the combined
probability is $`2^{-128} + (1 - 2^{-128})2^{-128} = 2^{-127} - 2^{-256}`$, which is close to
$`2^{-127}`$ rather than exactly $`2^{-128}`$. This does not add source entropy or establish a security
level; it only makes the two collision mechanisms explicit. This is a research hypothesis, not a
proven independence or security result. In particular, conditional on `L_0`, the source entropy
remaining in `R_0` is still only 0, 32, 64, 96, or 128 bits as shown above. The effect may reduce
accidental salt reuse; it does not increase source entropy, password entropy, or establish stronger
Feistel security.

#### Source-length identification

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
source length and recovers the corresponding `E`. If multiple relations pass, it MUST report an
ambiguous result. If none passes, it returns the complete 256-bit state as a 24-word source
candidate, but MUST label that fallback as unverified rather than as confirmation of the password.
The decoder MUST also permit an explicit 24-word override when a short relation passes.

Perfect self-description is impossible while the 24-word source mode covers all $`2^{256}`$ plaintext
states. Every packed short state is also a possible 256-bit entropy value for some 24-word source.
Therefore failure of all short checks means only "no short profile was verified"; treating the
state as a 24-word source remains an unverified interpretation, not proof of a correct password.
For a uniformly distributed 256-bit candidate, including an independently generated 24-word source
under the model above, the individual accidental verifier-relation match rates are:

| Short relation tested | Probability |                                    Approximate frequency |
| --------------------- | ----------: | -------------------------------------------------------: |
| 21 words              |   $`2^{-32}`$ |                                       1 in 4,294,967,296 |
| 18 words              |   $`2^{-64}`$ |                          1 in 18,446,744,073,709,551,616 |
| 15 words              |   $`2^{-96}`$ |              1 in 79,228,162,514,264,337,593,543,950,336 |
| 12 words              |  $`2^{-128}`$ | 1 in 340,282,366,920,938,463,463,374,607,431,768,211,456 |

The probability that at least one short relation passes is bounded by:

```math
\begin{aligned}
2^{-32}
&\le \Pr[\text{at least one short relation passes}] \\
&\le 2^{-32} + 2^{-64} + 2^{-96} + 2^{-128}
\end{aligned}
```

The $`2^{-32}`$ term from the 21-word profile dominates, so the probability of at least one accidental
short-relation match is approximately $`2^{-32}`$, or about one in 4.29 billion. This is strong
probabilistic screening for accidental uniform candidates, not exact type information. A deliberately
constructed 24-word entropy can equal a valid packed short state with certainty. Under the
uniform-candidate heuristic, a wrong-password candidate reaches the unverified 24-word fallback
unless it produces one or more accidental short matches; the actual distribution of MHFE
wrong-password outputs is not proven uniform. This auto-detection bound also does not replace the
stronger selected-profile rate, such as $`2^{-128}`$ when the decoder explicitly checks a 12-word
source.

#### Checksum-preserving cycle walking for 24-word sources

The capacity result above rules out an **additional independent checksum verifier** in the
full-domain 24-word source profile. It does not rule out preserving the source checksum as a visible
property of the container. Cycle walking over checksum classes provides one research path [35].
Let `CS(E)` denote the 8-bit BIP39 checksum of 256-bit entropy `E`, and let
`Perm_{P,PIM}` be one fixed MHFE permutation.

Encryption applies the permutation at least once and continues until the result has the source
checksum:

```text
Y = Perm_{P,PIM}(X)
while CS(Y) != CS(X):
    Y = Perm_{P,PIM}(Y)
```

Decryption applies the inverse at least once and continues until the candidate has the container's
checksum:

```text
X_candidate = inverse(Perm_{P,PIM})(Y)
while CS(X_candidate) != CS(Y):
    X_candidate = inverse(Perm_{P,PIM})(X_candidate)
```

The first application is mandatory because the starting value already belongs to its own checksum
class. Both directions move between consecutive members of the same subset on one permutation
cycle, so the construction is reversible and needs no stored counter. If the permutation behaves
ideally and the checksum classes have density close to $`2^{-8}`$, the expected work is approximately
256 complete forward or inverse permutations. This is an average research estimate, not a strict
execution bound or an MHFE benchmark.

That multiplier can make the construction impractical as soon as one complete MHFE permutation is
intentionally slow. The initial native measurement reported under **Reference Implementation**
took approximately 60 seconds for one complete forward or inverse permutation. Using that
single-machine observation only as an illustration, the mean cycle-walking time would be:

```math
\begin{aligned}
256 \cdot 60\ \mathrm{s} &= 15{,}360\ \mathrm{s} = 4\ \mathrm{h}\ 16\ \mathrm{min}
\end{aligned}
```

The mean also hides a long tail. Under the same idealized independent-hit approximation, the number
of complete permutations `J` is geometrically distributed with success probability
$`\rho = \frac{1}{256}`$:

```math
\begin{aligned}
\Pr[J > k] \approx (255/256)^k
\end{aligned}
```

|       Statistic | Complete permutations | At approximately 60 seconds each |
| --------------: | --------------------: | -------------------------------: |
|  Expected value |                   256 |                       4 h 16 min |
| 95th percentile |                   766 |                      12 h 46 min |
| 99th percentile |                 1,177 |                      19 h 37 min |

Termination is guaranteed only by the finite-domain cycle bound: the walk returns within the
length of the starting permutation cycle, so at most $`2^{256}`$ complete permutations are required.
There is no comparably small deterministic bound; the distance to the next member of a checksum
class can be vastly larger than 256. The construction can also return $`Y = X`$ without a one-step
fixed point if `X` is the only member of its checksum class encountered before that cycle closes.
Consequently the average of 256 must not be used as an interactive latency guarantee. With a
multi-second memory-hard profile, this variant is unlikely to be practical for routine encryption or recovery. Its input- and password-dependent
iteration count also creates an availability risk and a variable-time side-channel surface that
would require separate analysis. A worker, progress display, or cancellation control could keep a
user interface responsive, but would not reduce the cryptographic work.

##### Known-pair composition across cycle-walking iterations

Cycle walking changes the known-pair problem from one exposed application of
`Perm_{P,PIM}` into a stopped iteration of the same password-and-PIM-parameterized permutation. Write:

```math
\begin{aligned}
W_0 &= X \\
W_j &= \mathrm{Perm}_{P,\mathrm{PIM}}(W_{j-1}) \\
\tau &= \min\{j \ge 1 : \mathrm{CS}(W_j) = \mathrm{CS}(W_0)\} \\
Y &= W_\tau
\end{aligned}
```

Under threat model T3, an attacker may know the cycle-walking endpoints `(X,Y)`. Except when
$`\tau = 1`$, those endpoints are not an adjacent pair $`(W_{j-1},W_j)`$ for one application of
`Perm_{P,PIM}`. Unless exposed through timing or instrumentation, the
intermediate states and `tau` remain hidden. The single-permutation Feistel shortcut described above therefore cannot simply be
applied independently `tau` times: each application would require an adjacent internal pair that
the attacker does not initially possess.

The opposite assumption is also unjustified. All iterations reuse the same
`Perm_{P,PIM}`, password, PIM, and suite; they are not independently keyed layers. The stopping rule also
reveals a structured transcript condition:

```math
\begin{aligned}
\mathrm{CS}(W_j) &\ne \mathrm{CS}(X)
  \quad \text{for } 1 \le j < \tau \\
\mathrm{CS}(W_\tau) &= \mathrm{CS}(X)
\end{aligned}
```

A construction-specific analysis must determine whether a meet-in-the-middle computation, a
Feistel invariant spanning several applications, repeated state-derived salts, or the checksum
non-membership conditions can test a password while omitting expensive rounds in more than one
application. Any such saving must be analyzed jointly with the number of cycle-walking iterations;
neither multiplying the one-permutation shortcut by 256 nor charging 256 independent full attacks
is a justified cost model.

Timing can expose an additional filter even before such a shortcut is found. In the idealized
geometric model with checksum-match probability $`p_{\mathrm{match}} = \frac{1}{256}`$, let the
observed correct stopping time be `tau` and the stopping time under an independent wrong-password trajectory be
`tau'`. If an exact iteration count can be associated with `Y`, this timing-only filter does not
require knowledge of `X`: an attacker can inverse-walk from `Y` under each password guess and
compare its first-return count with the observed value. For one concrete observation $`\tau = t`$:

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
  &= \frac{p_{\mathrm{match}}}{2-p_{\mathrm{match}}} = \frac{1}{511} \\
\mathbb{E}[\min(\tau, \tau')]
  &= \frac{1}{1-(1-p_{\mathrm{match}})^2} \approx 128.25
\end{aligned}
```

Thus an exact stopping-time observation would reject about 510 of 511 idealized wrong-password
trajectories by the stopping-time condition alone, while requiring approximately 128.25 complete
permutations on average to reach that decision. This does **not** mean that password entropy is
reduced by a fixed number of bits or that these idealized values carry over unchanged to MHFE.
It shows that variable runtime is part of the password-guessing model, not only a user-interface
problem. Timing-only, endpoint-only, endpoint-plus-stopping-time, leaked-intermediate-state, and
multiple known-pair cases require separate lower bounds on the unavoidable number of Argon2id
evaluations.

The resulting outer BIP39 mnemonic has the same 8-bit checksum value as the source mnemonic. Those
bits are exposed as a class label. They are not an independent copy of the checksum: every password
defines its own inverse permutation, and inverse cycle walking under a wrong password still returns
a candidate in the requested checksum class. The method therefore does **not** verify the password,
authenticate the recovered phrase, or contradict the information-capacity argument. It changes the
design into one permutation that preserves each of 256 checksum classes, equivalently 256
restricted class permutations; no independence between those restrictions is claimed. Separate
security and worst-case-runtime analysis is required.

This application of cycle walking to MHFE checksum classes is only a derived research proposal.
Black and Rogaway prove that cycle walking induces a uniform permutation on the target subset
when the underlying block cipher is ideal [35]. MHFE has not been proven to provide that ideal
permutation, and their theorem does not establish the security of this password-based,
state-dependent-KDF composition.

### Direction A and Direction B: geometry comparison

Two research directions are retained:

- **Direction A — balanced Feistel, main candidate.** Use $`128 \mid 128`$ bits for the
  256-bit container. The current candidate formulas describe this direction.
- **Direction B — source-heavy 1:3 Feistel, alternative candidate.** Update one quarter
  using the remaining three quarters, then rotate the state. $`32 \mid 96`$ bits describes
  a 128-bit state; a 256-bit container requires $`64 \mid 192`$ bits instead.

The following table preserves the earlier comparison of hypothetical original-length states.
It is not the geometry selected by the universal 256-bit packing candidate:

| Source words | Entropy state (bits) | Direction A split (bits) | Direction B split (bits) |
| -----------: | -------------------: | ------------------------ | ------------------------ |
|           12 |                  128 | 64 / 64                  | 32 / 96                  |
|           15 |                  160 | 80 / 80                  | 40 / 120                 |
|           18 |                  192 | 96 / 96                  | 48 / 144                 |
|           21 |                  224 | 112 / 112                | 56 / 168                 |
|           24 |                  256 | 128 / 128                | 64 / 192                 |

For a universal 256-bit outer payload, every source length instead uses $`128 \mid 128`$ bits
in Direction A or $`64 \mid 192`$ bits in Direction B. Input entropy and permutation state
size are different quantities. Packing a short source together with deterministic verifier
redundancy into a longer state does not create additional source entropy.

#### Evidence and trade-offs

Hoang and Rogaway analyze their unbalanced $`Feistel^r[m,n]`$ construction using independently
and uniformly random round functions [36]. Figure 4 explicitly compares proven CCA-security
bounds on a 128-bit string for $`Feistel^r[32,96]`$ (bold curves) and balanced
$`Feistel^r[64,64]`$ (dashed curves), at 18, 36, 72, and 144 rounds. Their Appendix E comparison,
particularly Figure 6 and its surrounding discussion, states that imbalance improves the bounds
when enough rounds are available, while the balanced construction has the stronger bound when
rounds are scarce. This is evidence about the paper's idealized construction and security game. It
does not prove the state-dependent MHFE KDF composition, justify transferring those round counts
to MHFE, or establish a secure four-round implementation.

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

Targeting each chunk once is not a security criterion. Comparisons must use equal measured
latency and peak memory, not merely the same number of rounds. Increasing the number of
sequential Argon2id calls increases work; it does not automatically multiply peak memory by
the same factor. Reducing each call's parameters to meet a time budget changes attack cost.

With the current 128-bit salt truncation, the following are upper bounds on the source
width retained as distinct salt values, not measured entropy or security levels:

| Total state (bits) | A: source width (bits) | B: source width (bits) | A: source/salt-width cap (bits) | B: source/salt-width cap (bits) |
| -----------------: | ---------------------: | ---------------------: | ------------------------------: | ------------------------------: |
|                128 |                     64 |                     96 |                              64 |                              96 |
|                192 |                     96 |                    144 |                              96 |                             128 |
|                256 |                    128 |                    192 |                             128 |                             128 |

Hash collisions, structured plaintext, and knowledge available to the attacker matter in
addition to these widths. A 128-bit salt cap is not automatically a 128-bit security bound
on the entire cipher: the effective round function also processes the state. Conversely,
a 192-bit branch is not a claim of 192-bit password security.

For an original-length 12-word experiment, the larger source branch makes Direction B
particularly interesting. For 18 words, its benefit must be assessed alongside the salt
truncation and the changed round function. For the universal 256-bit container, Direction A
already has a 128-bit source branch, so Direction B needs a concrete demonstrated advantage
to justify its additional complexity. These are research priorities, not security findings.

#### Known-pair filtering cost

Write one Direction B round on four equal chunks as:

```math
\begin{aligned}
(A, B, C, D) \to (B, C, D, A \oplus G_i(B \mathbin{\Vert} C \mathbin{\Vert} D))
\end{aligned}
```

Across three consecutive rounds, the initial `D` becomes the first output chunk without
modification. Given a known plaintext/ciphertext pair, an attacker can evaluate the rounds
outside a three-round gap and test that equality without evaluating the gap. In an adaptation
with one KDF evaluation per round, a four-round design therefore allows an initial filter
using only one KDF call. Equivalently, the first output chunk after four rounds is
$`A \oplus G_0(B \mathbin{\Vert} C \mathbin{\Vert} D)`$.

In an idealized random-function model the four-round filter has a false-acceptance rate of
$`2^{-w}`$, where `w` is the chunk width: 32, 48, or 64 bits for states of 128, 192, or 256 bits.
This distribution is not established for MHFE. Surviving guesses require further checks.
For balanced Feistel, a related known-pair filter can omit one round. These examples exhibit
shortcuts; neither is a proof of the optimal attack or a lower bound on required work.

Direction B therefore requires a separate round count, round-function definition, and
password-attack analysis. Larger KDF input alone is insufficient justification for choosing it.

## Reference Implementation

An initial experimental Rust implementation is maintained in the public
[`hobby-eng/mhfe`](https://github.com/hobby-eng/mhfe) repository. The implementation state
described here is pinned to revision
[`12b26a3348798654d9ea2fa08a715fef8e9e8334`](https://github.com/hobby-eng/mhfe/tree/12b26a3348798654d9ea2fa08a715fef8e9e8334).
It provides a reusable library core, a native Linux CLI, deterministic JSON-vector
generation, exact timing of the selected 512 MiB Argon2id suite, and an optional WASM API with a
dedicated Web Worker adapter. The ordinary browser API omits round keys and other vector-only
intermediate secrets. The wrapper has been exercised in Chromium, but this remains prototype
evidence rather than a browser-support claim. The Rust library, native CLI, WASM wrapper, and
Worker client expose automatic source-length detection. After one inverse permutation they return
a unique short-source match, fall back to an unverified 24-word interpretation when none matches,
and report every matching short length when detection is ambiguous. Explicit source length remains
available as an override; detailed vector-trace recovery requires it because the trace result is
profile-specific.

The operational Rust API and the explicitly test-only vector API use separate result types. The
operational result does not expose source entropy, packed plaintext, Argon2 outputs, round masks,
or round traces. Reachable Rust-owned password, mnemonic, entropy, round-material, result, and
Argon2 work buffers are zeroized on their relevant drop or reuse paths. This is a memory-hygiene
measure rather than a guarantee that compilers, allocators, browser strings, operating systems, or
earlier reallocations leave no residual copies. Allocation failure is returned as a typed error
when the initial Argon2 work-area reservation fails. The implementation also rejects an unchanged
encrypted state rather than returning a fixed point as a usable backup.

The CLI's direct string-input path intentionally accepts ASCII test passwords only. ASCII is
unchanged by Unicode 18 NFKD, while the available Rust normalization tables currently implement
Unicode 17. The library and browser API also accept UTF-8 bytes already normalized by a conforming
Unicode 18 NPSS-NFKD implementation, but do not claim to verify that precondition. Rejecting
non-ASCII text on the self-normalizing path avoids silently producing vectors that fail the
specification's pinned NPSS-NFKD-Unicode-18.0.0 rule.

The implementation is not finalized or independently reviewed by a cryptography specialist, and
it is not independent evidence for its own vectors. A separately written Python scratch verifier
derived only from this specification has reproduced all six published vectors and intermediate
values in both directions. That is a limited interoperability cross-check, not a maintained second
implementation or a security review. A toy reduced-width model must not be used as evidence of
production security.

### Initial performance measurement

The native release build of the initial Rust implementation produced the following local
measurements for experimental suite 2 at $`\mathrm{PIM} = 0`$:

| Item                                    | Observed value                                                                                                                               |
| --------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- |
| Computer                                | Samsung Galaxy Book2 Pro 360, model `NP950QED-KA2DE` (`950QED`)                                                                              |
| Processor                               | Intel Core i7-1260P, 12 physical cores / 16 hardware threads                                                                                 |
| System memory visible to Linux          | 15,448,300 kB (approximately 14.7 GiB)                                                                                                       |
| Operating system                        | Ubuntu Linux, x86-64, kernel `7.0.0-31-generic`                                                                                              |
| Rust implementation                     | `rustc 1.98.1`, release build, RustCrypto `argon2 0.5.3`                                                                                     |
| Suite parameters                        | $`N = 12`$, Argon2id $`m_{\mathrm{bits}} = 2^{32}`$ bits (512 MiB), $`t_{\mathrm{eff}} = 12`$, $`p = 4`$, $`\mathrm{PIM} = 0`$                         |
| Encryption                              | 59.666 seconds                                                                                                                               |
| Decryption                              | 60.019 seconds                                                                                                                               |
| Complete measured process               | 120.21 seconds                                                                                                                               |
| Maximum resident set size               | 526,972 KiB                                                                                                                                  |
| Rust release CPU utilization check      | 59.144 seconds encryption, 99% CPU; the RustCrypto lane loop executed effectively on one core                                                |
| Independent forward-round recalculation | 34.26 seconds through Python `cryptography 46.0.5`; all intermediate values matched, and a representative single Argon2id call used 298% CPU |

This is one local observation, not a normative performance target, minimum attacker cost, or
guarantee for similar product names. CPU power policy, thermal state, memory bandwidth, compiler,
Argon2 implementation, native versus WASM execution, and concurrent load can materially change the
result. The substantially faster independent recalculation on the same machine demonstrates that
the initial Rust wall-clock time must not be used as an attack-cost estimate. Direct process
measurements confirmed the main implementation difference: RustCrypto `argon2 0.5.3` consumed
approximately one CPU core while the OpenSSL-backed `cryptography` call used approximately three
cores on average for the four-lane computation. Broader measurements on representative x86-64 and ARM64 systems would be required before these
figures could support a portability or deployment claim.

The same native implementation measured the 12-word vector at $`\mathrm{PIM} = 1`$ ($`t_{\mathrm{eff}} = 24`$) in
111.171 seconds for encryption and 118.975 seconds for decryption, with 527,032 KiB maximum
resident memory and 99% process CPU utilization. A separate Python/Argon2id calculation reproduced
all twelve forward rounds, and attempting to recover that short-source container with $`\mathrm{PIM} = 0`$
produced a recovery-verifier mismatch. This single observation is likewise non-normative.

A complete Chromium 153 module-Worker/WASM $`\mathrm{PIM} = 0`$ round trip subsequently matched the published
12-word container and recovered the source phrase. It took 85.237 seconds to encrypt and 85.109
seconds to decrypt on the same computer; a later audit run measured 85.337 and 84.145 seconds.
Replaying all six published vectors in both directions took 682.91 seconds, although that is a
validation workload rather than a single-operation benchmark. Machine-readable local records are
kept under
[`measurements/`](https://github.com/hobby-eng/mhfe/tree/12b26a3348798654d9ea2fa08a715fef8e9e8334/measurements)
in the implementation repository. These observations check the browser and vector paths; they are
not support or performance guarantees.

## Test Vectors

Six positive experimental suite 2 vectors are included with this specification:

|                 Source length | Source entropy | Recovery-verifier length | Vector                       |
| ----------------------------: | -------------- | -----------------------: | ---------------------------- |
|                      12 words | 128 zero bits  |                 128 bits | `vectors/zero-12-pim-0.json` |
|                      15 words | 160 zero bits  |                  96 bits | `vectors/zero-15-pim-0.json` |
|                      18 words | 192 zero bits  |                  64 bits | `vectors/zero-18-pim-0.json` |
|                      21 words | 224 zero bits  |                  32 bits | `vectors/zero-21-pim-0.json` |
|                      24 words | 256 zero bits  |                     none | `vectors/zero-24-pim-0.json` |
| 12 words ($`\mathrm{PIM} = 1`$) | 128 zero bits  |                 128 bits | `vectors/zero-12-pim-1.json` |

Every vector uses the public ASCII password `public test password`; five use $`\mathrm{PIM} = 0`$ and the
additional 12-word vector uses $`\mathrm{PIM} = 1`$. Each records the
source mnemonic and entropy, `V_r`, packed state, encrypted entropy and mnemonic, every forward and
inverse round salt, Argon2id output, mask, state transition, and the recovered result. The 12-word
$`\mathrm{PIM} = 0`$ vector was reproduced twice byte-for-byte. A separately written Python scratch
verifier, derived from the specification rather than the Rust round code, reproduced all six
vectors in both directions. It matched every recorded salt, Argon2id output, mask, state,
container mnemonic, inverse round, recovered entropy, verifier result, and automatically detected
source length. This cross-check can detect implementation mistakes, but the scratch verifier is
not a maintained independent library or a security review.

The published Rust repository contains an
[ignored-by-default expensive test](https://github.com/hobby-eng/mhfe/blob/12b26a3348798654d9ea2fa08a715fef8e9e8334/tests/published_vectors.rs)
that replays all six published containers in both directions with the frozen suite parameters. A
[dedicated CI workflow](https://github.com/hobby-eng/mhfe/blob/12b26a3348798654d9ea2fa08a715fef8e9e8334/.github/workflows/vectors.yml)
runs that test when the implementation, parameters, or embedded expected vectors change and before
a release. This guards the implementation against suite drift; it is not independent evidence for
the vectors because the test and implementation share the same codebase.

The six files are released under CC0-1.0. They establish reproducible positive interoperability
cases for every supported source length; they do not establish security or complete negative and
boundary coverage. They MUST remain identified as vectors for
`MHFE-BIP39-256-EXPERIMENTAL-2`; an incompatible suite MUST publish a distinct vector set under its
new suite identifier. Expansion of the test-vector set SHOULD add at least:

- an additional non-zero-entropy source and corresponding encrypted entropy and mnemonic;
- Unicode passwords demonstrating NFKD normalization equivalence and non-equivalence cases;
- rejection of an empty normalized password, acceptance at 1024 normalized UTF-8 bytes, and
  rejection above that boundary;
- assigned and unassigned Unicode 18.0.0 cases for NPSS-NFKD processing;
- exact bit/byte serialization at every hash, Argon2id, HMAC, and truncation boundary;
- invalid input-mnemonic checksum rejection;
- invalid encrypted-mnemonic checksum rejection;
- wrong-password examples demonstrating short-source verifier rejection;
- a 24-word wrong-password example demonstrating that no protocol-level password error is
  available in that profile;
- source-length mismatch, accidental short-profile acceptance, and ambiguous auto-detection cases;
- suite-identifier and wordlist mismatch cases;
- omitted PIM and explicit $`\mathrm{PIM} = 0`$ equivalence, additional non-zero PIM/source-length cases,
  machine-readable wrong-PIM recovery cases, and rejection of $`\mathrm{PIM} = 32`$;
- bounded rejection of unknown or excessive resource parameters;
- equality handling in reduced models that can exercise fixed points or full-cycle returns;
- at least one maintained independent implementation reproducing the vectors before the
  construction is treated as mature.

The companion [vector notes](vectors/README.md) also record a small, non-Argon verifier fixture for
checking digest-byte order, most-significant-bit-first truncation, and the BIP39 checksum prefix.

Although MHFE is not a BIP proposal, this document follows BIP 3's useful recommendation that test
vectors be available under CC0-1.0 or FSFAP in addition to any other license so implementations can
copy them without license friction [7].

## Known Limitations

This section records the present boundaries of the experimental suite. It is not a roadmap and does
not commit the author to further research or implementation work.

- The construction has no formal security proof or reduction for its state-dependent Argon2id
  round functions.
- No independent cryptography-specialist review has been completed. Successful implementation,
  round trips, and matching vectors establish reproducibility, not cryptographic security.
- The selected Argon2id and Feistel parameters are supported by limited measurements on the
  documented development system; they are not proven optimal or portable performance guarantees.
- Short-source recovery verifiers intentionally provide an offline password-checking signal, while
  the 24-word source mode has no internal wrong-password test and automatic source-length detection
  remains probabilistic. The reference APIs implement automatic detection and retain explicit
  source length as an override.
- Password-guessing lower bounds, multi-container behavior, structured short-source domains, and
  state-derived-salt assumptions remain unresolved analytical questions.
- Checksum-class cycle walking and source-heavy unbalanced Feistel remain non-normative research
  alternatives. They are not part of experimental suite 2 or the reference implementation.

The implemented utility may be used for public experiments and interoperability testing under the
warnings in this document. Nothing in this section should be read as a promise of a future version
or as a claim that the current construction is suitable for protecting real funds.

## AI Assistance and Acknowledgments

The research direction, practical requirements, and publication decisions are attributed to
Sergei Semenov. This draft was developed through extended interaction with ChatGPT (OpenAI) and
Claude (Anthropic). These systems made substantial contributions to drafting, literature discovery,
mathematical calculations, counterargument generation, and adversarial security review.

This document has not received independent expert cryptographic review. The author understands
and endorses its research goals and high-level design, but does not represent that every
specialized cryptanalytic argument, numerical estimate, citation, or technical claim was
independently derived or reproduced without AI assistance.

## Copyright

Copyright © 2026 Sergei Semenov.

Except where otherwise noted, this specification and the original repository documentation are
licensed under the Creative Commons Attribution 4.0 International License (`CC-BY-4.0`). The full
legal text is included in the repository's `LICENSE` file and is available at:

https://creativecommons.org/licenses/by/4.0/

When sharing or adapting the licensed material, users must provide appropriate credit to Sergei
Semenov, link to the license, link to the canonical project source where reasonably practicable,
and indicate whether changes were made. Attribution must not imply endorsement by the author.
Third-party quotations, cited works, names, and trademarks remain subject to their respective
rights.

This document license does not automatically select a license for a reference implementation or
other software. Such code carries its own explicit software license. The published test vectors and
their vector README are released separately under CC0-1.0, as recorded in `vectors/`, so
implementations can reproduce and copy the test data without attribution friction. Future vectors
added to that set SHOULD use the same terms.

## References

1. Cryptosteel, "How to Use Cryptosteel Capsule." [Online]. Available:
   https://cryptosteel.com/how-to-use-capsule/. [Accessed: Sep. 18, 2026].
2. M. Palatinus, P. Rusnak, A. Voisine, and S. Bowe, "Mnemonic code for generating deterministic
   keys," BIP 39, Sep. 10, 2013. [Online]. Available:
   https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki. [Accessed: Sep. 18, 2026].
3. Tarion, "How to encrypt an existing BIP-39 mnemonic with a password without changing the
   seed?" _Bitcoin Stack Exchange_, May 5, 2021. [Online]. Available:
   https://bitcoin.stackexchange.com/questions/106036/. [Accessed: Sep. 19, 2026].
4. T. Kaupat, _go-bip39_, GitHub repository, rev. `3ab2b81a7576aedbe1e1a347cab359e383dbf248`,
   Dec. 17, 2024. [Online]. Available:
   https://github.com/Niondir/go-bip39/blob/3ab2b81a7576aedbe1e1a347cab359e383dbf248/encryption.go.
   Relevant earlier revisions: `6615be49f50a990856ec5a65e7b3d9e985644946`, May 5, 2021, and
   `2a307b8f25e0454ebbe9bbae0fcb7659fafcbba2`, May 10, 2021. [Accessed: Sep. 19, 2026].
5. S. Bradner, "Key words for use in RFCs to Indicate Requirement Levels," RFC 2119, BCP 14,
   RFC Editor, Mar. 1997, doi: 10.17487/RFC2119.
6. B. Leiba, "Ambiguity of Uppercase vs Lowercase in RFC 2119 Key Words," RFC 8174, BCP 14,
   RFC Editor, May 2017, doi: 10.17487/RFC8174.
7. Murch, "Updated BIP Process," BIP 3, ver. 1.4.0, Jan. 9, 2025. [Online]. Available:
   https://github.com/bitcoin/bips/blob/master/bip-0003.md. [Accessed: Sep. 20, 2026].
8. E. Lombrozo, "BIP Classification," BIP 123, Aug. 26, 2015. [Online]. Available:
   https://github.com/bitcoin/bips/blob/master/bip-0123.mediawiki. [Accessed: Sep. 20, 2026].
9. National Institute of Standards and Technology, _Secure Hash Standard (SHS)_, FIPS PUB 180-4,
   Aug. 2015, doi: 10.6028/NIST.FIPS.180-4.
10. K. Whistler, Ed., "Unicode Normalization Forms," Unicode Standard Annex #15, rev. 58,
    Unicode 18.0.0, Aug. 12, 2026. [Online]. Available:
    https://www.unicode.org/reports/tr15/tr15-58.html. [Accessed: Sep. 22, 2026].
11. M.-J. Saarinen and J.-P. Aumasson, "The BLAKE2 Cryptographic Hash and Message Authentication
    Code (MAC)," RFC 7693, RFC Editor, Nov. 2015, doi: 10.17487/RFC7693.
12. H. Krawczyk, M. Bellare, and R. Canetti, "HMAC: Keyed-Hashing for Message Authentication,"
    RFC 2104, RFC Editor, Feb. 1997, doi: 10.17487/RFC2104.
13. A. Biryukov, D. Dinu, D. Khovratovich, and S. Josefsson, "Argon2 Memory-Hard Function for
    Password Hashing and Proof-of-Work Applications," RFC 9106, RFC Editor, Sep. 2021,
    doi: 10.17487/RFC9106.
14. J. Patarin, "Luby-Rackoff: 7 Rounds Are Enough for 2^{n(1-epsilon)} Security," in
    _Advances in Cryptology--CRYPTO 2003_, LNCS 2729. Berlin, Germany: Springer, 2003,
    pp. 513-529, doi: 10.1007/978-3-540-45146-4_30.
15. J. Patarin, "Security of Random Feistel Schemes with 5 or More Rounds," in
    _Advances in Cryptology--CRYPTO 2004_, LNCS 3152. Berlin, Germany: Springer, 2004,
    pp. 106-122, doi: 10.1007/978-3-540-28628-8_7.
16. A. Juels and T. Ristenpart, "Honey Encryption: Security Beyond the Brute-Force Bound," in
    _Advances in Cryptology--EUROCRYPT 2014_, LNCS 8441. Berlin, Germany: Springer, 2014,
    pp. 293-310, doi: 10.1007/978-3-642-55220-5_17.
17. J. Patarin, "Generic Attacks on Feistel Schemes," in _Advances in Cryptology--ASIACRYPT
    2001_, LNCS 2248. Berlin, Germany: Springer, 2001, pp. 222-238,
    doi: 10.1007/3-540-45682-1_14. Extended version: Cryptology ePrint Archive, Paper 2008/036.
18. J. Patarin, "Security of balanced and unbalanced Feistel Schemes with Linear Non
    Equalities," Cryptology ePrint Archive, Paper 2010/293, May 18, 2010. [Online]. Available:
    https://eprint.iacr.org/2010/293. [Accessed: Sep. 21, 2026].
19. A. Biryukov, D. Dinu, and D. Khovratovich, "Argon2: New Generation of Memory-Hard Functions
    for Password Hashing and Other Applications," in _2016 IEEE European Symposium on Security
    and Privacy_. Piscataway, NJ, USA: IEEE, 2016, pp. 292-302,
    doi: 10.1109/EuroSP.2016.31.
20. P. Rusnak, A. Kozlik, O. Vejpustek, T. Susanka, M. Palatinus, and J. Hoenicke, "Shamir's
    Secret-Sharing for Mnemonic Codes," SLIP-0039, Dec. 18, 2017. [Online]. Available:
    https://github.com/satoshilabs/slips/blob/master/slip-0039.md. [Accessed: Sep. 21, 2026].
21. M. Caldwell and A. Voisine, "Passphrase-protected private key," BIP 38, Nov. 20, 2012.
    [Online]. Available: https://github.com/bitcoin/bips/blob/master/bip-0038.mediawiki.
    [Accessed: Sep. 21, 2026].
22. National Institute of Standards and Technology, _Advanced Encryption Standard (AES)_,
    FIPS PUB 197, updated May 9, 2023, doi: 10.6028/NIST.FIPS.197-upd1.
23. M. Dworkin, _Recommendation for Block Cipher Modes of Operation: Methods and Techniques_,
    NIST SP 800-38A, Dec. 2001, Appendix B, doi: 10.6028/NIST.SP.800-38A.
24. mifunetoshiro, _Seedshift_, GitHub repository,
    rev. `853423930e29b388ff936f581d9b692944319d46`, Jul. 26, 2025. [Online]. Available:
    https://github.com/mifunetoshiro/Seedshift/tree/853423930e29b388ff936f581d9b692944319d46.
    [Accessed: Sep. 18, 2026].
25. mifunetoshiro, _bip39_obfuscator_, GitHub repository,
    rev. `0d82f4809fe4bec0e53d4487a3dd9e34142af04b`, Oct. 25, 2021. [Online]. Available:
    https://github.com/mifunetoshiro/bip39_obfuscator/tree/0d82f4809fe4bec0e53d4487a3dd9e34142af04b.
    [Accessed: Sep. 19, 2026].
26. EnteroPositivo, _BIP39Colors_, GitHub repository,
    rev. `df3bc100416d8acc48d7cad02050e5eb3ac177ae`, Jul. 15, 2023. [Online]. Available:
    https://github.com/EnteroPositivo/bip39colors/tree/df3bc100416d8acc48d7cad02050e5eb3ac177ae.
    [Accessed: Sep. 22, 2026].
27. JonDerThan, _MnemonicCrypt_, GitHub repository,
    rev. `d3c9315b483805689fd978b7dc783b0e86676473`, Oct. 31, 2025. [Online]. Available:
    https://github.com/JonDerThan/mnemonic-crypt/tree/d3c9315b483805689fd978b7dc783b0e86676473.
    [Accessed: Sep. 20, 2026].
28. kklash, _Mnemonikey_, GitHub repository,
    rev. `0bd15d84d23ffd7e439eb3217c4215dd8df8894f`, Jan. 29, 2024. [Online]. Available:
    https://github.com/kklash/mnemonikey/tree/0bd15d84d23ffd7e439eb3217c4215dd8df8894f.
    [Accessed: Sep. 21, 2026].
29. C. J. DeLisle, _pktseed_, GitHub repository,
    rev. `1ec6b87f6603579bac8b63f38d73710ee8e36425`, Aug. 28, 2021. [Online]. Available:
    https://github.com/cjdelisle/pktseed/tree/1ec6b87f6603579bac8b63f38d73710ee8e36425.
    [Accessed: Sep. 22, 2026].
30. B. Matthews, _seed-otp_, GitHub repository,
    rev. `70b51e05daf054355bd7691188ff7720afc7ca3c`, Apr. 30, 2021. [Online]. Available:
    https://github.com/brndnmtthws/seed-otp/tree/70b51e05daf054355bd7691188ff7720afc7ca3c.
    [Accessed: Sep. 18, 2026].
31. M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom
    Functions," _SIAM Journal on Computing_, vol. 17, no. 2, pp. 373-386, Apr. 1988,
    doi: 10.1137/0217022.
32. M. Dworkin, _Recommendation for Block Cipher Modes of Operation: Methods for
    Format-Preserving Encryption_, NIST SP 800-38G, updated Aug. 4, 2016,
    doi: 10.6028/NIST.SP.800-38G. The second public draft of Revision 1 was published
    Feb. 3, 2025; it is not a final publication.
33. B. Morris, H. Oberschelp, and H. S. Santhakumar, "Format Preserving Encryption in the
    Bounded Retrieval Model," arXiv:2307.08158, Jul. 16, 2023,
    doi: 10.48550/arXiv.2307.08158.
34. B. Morris, P. Rogaway, and T. Stegers, "How to Encipher Messages on a Small Domain," in
    _Advances in Cryptology--CRYPTO 2009_, LNCS 5677. Berlin, Germany: Springer, 2009,
    pp. 286-302, doi: 10.1007/978-3-642-03356-8_17.
35. J. Black and P. Rogaway, "Ciphers with Arbitrary Finite Domains," in _Topics in Cryptology--
    CT-RSA 2002_, LNCS 2271. Berlin, Germany: Springer, 2002, pp. 114-130,
    doi: 10.1007/3-540-45760-7_9.
36. V. T. Hoang and P. Rogaway, "On Generalized Feistel Networks," in
    _Advances in Cryptology--CRYPTO 2010_, LNCS 6223. Berlin, Germany: Springer, 2010,
    pp. 613-630, doi: 10.1007/978-3-642-14623-7_33.
