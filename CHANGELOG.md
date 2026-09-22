# Changelog

Version history for **MHFE: Memory-Hard Feistel Encryption for BIP39 Mnemonics**. The normative experimental-suite definition remains in [`README.md`](README.md).

- **0.3.0 (2026-09-22):**
  - published the companion Rust implementation repository, linked its exact reviewed revision,
    measurements, vector replay test, and CI workflow, and included separate audit records for the
    specification and implementation;
  - named the project **MHFE: Memory-Hard Feistel Encryption for BIP39 Mnemonics**, retaining
    `MHFE` and the existing experimental suite identifier;
  - moved the practical motivation directly after the abstract, placed the use case before
    historical context, and relocated AI-assistance disclosure near the end of the document;
  - replaced the earlier separate custom-check proposal with one universal packing rule,
    `E || Trunc_(256-ENT)(SHA256(E))`, for 12-, 15-, 18-, and 21-word sources;
  - documented how the ordinary source BIP39 checksum is already the prefix of the recovery
    verifier, leaving 124, 91, 58, or 25 additional verifier bits respectively;
  - distinguished the encrypted recovery verifier from AEAD authentication and the outer BIP39
    transcription checksum, and documented its offline password-testing trade-off;
  - selected one 256-bit state and balanced `128 | 128` core for all source lengths while retaining
    24-word sources as the no-verifier full-domain case;
  - specified automatic short-source length detection, an explicit 24-word override, exact
    ambiguity with the full 24-word domain, and selected-profile false-acceptance rates;
  - added explicit decoder checks and accidental-classification probabilities for every short
    source length, plus the first-round salt collision-diversity hypothesis;
  - recorded and set aside public reversible pre-mixing after finding no demonstrated practical
    benefit for uniform 24-word sources and no protection against constructed branch collisions;
  - expanded related work with Honey Encryption, the 2021 BIP39 backup-encryption discussion,
    `Seedshift`, `bip39_obfuscator`, `MnemonicCrypt`, `Mnemonikey`, `pktseed`, `seed-otp`, and
    bounded-retrieval format-preserving encryption;
  - documented the Niondir prototype's fixed AES-CTR keystream reuse and scoped the resulting
    cross-record XOR exposure to known- or chosen-plaintext recovery;
  - recorded the limits of the non-exhaustive public-code search rather than asserting novelty;
  - separated the marginal collision diversity of `R_0` from its exact conditional source entropy
    given `L_0`, including the 0-, 32-, 64-, 96-, and 128-bit spectrum;
  - distinguished the short-profile benefit of early whole-source KDF sensitivity from the
    unavoidable structured-domain question, without treating either as a security proof;
  - included a bounded PIM work factor with default `0`, fixed `t_eff = 12 * (PIM + 1)`, explicit
    domain binding, and no reduction below the standard cost;
  - added an initial reusable Rust core and Linux CLI, a WASM compile check, deterministic CC0 test
    vector generation, exact local timing, and an independently recalculated twelve-round vector;
  - separated operational and test-vector APIs, added best-effort secret-buffer zeroization,
    typed initial-allocation failure, fixed-point refusal, reduced-parameter behavioral tests, and
    an expensive CI replay of every published round transcript in both directions;
  - documented checksum-preserving cycle walking as a reversible 24-word alternative that does
    not provide password verification, including its prohibitive conditional runtime, long-tail
    latency, lack of a useful small worst-case bound, and variable-time surface;
  - separated adjacent-pair Feistel shortcuts from the hidden-intermediate-state cycle-walking
    problem and quantified the idealized stopping-time filter exposed by exact runtime;
  - clarified the expected fixed-point behavior of an idealized random permutation, its negligible
    per-state probability, and the required handling of an unchanged encrypted state;
  - assigned an exact external suite identifier and separate salt and mask domain strings, and
    required every incompatible algorithm-suite revision to change all three;
  - identified the human author and disclosed the substantial drafting, research, calculation,
    and adversarial-review assistance provided by ChatGPT and Claude;
  - added the practical motivation for capacity-limited physical backups, separate password
    preservation, protection against accidental viewing or photography, and the container's
    practical format ambiguity without claiming formal plausible deniability;
  - scoped execution to trusted high-memory general-purpose computers, excluded hardware-wallet
    firmware and constrained devices as initial targets, and prohibited silent parameter downgrade;
  - organized the document as an independent research specification with BIP-inspired
    Motivation, Backward Compatibility, Reference Implementation, Test Vectors, Copyright,
    and requirements-language sections;
  - retained the balanced 256-bit construction as the baseline and explicitly compared
    source-heavy unbalanced Feistel as an alternative research direction;
  - incorporated universal short-source packing into the principal candidate while keeping
    auto-detection probabilistic and explicitly non-authoritative;
  - added equal-state geometry tables, salt-width limits, cost comparisons, and known-pair
    filtering caveats for both research directions;
  - standardized stated sizes in bits and documented conversion at the Argon2 API boundary;
  - made the effective-round definition use the same 128-bit truncated salt as encryption
    and decryption, and clarified hash, encoding, and KDF parameter conventions;
  - removed unsupported claims that per-container amortization is impossible or every
    state-derived salt is unique;
  - distinguished transcription checks, recovery verification, and authentication;
  - corrected Argon2id side-channel wording;
  - fixed experimental-suite parameters of twelve Feistel rounds and Argon2id with 512 MiB, four
    lanes, and a default of twelve passes, while retaining explicit Patarin/RFC transfer limitations;
  - licensed the specification and original repository documentation under `CC-BY-4.0` with
    attribution, source-linking, and change-indication requirements;
  - recorded RFC 9106's four-lane baseline, rejected an unexplained `p = 1` choice, and separated
    the Argon2 lane symbol from the cycle-walking checksum-match probability;
  - fixed NPSS-NFKD Unicode 18.0.0 password encoding, a 1-to-1024-byte normalized-password
    range, HMAC-SHA-256 round masks, and exact domain-separation strings for experimental suite 2;
  - removed Fast/Balanced/Hardened profiles and prohibited parameter overrides under the fixed
    experimental suite;
  - added SLIP-0039 as direct prior art for Feistel rounds with `R` in the KDF salt;
  - qualified collision, wrong-password, fixed-point, and per-guess KDF-cost statements;
  - cleaned notation and formulas into renderer-stable text blocks and removed hidden Unicode;
  - verified reference metadata against primary records, split combined sources into individual
    entries, standardized the bibliography in an IEEE-like numeric style, and renumbered citations
    by first appearance.
- **0.2.0 (2026-09-21):**
  - added BIP39 application-profile and capacity analysis;
  - introduced the conservative 256-bit reference-container direction;
  - separated the algorithm, rationale, alternatives, and security considerations;
  - separated single-container password guessing from multi-query Feistel analysis;
  - clarified input-dependent subkeys versus deterministic effective round functions;
  - added Patarin beyond-birthday discussion and the Argon2 salt-separation hypothesis A1;
  - refined known-pair provenance and the T1-T5 threat models.
- **0.1.0 (2026-09-19):** initial draft release.
