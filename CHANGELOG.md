# Changelog

Version history for **MHFE: Memory-Hard Feistel Encryption for BIP39 Mnemonics**. The specification
is [`README.md`](README.md).

- **Unreleased:**
  - Renumbered the shared references by first citation in the specification, then in the supplement;
    updated both documents and reordered the bibliography without changing sources.
  - Recorded the Zenodo DOI of release v0.4.0,
    [10.5281/zenodo.23074882](https://doi.org/10.5281/zenodo.23074882), in `CITATION.cff` and the
    specification's banner.
  - Moved the archived suite 2 vectors and their checksum manifest from `vectors/` to
    [`vectors/archive/suite-2/`](vectors/archive/suite-2/), next to the current corpus in
    `vectors/suite3/`. Their bytes are unchanged; release v0.4.0 and its archive keep the earlier
    paths.
  - Checked every cited source against its original and corrected the places where the text said
    more than its source: the capacity of a Cryptosteel capsule, EFF's own six-word advice, the
    alternatives to a balanced Feistel network as sufficient bounds rather than minimums, the
    narrower relation to classical deniable encryption, and the full version of the Hoang-Rogaway
    paper whose figure numbers the supplement uses. Three smaller wording fixes in the supplement.
- **0.4.0 (2026-10-01):**
  - **Audit records and vectors:** imported the historical
    [AUD-002](docs/audits/audit-02-2026-09-29.md) report, retained the existing
    [AUD-003](docs/audits/audit-03-2026-09-30.md), and added
    [AUD-004](docs/audits/audit-04-2026-09-30.md) with its five verified documentation fixes,
    followed by [AUD-005](docs/audits/audit-05-2026-09-30.md) with both verified text corrections:
    qualified the password-input explanation and the manual source-length recovery case. The
    [audit index](docs/audits/README.md) records scope and provenance; audit evidence stays local,
    and each audit's harness scripts are published in `docs/audits/AUD-NNN-harnesses/` with a
    README. Refreshed the current [suite 3 corpus](vectors/suite3/) with full-cost independent
    replay and fast input-validation coverage; preserved the archived suite 2 vectors at their
    existing paths. Clarified recovery-result labels, original-length context, password entry,
    benchmark assumptions and historical mathematical claims without changing the cryptographic
    format.
  - **Document structure and status:** kept `README.md` as the specification, with all nine detailed
    Rationale answers and plain notation; moved the extended technical analysis to the non-normative
    [supplement](docs/DESIGN-NOTES.md), sharing one reference list and consolidating repeated
    caveats. Retired `SPECIFICATION-PLAIN.md`. Adopted the BIP 3 preamble (`BIP: ?`, Layer
    Applications, Status Draft, Type Specification, `Requires: 39`) and added the Changelog section.
    Updated `CITATION.cff` to version 0.4.0.
  - **Suite and parameters:** defined `MHFE-BIP39-256-EXPERIMENTAL-3` with 2 GiB of Argon2id memory
    instead of 512 MiB, four lanes and twelve passes by default. The 2 GiB/four-lane baseline
    follows RFC 9106; twelve passes are the project's choice for cold storage. Extended PIM to
    `0..1023` and added memory levels `0..21` (2 GiB to 3 TiB, doubling every two levels in whole
    GiB), binding both settings into salt and mask messages. Explained the limits, why additional
    default time goes into passes and why the time budget does not determine the Feistel round
    count.
  - **Password encoding:** pinned normalization to Unicode 17.0.0 and explained the change from
    suite 2's Unicode 18.0.0. Specified stabilized normalization in terms of
    `General_Category=Unassigned`, rejecting noncharacters while accepting Private Use characters.
    Forbade control characters (including NUL, TAB, LF and CR) and the line and paragraph separators
    U+2028 and U+2029 in passwords to avoid common line-ending and input-control problems. Clarified
    that other accepted Unicode characters can still be invisible or require suitable input and
    display support. Explained the choice of NFKD, why BIP39 support alone is not enough, and why
    sources and containers use only the English wordlist: BIP39 itself strongly discourages other
    wordlists, and it derives the seed from the words, so re-encoding a phrase with another wordlist
    changes the wallet.
  - **Motivation and password choices:** stated cold storage as the intended use, with protection of
    the mnemonic before its BIP39 passphrase, no movement of funds, decoy wallets and the option to
    remember a password instead of the original phrase. Explained that a photographed container
    enables offline guessing without revealing the phrase directly. Recommended four or more
    independently chosen dice words; distinguished the short-source verifier from the 24-word case,
    where independent secrets require a pair search only without a separate mnemonic check. Kept the
    illustrative cost comparison in Motivation and the full attack-time tables, including farms and
    botnets, in the supplement.
  - **Creation, recovery and input:** required password confirmation at creation and a reverse check
    that decodes the new container's words and compares the recovered state with the source. Allowed
    display during verification only with a clear unverified status and outcome; noted that a bug
    shared by both directions can survive the check. Asked for the rehearsal to read the container
    from the finished backup, because a random one-word copying error passes the checksum in about
    one case in 256, and for applications to say that letter case and the characters between words
    of a password are significant after NFKD, with the reason why words are read forgivingly and
    passwords are not. Recommended case-insensitive word entry, acceptance of extra whitespace and
    unique prefixes of at least four letters, with exact matches resolved first. Asked applications
    to warn before encryption if the packed state passes another short-source verifier, so the owner
    can record and select the original length. Added guidance for local password-variant assistance
    and a rehearsal check that hides the mnemonic and uses its known length; distinguished that
    check from confirmation of a particular wallet.
  - **Recovery context and resources:** required applications to show the suite identifier and to
    tell the user to remember any non-default setting; with the defaults, nothing besides the
    container and the password needs to be kept; settings may be kept secret. Asked applications to
    check available memory before accepting a level, state supported levels, account for recovery on
    other hardware and support cancellation during long rounds. Required parallel Argon2id lanes
    where threads are available. Attributed the 2 GiB browser limit to the reference C code with
    32-bit pointers, not WebAssembly. Distinguished recovery time from creation time, which includes
    a full recovery check.
  - **Security requirements and rationale:** strongly recommended offline use and prohibited network
    transmission of secrets or derived values, as well as logging, exporting or persistently storing
    intermediate values, including Argon2id working memory, error reports and files kept to resume
    an interrupted operation. Explained which endpoint salts are public, the known `11 - i`-call
    filter from a leaked intermediate salt, without claiming a lower bound, and why constant salts
    permit shared dictionaries. Explained the Feistel choice, BLAKE2b salt hashing and HMAC-SHA-256
    masks, including why BLAKE2b-256 is not truncated BLAKE2b-512. Recommended a distinct password
    for each encrypted phrase that is used nowhere else, with further copies made as exact copies of
    the same container, described plate substitution and future weakening of Argon2id, and stated
    precisely what determinism and identical containers imply. Narrowed claims about alternative
    structures and corrected citations, RFC 9106's status and the comparison with scrypt. Explained
    why Argon2id's secret and associated data are empty, and that the container's own wallet can
    serve as a decoy only against someone who does not know that MHFE was used.
  - **Security analysis and estimates:** added random-oracle arguments for ciphertext-only guessing
    and the known-pair one-round discount, defining password tests separately for short and 24-word
    sources. Withdrew the bound that counted only Argon2id calls and left optimality open. Qualified
    salt uniqueness and combined-password costs, including false short-verifier matches. Recomputed
    attack estimates from one model, distinguished logical memory accesses from DRAM traffic and
    limited memory-cost claims to their bandwidth or capacity assumptions and treatment of
    memory-time trade-offs. Kept secret-PIM guidance qualitative in the specification, with the
    conditional calculation in the supplement; retained `(k + 2) / 2` specifically for an owner
    searching a forgotten PIM. Consolidated overlapping attack tables and listed open questions.
    Added threat models for old containers after a password or settings change, a partly known or
    weak source, leaked intermediate values, a dishonest implementation, a future attacker, an
    observer on the same computer, a password known from elsewhere, faults during computation and
    many owners at once, and a table of what each recovery check confirms. Analysed what each leaked
    intermediate value saves an attacker, attacks on the containers of many owners, faults,
    observers on the same computer, determinism as a check on implementations, cheaper guessing in
    the future and losing access, including a damaged plate, heirs and quantum search. Explained how
    the state-derived salts relate to NIST SP 800-132 and to the salt recommendation of RFC 9106,
    without claiming conformance. Added a deniability analysis: two experiments comparing an honest
    disclosure with a prepared decoy password, with an exact equality of the disclosures for 24-word
    sources, before the refusal of fixed points and the redrawing of the decoy password, which are
    bounded separately, and, in the random-oracle model, a bound of about the probability of
    guessing the real password for every source length, the latter for shorter sources only when the
    adversary does not know the length. Explained that naming the same decoy password again and
    answering checks computed from the disclosed phrase add no information, that containers of one
    phrase under different passwords or settings expose a decoy, so copies have to be identical,
    which outside records can expose it, and that deniability removes evidence without deterring an
    adversary from continuing.
  - **Historical material and research:** defined suite 2 by archived release v0.3.0, with an
    informative appendix and unchanged suite 2 vectors. Brought the supplement's Part II up to date
    for suite 3, replaced its repetitions of the specification with references, wrote its formulas
    in the plain notation of the specification instead of LaTeX, and kept the released v0.3.0 text
    in [`docs/archive/`](docs/archive/README.md), marked as historical. Recorded the
    final-word-preserving profile `MHFE-BIP39-256-EXPERIMENTAL-2-CYCLE-WALK-FINAL-WORD`, drafted and
    implemented after 0.3.0 but never released. Left cycle walking out of suite 3 while preserving
    its purpose, prohibitive expected cost, variable walk lengths, about 11 bits of information
    revealed, the limitations of the cheaper variants considered and the rejected 253-bit variant as
    research material.
  - **Implementation and verification:** documented the move to suite 3 only in implementation
    version 0.4.0, using the reference C Argon2 engine for native and Emscripten browser builds. The
    source implementation revision for the refreshed public corpus is
    [`46112d2b4bec0b9eba34cbbb9d632df099e11672`](https://github.com/hobby-eng/mhfe/commit/46112d2b4bec0b9eba34cbbb9d632df099e11672).
    The [current corpus](vectors/suite3/) includes 17 positive round transcripts and six negative
    recovery cases, all reproduced at full cost with the independent OpenSSL 3.5.5 Argon2 engine;
    every positive transcript was reproduced in both directions. Added 54 fast cases covering
    password, JavaScript boundary, settings, phrase and source-length validation and verifier
    serialization. Source, generator and verifier provenance and verification limits are recorded
    with the corpus. Retained the requirement for an independent Argon2 API supporting all
    parameters, including four lanes. Added a check runner that returns failure when a check fails,
    preserving the original audit harnesses and their recorded hashes. Reordered pre-computation
    guidance and vector requirements and removed redundant navigation and numerical examples.
- **0.3.0 (2026-09-22):**
  - published the companion Rust implementation repository, linked its exact reviewed revision,
    measurements, vector replay test, and CI workflow, and included separate audit records for the
    specification and implementation;
  - named the project **MHFE: Memory-Hard Feistel Encryption for BIP39 Mnemonics**, retaining `MHFE`
    and the existing experimental suite identifier;
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
  - specified automatic short-source length detection, an explicit 24-word override, exact ambiguity
    with the full 24-word domain, and selected-profile false-acceptance rates;
  - added explicit decoder checks and accidental-classification probabilities for every short source
    length, plus the first-round salt collision-diversity hypothesis;
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
  - separated operational and test-vector APIs, added best-effort secret-buffer zeroization, typed
    initial-allocation failure, fixed-point refusal, reduced-parameter behavioral tests, and an
    expensive CI replay of every published round transcript in both directions;
  - documented checksum-preserving cycle walking as a reversible 24-word alternative that does not
    provide password verification, including its prohibitive conditional runtime, long-tail latency,
    lack of a useful small worst-case bound, and variable-time surface;
  - separated adjacent-pair Feistel shortcuts from the hidden-intermediate-state cycle-walking
    problem and quantified the idealized stopping-time filter exposed by exact runtime;
  - clarified the expected fixed-point behavior of an idealized random permutation, its negligible
    per-state probability, and the required handling of an unchanged encrypted state;
  - assigned an exact external suite identifier and separate salt and mask domain strings, and
    required every incompatible algorithm-suite revision to change all three;
  - identified the human author and disclosed the substantial drafting, research, calculation, and
    adversarial-review assistance provided by ChatGPT and Claude;
  - added the practical motivation for capacity-limited physical backups, separate password
    preservation, protection against accidental viewing or photography, and the container's
    practical format ambiguity without claiming formal plausible deniability;
  - scoped execution to trusted high-memory general-purpose computers, excluded hardware-wallet
    firmware and constrained devices as initial targets, and prohibited silent parameter downgrade;
  - organized the document as an independent research specification with BIP-inspired Motivation,
    Backward Compatibility, Reference Implementation, Test Vectors, Copyright, and
    requirements-language sections;
  - retained the balanced 256-bit construction as the baseline and explicitly compared source-heavy
    unbalanced Feistel as an alternative research direction;
  - incorporated universal short-source packing into the principal candidate while keeping
    auto-detection probabilistic and explicitly non-authoritative;
  - added equal-state geometry tables, salt-width limits, cost comparisons, and known-pair filtering
    caveats for both research directions;
  - standardized stated sizes in bits and documented conversion at the Argon2 API boundary;
  - made the effective-round definition use the same 128-bit truncated salt as encryption and
    decryption, and clarified hash, encoding, and KDF parameter conventions;
  - removed unsupported claims that per-container amortization is impossible or every state-derived
    salt is unique;
  - distinguished transcription checks, recovery verification, and authentication;
  - corrected Argon2id side-channel wording;
  - fixed experimental-suite parameters of twelve Feistel rounds and Argon2id with 512 MiB, four
    lanes, and a default of twelve passes, while retaining explicit Patarin/RFC transfer
    limitations;
  - licensed the specification and original repository documentation under `CC-BY-4.0` with
    attribution, source-linking, and change-indication requirements;
  - recorded RFC 9106's four-lane baseline, rejected an unexplained `p = 1` choice, and separated
    the Argon2 lane symbol from the cycle-walking checksum-match probability;
  - fixed NPSS-NFKD Unicode 18.0.0 password encoding, a 1-to-1024-byte normalized-password range,
    HMAC-SHA-256 round masks, and exact domain-separation strings for experimental suite 2;
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
