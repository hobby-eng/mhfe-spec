"""The AUD-006 finding and observation records, the single source for the Markdown and JSON reports."""

BASE = "2cd5e4c96a2bf2cc177f8b99b81fa7427bdf1b86"


def rec(id, category, severity, title, affected, observed, expected, impact, fix, verification,
        status="verified", blocking=False, blocking_reason=None, kind="finding", reproduction=None):
    return {
        "id": id,
        "category": category,
        "kind": kind,
        "title": title,
        "severity": severity,
        "status": status,
        "releaseBlocking": blocking,
        "releaseBlockingReason": blocking_reason
        or "A bounded wording or consistency defect; no suite algorithm, packing or vector is affected.",
        "affected": affected,
        "evidence": [f"Baseline text at {BASE} plus the uncommitted tree; reviewer notes are local only."],
        "reproduction": reproduction or "Read the affected passages of the baseline tree side by side.",
        "expected": expected,
        "observed": observed,
        "impact": impact,
        "recommendedFix": fix,
        "requiredVerification": verification,
    }


FINDINGS = [
    rec(
        "AUD-006-FUN001", "FUN", "high",
        "The published suite 3 corpus has no machine-readable record for the current stated-24-words outcome",
        ["vectors/suite3/negative-cases.json", "vectors/suite3/README.md", "README.md (Test Vectors)"],
        "The `selected-24-words` record keeps only the 24-word reading requested under the historical rules; "
        "the current two-reading result exists only as a prose table in the corpus notes.",
        "Each conformance case states its expected readings, word counts, order and labels in the corpus "
        "itself, as the Test Vectors section requires.",
        "A conforming implementation cannot be checked mechanically against the current length rules.",
        "Import the reference implementation's `stated-24-words` record with its manifest and independent "
        "verification record from a pinned commit, update the counts and provenance, and shorten the prose "
        "table to a pointer.",
        "SHA256SUMS of the imported corpus, the record hash, the case counts in all notes, and a replay of "
        "the new case.",
        status="fixed", blocking=True,
        blocking_reason="The specification's own conformance requirement was not met by the corpus it ships; "
        "fixed by importing the record from implementation revision 3a705db6945b35f8c248c44893e71ddc36902af4.",
    ),
    rec(
        "AUD-006-FUN002", "FUN", "medium",
        "Two length rules applied to one input with different results",
        ["README.md (Recovering a mnemonic, step 3 and the list after it)"],
        "With 24 words stated and exactly one short match, 'one other length matches: use the detected length' "
        "withheld the 24-word reading, while '24 words stated, but a short length matches' offered it.",
        "Every combination of stated length and match count falls under exactly one rule.",
        "Implementations could disagree on the one case that creation step 2 exists for.",
        "Write the rules as two lists, with and without a stated length, and narrow the conflicting rule to a "
        "stated short length.",
        "Trace every combination of stated length (none, short, 24) and match count (0, 1, 2 or more).",
    ),
    rec(
        "AUD-006-FUN003", "FUN", "medium",
        "The private-screen confirmation could not satisfy the replacement rule",
        ["README.md (Application requirements: Re-encryption)"],
        "Showing the phrase was a MAY after a MUST it did not name as an alternative, and a replacement "
        "without a source verifier then needed an independent reference the owner did not have.",
        "Each confirmation path the specification allows leads to a replacement that can be rehearsed.",
        "Applications following the text strictly could refuse the re-encryption the owner's path was meant "
        "to allow.",
        "State the two confirmation paths as alternatives; require the rehearsal reference before the "
        "replacement is created; allow it to be derived from the phrase after the owner's explicit "
        "confirmation, for the replacement rehearsal only.",
        "Trace short source with verifier, 24-word reading and suite 4 reading through the rule.",
    ),
    rec(
        "AUD-006-FUN004", "FUN", "low",
        "The rehearsal check had no outcome for a reading that is not verified",
        ["README.md (Application requirements: Rehearsal check)"],
        "With no length stated, a wrong password on a short source gives an unverified 24-word reading; the "
        "check defined only 'matches' and 'does not match'.",
        "An unverified reading is never reported as a match.",
        "An application could report 'matches' before the owner discards a backup.",
        "Report 'not verified' when only unverified readings result and no reference was supplied; ask for "
        "the length of a short source.",
        "Apply the rules to the wrong-password-detect case.",
    ),
    rec(
        "AUD-006-SEC001", "SEC", "medium",
        "The recovery plan advised recording the source length next to the backup",
        ["docs/DESIGN-NOTES.md (Losing access: A recovery plan)", "README.md (Creating a container, step 2)"],
        "The supplement told the owner to record the source length in every case; the specification asked "
        "for the word count in the rare case without saying where to keep it.",
        "Recovery needs only the container and the password by default, and a note showing a short source "
        "is kept apart from the container.",
        "A found note showing fewer than 24 words removes the decoy option that the deniability analysis "
        "relies on.",
        "Record only what recovery needs, the word count only in the rare case, and keep that note apart "
        "from the container like the password.",
        "Read both passages against the deniability limits.",
    ),
    rec(
        "AUD-006-SEC002", "SEC", "low",
        "The re-encryption risk figure named the wrong cause and left one accepted risk unstated",
        ["README.md (Re-encryption)"],
        "The `2^-32` figure was attributed to any short verifier, although it comes from the 32-bit verifier "
        "of the 21-word layout, and a stated 21 that matches was accepted on that verifier without saying so.",
        "The figure names its source and the accepted case states its risk.",
        "Readers could treat a stated 21-word match as stronger than it is.",
        "Attribute the figure to the 21-word layout and wrong passwords, and state the accepted risk.",
        "Recompute 2^-128 + 2^-96 + 2^-64 + 2^-32.",
    ),
    rec(
        "AUD-006-SEC003", "SEC", "low",
        "The BIP39 passphrase and seed were missing from the network and memory rules",
        ["README.md (Offline use and no secrets on the network; Sensitive memory)"],
        "Every 24-word reading now takes the BIP39 passphrase and computes the BIP39 seed, but neither was "
        "named in the network ban or the sensitive-memory list.",
        "Every secret that recovery handles is covered by both rules.",
        "An implementation could treat the passphrase or the seed as outside both rules.",
        "Name the BIP39 passphrase and the BIP39 seed in both rules.",
        "Read both rules.",
    ),
    rec(
        "AUD-006-BLD001", "BLD", "medium",
        "The text still presents itself as release 0.5.0",
        ["README.md (badge, banner, preamble, release line, previous releases)", "CITATION.cff", "CHANGELOG.md"],
        "Badge, banner, preamble version and citation metadata say 0.5.0 and 'Released as v0.5.0', while the "
        "text holds normative changes that change conformance; the previous-releases list lacks v0.5.0.",
        "The released text names its own version; an implementation conforming to 0.5.0 is not assumed to "
        "conform to the new text.",
        "Readers and implementers would take the changed rules for the released 0.5.0 rules.",
        "At release, set version 0.6.0 (a minor version: conformance changed, suites did not), date the "
        "CHANGELOG section, add v0.5.0 to the previous releases and rewrite the banner sentence.",
        "Read the version strings and run the document checks after the change.",
        status="fixed", blocking=True,
        blocking_reason="A release must carry its own version; set to 0.6.0 in the release commit.",
    ),
    rec(
        "AUD-006-DOC001", "DOC", "medium",
        "The CHANGELOG described the re-encryption rule as a recommendation",
        ["CHANGELOG.md (Unreleased)"],
        "'should check a wallet-identity reference when several lengths match or the owner states another "
        "length'; the specification makes this a MUST, also with no stated length, and adds the private-screen "
        "path.",
        "The changelog states normative changes at their actual strength.",
        "Implementers reading the changelog would miss a mandatory change.",
        "State the MUST, all three conditions and the private-screen path.",
        "Compare the entry with the rule.",
    ),
    rec(
        "AUD-006-DOC002", "DOC", "medium",
        "The prose terms the rules depend on were not defined",
        ["README.md (Conventions and Terminology)"],
        "Source, original seed phrase, container phrase, reading, stated and detected length and "
        "wallet-identity reference were used before or without a definition.",
        "Terms used by normative rules are defined once, before their first use.",
        "Readers must infer the meaning of the length rules from context.",
        "Add a short definitions paragraph.",
        "Read the paragraph against the uses of each term.",
    ),
    rec(
        "AUD-006-DOC003", "DOC", "medium",
        "The suite 4 admission table said a phrase is supplied where a word count is meant",
        ["README.md (suite 4: Choosing the suite and the length during recovery)"],
        "Rows read 'An original seed phrase of n words' under the header 'Supplied with the container'.",
        "The rows name a length.",
        "The table could be read as asking for the original seed phrase.",
        "Write 'A length of n words'.",
        "Read the table and the sentence after it.",
    ),
    rec(
        "AUD-006-DOC004", "DOC", "low",
        "The supplement said every recovery runs the 16-bit check",
        ["docs/DESIGN-NOTES.md (five places)", "README.md (Recovering a mnemonic)"],
        "The rule applies to every 24-word reading, not to every recovery; it was restated about ten times in "
        "slightly different words.",
        "One normative statement, with the supplement referring to its analysis.",
        "Suite 4 and short-only recoveries could be thought to run the check.",
        "Say 'every 24-word reading' and trim the restatements.",
        "Search for 'every recovery'.",
    ),
    rec(
        "AUD-006-DOC005", "DOC", "low",
        "The supplement restated the length rules in part",
        ["docs/DESIGN-NOTES.md (Source-length identification; Derived wallets of a chosen length; Known Limitations)"],
        "A partial copy of the normative rules omitted two cases, and Known Limitations stated a rule.",
        "The supplement gives the probabilities and points to the rules.",
        "Two versions of one rule drift apart.",
        "Replace the copies with a pointer to Recovering a mnemonic.",
        "Read the three places.",
    ),
    rec(
        "AUD-006-DOC006", "DOC", "low",
        "The independent replay was described as covering the current recovery rules",
        ["docs/DESIGN-NOTES.md (Open questions; Reference Implementation; Test Vectors)"],
        "The replay of every recovery case was not marked as made under the rules of that time.",
        "The evidence names the rules it covers.",
        "The replay could be taken as evidence for the current length rules.",
        "Add 'under the recovery rules of that time' and point to the current expectations.",
        "Read the three places.",
    ),
    rec(
        "AUD-006-DOC007", "DOC", "low",
        "Three different timings for one Argon2id call",
        ["README.md (Rationale)", "docs/DESIGN-NOTES.md (Parameter rationale; Performance measurements)"],
        "4.4 to 7 s, 5 to 10 s and 4.6 to 5.0 s were given for the same call on the same laptop; no record "
        "contains 4.4 s.",
        "One figure from the measurement record.",
        "Readers cannot tell which figure is measured.",
        "Use about 4.6 to 5.0 s (C) and about 10 s (OpenSSL), with a pointer to the measurements.",
        "Compare with the cited measurement record.",
    ),
    rec(
        "AUD-006-DOC008", "DOC", "low",
        "The cycle-walking tail was computed at a different speed than elsewhere",
        ["docs/DESIGN-NOTES.md (Final-word-preserving cycle walking)", "README.md (Why is the final word not preserved?)"],
        "'up to about 13 days at the 99th percentile' assumes 120 s per permutation; Part II gives 183 h at the "
        "measured 70 s.",
        "Figures state their basis and agree.",
        "A factor of almost two between two places.",
        "Use the measured 70 s (about 1.7 days mean, 8 days at the 99th percentile) and state the 1-2 minute "
        "basis in the specification.",
        "Recompute with a geometric distribution, p = 1/2048.",
    ),
    rec(
        "AUD-006-DOC009", "DOC", "low",
        "The non-conformance of implementation versions 0.4.0 and 0.5.0 was buried",
        ["docs/DESIGN-NOTES.md (Reference Implementation; Known Limitations)", "CHANGELOG.md"],
        "The override of detection by a stated length was mentioned in a relative clause only.",
        "A known non-conformance is stated plainly and listed with the limitations.",
        "Users of those versions would not learn that they behave differently.",
        "State it plainly and add a Known Limitations bullet.",
        "Read both places.",
    ),
    rec(
        "AUD-006-DOC010", "DOC", "low",
        "The suite selection rule was stated four times",
        ["README.md (suite 4: Recovering a mnemonic; Choosing a length during recovery; table)"],
        "Word count selects the suite in four places, and the 24-word rejection twice.",
        "One paragraph holds the rule and its MUSTs.",
        "Copies drift apart.",
        "Merge into 'Choosing the suite and the length during recovery' and point to it.",
        "Read the suite 4 section.",
    ),
    rec(
        "AUD-006-DOC011", "DOC", "low",
        "The supplement's contents did not match its Part II headings",
        ["docs/DESIGN-NOTES.md (Contents)"],
        "Relabelled entries and missing sections.",
        "Contents list the headings with their exact titles.",
        "Readers cannot find several sections.",
        "List the Part II headings exactly.",
        "Link check of every contents anchor.",
    ),
    rec(
        "AUD-006-DOC012", "DOC", "low",
        "Variant names for defined terms and symbols",
        ["README.md", "docs/DESIGN-NOTES.md"],
        "'wallet reference', 'seed check', 'source phrase', and `m_bits`, `t_eff`, `P_encoded`, `SUITE_{ID}` "
        "beside the defined forms.",
        "One name per concept, as the specification defines it.",
        "Readers may take variants for different things.",
        "Use wallet-identity reference, source check, original seed phrase and the specification's symbols.",
        "Search for each variant.",
    ),
    rec(
        "AUD-006-DOC013", "DOC", "low",
        "The CHANGELOG mixed changes and filed one under the wrong release",
        ["CHANGELOG.md"],
        "One 16-line bullet held several changes; substantive Reference Implementation changes were described "
        "as link updates; the signing-key note made after v0.5.0 sat under 0.5.0; the 0.5.0 suite 4 revision "
        "had no pointer to the commit with the same files.",
        "One entry per change, under the release that contains it.",
        "Readers cannot see the separate changes or where they belong.",
        "Split the entry, describe the Reference Implementation change, move the signing-key note and add "
        "the pointer.",
        "Compare the entries with the diff.",
    ),
    rec(
        "AUD-006-DOC014", "DOC", "low",
        "Long sentences and repeated warnings in the replacement rules",
        ["README.md (Re-encryption; Preserving derived wallets)", "docs/DESIGN-NOTES.md (two wallet sections)"],
        "A 20-line Re-encryption bullet, a 66-word warning sentence, and the warning copied into two supplement "
        "sections.",
        "Short sentences; the warning stated once.",
        "The rules are hard to follow and copies drift.",
        "Split into sub-bullets, shorten the warning and point to it from the supplement.",
        "Read the passages.",
    ),
    rec(
        "AUD-006-DOC015", "DOC", "low",
        "Forward references without links",
        ["README.md (Recovering a mnemonic; Work factor)"],
        "References to the source check and the rehearsal check 'below' had no link.",
        "Forward references are linked.",
        "Readers have to search.",
        "Link them.",
        "Link check.",
    ),
    rec(
        "AUD-006-DOC016", "DOC", "low",
        "The implementation version of the new rules is not named",
        ["README.md (Reference Implementation)"],
        "The section describes versions 0.4.0 and 0.5.0 only.",
        "It names the version that implements the current rules and pins its corpus revision.",
        "Readers cannot tell which implementation conforms.",
        "After the implementation's 0.6.0 release, name it with its corpus revision.",
        "Read the section after the import of AUD-006-FUN001.",
        status="open",
    ),
    rec(
        "AUD-006-DOC017", "DOC", "low",
        "The audit index list was loose",
        ["docs/audits/README.md"],
        "Blank lines between items 3, 4 and 5.",
        "No blank line inside a Markdown list.",
        "Inconsistent rendering.",
        "Remove the blank lines.",
        "Read the list.",
    ),
    rec(
        "AUD-006-DOC018", "DOC", "low",
        "The AUD-005 publication record is edited for every later document change",
        ["docs/audits/AUD-005-publication.json", "docs/audits/AUD-004-publication.json"],
        "Later specification changes are carried into the AUD-005 bindings, whose entries keep their earlier "
        "dates while their reasons grow.",
        "A record binds the state it describes; later changes get their own record.",
        "Every README edit forces an edit of an older audit record.",
        "Owner decision: freeze the AUD-005 bindings at the release state and bind later documents in the "
        "next release record, or give each later edit its own dated entry.",
        "Run the AUD-005 validator after the decision.",
        status="deferred",
    ),
]

OBSERVATIONS = [
    rec(
        "AUD-006-DOC019", "DOC", "info",
        "Remaining overlap between Part II and the specification",
        ["docs/DESIGN-NOTES.md (Part II)"],
        "Part II still restates parts of Backward Compatibility, resource limits, sensitive-memory handling and "
        "the side-channel note; the rare-case word-count advice and the equal-container note were reduced to "
        "pointers.",
        "Requirements are stated once.",
        "Minor; the copies agree today.",
        "Shorten further when Part II is next revised.",
        "None for this release.",
        status="accepted", kind="observation",
    ),
    rec(
        "AUD-006-DOC020", "DOC", "info",
        "Seed-check results of the other 24-word readings were not recorded",
        ["vectors/suite3/README.md"],
        "Only `selected-24-words` recorded its 16-bit check result.",
        "Each 24-word reading of the corpus has its check result.",
        "Implementers had no expected value for the other cases.",
        "List the empty-passphrase digests: 1d8a88b4, 8d4927e3, a08e73ba, 9afb047d.",
        "Recompute with PBKDF2-HMAC-SHA512 and the profile's SHA-256.",
        kind="observation",
    ),
    rec(
        "AUD-006-DOC021", "DOC", "info",
        "The suite 4 notes did not list the helper script its verifier imports",
        ["vectors/suite4/README.md"],
        "The suite 4 verifier imports scripts/independent-suite3.py, whose hash the record pins.",
        "Every pinned source file is listed.",
        "Provenance was incomplete in the notes.",
        "Add the row with SHA-256 bcc12b46f4cf91e94542627eb79c748f562814b64ed6cda5cf978eb6acb20c07.",
        "git show of the file at the pinned revision.",
        kind="observation",
    ),
    rec(
        "AUD-006-FUN005", "FUN", "info",
        "The reference implementation's derived-wallet warning differs from the specification",
        ["specification README.md (Preserving derived wallets)"],
        "The implementation speaks of 'funds at the old addresses' and advises destroying the old container "
        "without a condition about wallets that other passwords open.",
        "The warning names wallets that other passwords open on the old container.",
        "Owners could destroy a container that a derived wallet still needs.",
        "Handed to the implementation; no specification change.",
        "Check the implementation's warning text before its release.",
        status="open", kind="observation",
    ),
    rec(
        "AUD-006-BLD002", "BLD", "info",
        "Untracked repository files",
        ["AGENTS.md", "docs/drafts/"],
        "Both are untracked and not excluded; AGENTS.md claims that every vector is reproducible by the current "
        "implementation, which is not true for the archived suite 2 vectors.",
        "Repository files are either committed or excluded.",
        "A careless add could commit them.",
        "Owner decision: commit AGENTS.md with the claim corrected, or exclude it; exclude docs/drafts/.",
        "git status before the release commit.",
        status="open", kind="observation",
    ),
]

FIXED_BY_HARNESS = (
    "The baseline link check reported one broken anchor in docs/audits/audit-01-2026-09-22.md. It was link "
    "syntax quoted inside inline code; the harness now skips code spans and code blocks."
)
