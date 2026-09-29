"""Build the paired AUD-004 records from one reviewed finding register."""

import collections
import datetime
import json
from pathlib import Path
import re


EVIDENCE = Path(__file__).resolve().parents[1]
ROOT = EVIDENCE.parents[2]
WORKSPACE = ROOT.parent
AUDITS = EVIDENCE.parent
DATE = datetime.datetime.now(datetime.timezone.utc).date().isoformat()
SNAPSHOT = json.loads((EVIDENCE / "snapshot.json").read_text())
PROCEDURES = json.loads((EVIDENCE / "procedure-hashes.json").read_text())


def finding(number, title, locations, reproduction, expected, observed, impact, fix, verification, evidence):
    return {
        "id": f"AUD-004-DOC{number:03}",
        "category": "DOC",
        "kind": "finding",
        "title": title,
        "severity": "low",
        "status": "open",
        "releaseBlocking": False,
        "releaseBlockingReason": "A bounded documentation defect; no current suite-3 cryptographic or recovery failure was demonstrated.",
        "affectedFiles": locations,
        "reproduction": reproduction,
        "expected": expected,
        "observed": observed,
        "impact": impact,
        "recommendedFix": fix,
        "requiredVerification": verification,
        "evidence": evidence,
    }


findings = [
    finding(
        1,
        "CR/LF exclusion is incorrectly explained as universal single-line input",
        ["README.md:201-213, especially 208-210"],
        "Apply the written password rules to A + U+2028 LINE SEPARATOR + B. It is assigned in Unicode 17, contains no CR/LF, is NFKD-stable, and encodes as 41 e2 80 a8 42. U+0085, U+2029 and embedded NUL are other accepted controls/separators. The retained Node Unicode-17 probes check these properties without invoking MHFE.",
        "The explanation should describe the precise accepted character domain and should not promise that all such inputs are ordinary single-line text in every interface.",
        "The normative restriction excludes CR and LF only, but its rationale says a password is a single line so every interface can take it as typed. This is broader than the rule actually establishes.",
        "An implementer could infer additional filtering or unsupported input-widget behavior. This is a prose defect, not evidence that an existing utility corrupts passwords. The byte-level acceptance rule itself is coherent.",
        "Replace the universal claim with: 'This rule excludes CR and LF record separators. It does not exclude other Unicode line or paragraph separators; interfaces must preserve every other accepted scalar value exactly.' Explain entry of legal controls separately. Do not reject additional characters as an editorial correction to this frozen suite.",
        "Keep the accepted-input domain unchanged; check CR, LF, U+0085, U+2028, U+2029, NUL and whitespace against exact normalized UTF-8 expectations. Re-read the rationale for agreement with that domain.",
        ["AUD-004-evidence/protocol-algebra.log", "AUD-004-evidence/protocol-unicode.log", "AUD-004-evidence/agent-protocol-review.md", "AUD-004-evidence/agent-editorial-review.md"],
    ),
    finding(
        2,
        "Parallel-lane rationale misattributes the historical benchmark and overgeneralizes it",
        ["docs/DESIGN-NOTES.md:411-415", "docs/DESIGN-NOTES.md:1973-1999"],
        "Compare the Part I claim of about 60 seconds with 'single-threaded reference code' and about 34 seconds with a multithreaded implementation to the retained measurement table. The table identifies RustCrypto argon2 0.5.3 for the approximately 60-second result and OpenSSL through Python cryptography for 34.26 seconds; the ratio is about 1.75.",
        "Identify the engines correctly and separate the measured implementation comparison from an isolated measurement of thread-count effects.",
        "Current text uses 'reference code' for the slow historical run, while elsewhere 'reference C code' names a different engine. It concludes that absence of threads makes an operation several times slower, although this particular comparison changes both engine and threading and is about 1.75 times.",
        "The reader receives a misleading account of the evidence used to justify a performance requirement. No algorithm-output disagreement, measured current implementation defect or performance regression is established.",
        "Name RustCrypto argon2 0.5.3 and the OpenSSL-backed cross-check explicitly. Say the historical observations combine implementation and threading differences. Replace the universal 'several times' statement with a platform- and engine-dependent slowdown, or supply a controlled measurement that supports a more specific statement.",
        "Compare the revised prose with the historical table and preserve its original numbers. A new utility benchmark is unnecessary to correct the attribution and was not authorized in this audit.",
        ["AUD-004-evidence/agent-editorial-review.md"],
    ),
    finding(
        3,
        "Memory rationale incorrectly places 3 TiB beyond all current computers",
        ["docs/DESIGN-NOTES.md:366-368"],
        "Read the level-21 explanation and its claim that such amounts are far beyond today's computers. Compare the official AWS 2019 announcement, which documents 18- and 24-TiB bare-metal systems and a table beginning at 6 TiB.",
        "Distinguish typical personal recovery computers from all existing computers. The MEM ceiling follows the Argon2 parameter field, not the absence of hardware.",
        "The text makes an unqualified hardware-existence claim contradicted by systems documented years before this draft.",
        "A limited factual error in parameter rationale. The MEM formula, 3-TiB value and RFC upper-bound arithmetic remain correct. The reference to hosted hardware establishes existence only; it is not a recommendation for online recovery.",
        "Use 'Such amounts are far beyond ordinary personal computers and are retained as headroom. The upper bound follows Argon2id's parameter limit, not a limit on available hardware.'",
        "Preserve all memory mappings and range checks; confirm that the revised hardware statement names the intended device class.",
        ["AUD-004-evidence/agent-editorial-review.md", "AUD-004-evidence/primary-sources.md", "https://aws.amazon.com/blogs/aws/ec2-high-memory-update-new-18-tb-and-24-tb-instances/"],
    ),
    finding(
        4,
        "Historical cycle-walk theorem is applied without qualifying the rejecting wrapper",
        ["docs/DESIGN-NOTES.md:1677-1681", "docs/DESIGN-NOTES.md:1814-1825"],
        "Take the permutation (0 1)(2 3) on four states and the target class {0,2}. Ordinary cycle walking maps 0 to 0 and 2 to 2 after two steps. The documented rule instead returns failure for both because no distinct class member is met. The retained analytical probe reproduces the complete counterexample.",
        "Separate the total mathematical class permutation from the operational wrapper that refuses its fixed points. Black and Rogaway section 4 explicitly permits a first return to the original point.",
        "The archived profile requires failure on a return to the start, but the later analysis describes the resulting design as a permutation on each whole class and cites the uniform-permutation theorem without that distinction.",
        "A theoretical characterization error in historical/research text. The rejecting map remains invertible on accepted cycles, and no practical suite-3 attack is shown. In the ideal model the rejection probability for one input is 1/class-size, approximately 2^-245 for the proposed final-word class; this is not a practical recovery-break claim. Suite 3 does not include this feature.",
        "Keep the refusal rule. Add an explanatory qualification: ordinary cycle walking induces the class permutation; the operational MHFE wrapper rejects its fixed points. The cited theorem applies before that rejection. Preserve the archived rule rather than silently changing it to match the theorem.",
        "Check the four-state counterexample and a class cycle with a distinct accepted successor against the revised wording. Do not claim a total wrapper or change historical protocol behavior.",
        ["AUD-004-evidence/appendix-analytical.log", "AUD-004-evidence/agent-appendix-review.md", "https://web.cs.ucdavis.edu/~rogaway/papers/subset.pdf"],
    ),
    finding(
        5,
        "Restricted-image argument overgeneralizes deterministic packing to every lossless encoding",
        ["docs/DESIGN-NOTES.md:1506-1510"],
        "For a one-bit source E, encode as E || U with a free random bit U; decode the first bit. E=0 has representations 00 and 01; E=1 has 10 and 11. Decoding is lossless but the representation union has four states, not two. More generally E || U with 256-ENT random bits can use the full 256-bit representation space.",
        "The exact 2^ENT image-size statement should be restricted to deterministic injective encodings, including the selected MHFE packing.",
        "The text calls the restricted size mathematically unavoidable for 'any lossless encoding'. Losslessness alone does not require a single representation per source.",
        "A bounded false universal statement in the historical analysis. It does not invalidate the selected deterministic E || verifier construction, its exact verifier cardinality, or the full-256-bit authentication-capacity argument. Random filler would abandon the chosen verifier and deterministic-container properties; it is not proposed as a repair to MHFE.",
        "Change the quantifier to 'any deterministic lossless encoding of an ENT-bit source into a 256-bit state'. Explain, only if useful, that randomized representations trade away properties deliberately selected here.",
        "Use the complete four-state counterexample to confirm why the qualifier is needed, and recheck that the preceding claim for the actual deterministic packing still has exactly 2^ENT states.",
        ["AUD-004-evidence/agent-appendix-review.md"],
    ),
]

recommendations = [
    {
        "priority": "Before stability",
        "title": "Publish the suite-3 interoperability corpus and its provenance",
        "locations": "README.md:574-591; DESIGN-NOTES.md:504-505",
        "text": "The draft openly says the 17 positive suite-3 vectors and their independent reproduction are not yet published. This is a declared readiness gap, not a newly discovered broken promise or evidence that the private cross-check never happened. Publish exact source and normalized password bytes, packing, salt/mask message bytes, all round values, expected mode-specific outcomes, producer and verifier revisions, hashes and licenses. Include all five source lengths, non-zero entropy, PIM and MEM separately and together, and both inverse and forward paths. Add cheap representation fixtures alongside expensive end-to-end vectors. This audit did not run or audit any implementation, so it cannot confirm the claimed 17-vector reproduction.",
    },
    {
        "priority": "Before stability",
        "title": "Define the security games and computational budgets before changing primitives",
        "locations": "DESIGN-NOTES.md:75-180, 495-503",
        "text": "Specify ciphertext-only, known-pair, chosen-input, multi-container and leaked-state games separately. Give budgets for Argon2 queries, ordinary hash work, memory and preprocessing; define the password/source distributions and A1 joint behavior explicitly. The eleven-call known-pair construction is valid, but neither its optimality nor a twelve-call ciphertext-only lower bound is proved. Uniform random round-function theorems do not automatically apply to one low-entropy password and state-derived Argon2 inputs. Commission independent cryptographic analysis of those questions. The present audit supplies no reason to change the hashes, add rounds, lower rounds, increase memory, or revive cycle walking.",
    },
    {
        "priority": "High practical value, same format",
        "title": "Standardize recovery context and explicit result states",
        "locations": "README.md:186-197, 294-317, 344-363",
        "text": "Recommend recording the original word count with suite/PIM/MEM for every container, not only when a creation-time overlap is detected. Distinguish malformed input, verifier mismatch, a verified short-format relation, ambiguous length and an unverified 24-word candidate. Explicitly apply the unverified label to manual 24-word selection too. A verifier match is not wallet-identity confirmation: compare a known receiving address with correct network/type/path and any separate BIP39 passphrase. The 32-bit master fingerprint remains a weaker convenience check. These are application-contract improvements without changing cryptographic bytes; the existing manual mode already handles overlap.",
    },
    {
        "priority": "High practical value, same format",
        "title": "Expand normalization and negative-outcome conformance cases",
        "locations": "README.md:198-213, 580-585",
        "text": "In addition to NFKD expansion past 1024 bytes, include contraction from a longer raw string to exactly 1024 normalized bytes: 1024 U+FF21 characters occupy 3072 raw UTF-8 bytes but normalize to 1024 ASCII bytes and are valid. Cover exact 1024/1025 normalized boundaries, canonical-equivalent spellings, NUL, spaces, accepted Unicode separators, Cn/noncharacters, Private Use, invalid UTF-8 and unpaired surrogates. Negative vectors must name the selected recovery mode and expected rejection, ambiguity or unverified output: a wrong password does not universally cause an error. Keep this corpus independent of implementation parsing code.",
    },
    {
        "priority": "Evidence improvement",
        "title": "Calibrate attack costs and display a sensitivity range",
        "locations": "README.md:110-126; DESIGN-NOTES.md:182-308",
        "text": "The table arithmetic is correct at its declared precision, but it uses assumed rates. Make a compact assumptions table for hardware, bandwidth, memory capacity, MHFE candidates/s, PBKDF2 candidates/s, mean half-space search and omitted wallet work. Supply reproducible benchmark inputs, kernels and revisions before treating the roughly 20.5-bit ratio as empirical. A primary RTX-4090 Hashcat benchmark supports the order of magnitude of the assumed PBKDF2 rate after iteration scaling, but it varies PBKDF2's password whereas a BIP39 passphrase varies its salt. It does not measure the complete wallet search or suite-3 Argon2 attack. Show results parametrically as log2(R_BIP39/R_MHFE); a factor-of-ten change moves the cost comparison by about 3.32 bits. Give the 25-card farm an explicit bandwidth assumption; capacity alone does not yield 90 candidates/s. Benchmarking utilities is future work outside this audit.",
    },
    {
        "priority": "Clarity, same format",
        "title": "Retain the present structure and add precise reading routes",
        "locations": "README.md Rationale; DESIGN-NOTES.md:3-33, 507-518",
        "text": "Keep the nine Rationale answers in README. Its current sequence is coherent and the earlier round-trip reorganization should not be repeated. Add navigation within the approximately 1600-line historical Part II, plus clear deep-link historical labels where useful. Restate the current side-channel caveat briefly in Part I, since its introduction carries forward only explicitly restated conclusions while README advertises side-channel discussion. Link T1-T6 as a historical taxonomy rather than making readers infer current parameter applicability.",
    },
    {
        "priority": "Clarity, same format",
        "title": "Use consistent probabilistic and operational language",
        "locations": "README.md:351-363, 529-533; DESIGN-NOTES.md:54-56, 143-149, 305-307",
        "text": "Qualify the opening no-shared-dictionary sentence with the same collision/repeated-state exception already present later. Prefer 'passes the verifier' to 'confirms the password'. Change the potentially overread plate-substitution sentence to 'may be detected during recovery', with wallet-identity comparison at every length. Explain that rehearsal forbids persistent storage, clipboard and external disclosure while still requiring temporary computation in sensitive memory. None of these wording improvements establishes an existing utility vulnerability.",
    },
    {
        "priority": "Conditional future protocol",
        "title": "Treat authentication and self-description as an explicit alternative format",
        "locations": "README.md:185-197, 294-317, 529-548",
        "text": "If version/settings storage and cryptographic authenticity become requirements, design a separate expanded envelope using established authenticated encryption and a stored random salt, or explicitly restrict the source domain. A lossless permutation covering every 256-bit source consumes all 256-bit outputs; no independent tag/version field can be added for free. Likewise the union of all five source-length domains cannot fit injectively into that domain without external length context. Such a format could simplify recovery and authentication but would abandon the present single-24-word/no-metadata requirement and require its own identifier, analysis and vectors. It is not a necessary repair or an instruction to modify suite 3 now.",
    },
]

technical = [
    ("Normative byte framing", "Reviewed suite/domain labels, raw bytes, BE32 settings and round index, bit order and leftmost truncation. Both salt and mask message lengths are 68 bytes. BLAKE2b digest parameterization is explicitly distinguished from truncating a 512-bit digest. No missing output-affecting Argon2 input was identified."),
    ("Permutation and inversion", "The inverse matches the forward equations without a hidden final swap. Synthetic round functions test algebra only: 500 round trips and 6000 omitted-round positions in one probe; a separate 8-bit-branch probe checks 12000 known-pair equalities. These overlapping exercises are not added into a production-test total and establish no cryptographic bound."),
    ("Packing and verifier", "All five source widths fit one 256-bit state; short-source verifier prefixes contain the original BIP39 checksum. For uniform candidate states, an explicitly selected r-bit verifier accepts exactly 2^-r by counting, without a random-oracle assumption for that counting identity. Applying it to real wrong-password decryptions requires a distribution assumption."),
    ("Length ambiguity", "The four-check union is between 2^-32 and 2^-32+2^-64+2^-96+2^-128 for uniform states. Deliberately using a packed short state as genuine 24-word entropy creates overlap with certainty; the manual mode resolves it. There is no newly discovered automatic-detection break: the limitations are already described."),
    ("Work-factor range", "All 22 MEM levels are exact integer KiB and multiples of 16, so four-lane RFC memory rounding has no effect. MEM 21 is 3 TiB; MEM 22 exceeds 2^32-1 KiB. PIM 1023 gives 12288 passes per round. Hardware-support refusal and no silent parameter reduction are specified. No high-memory allocation or runtime benchmark was performed."),
    ("Unicode and input boundaries", "Node 26.10.0 reports Unicode 17.0. The audit-only census visits all 1112064 scalar values, including 297334 assigned values in that runtime. Only CR and LF normalize to strings containing CR/LF. Cn/noncharacters, Private Use, NUL and normalized-size expansion/contraction match the narrow written contract. This is not an exhaustive cross-library normalization certification or an MHFE interface test."),
    ("Known pairs and early filters", "The one-skipped-round Feistel equality provides the stated eleven-call filter. Two missing adjacent masks do not yield that same equality test. The description correctly does not claim an optimality theorem; the free-fast-hash lower-bound counterargument and sensitive intermediate-salt filters are coherent."),
    ("Salt diversification and determinism", "Repeated state/password/settings repeat outputs. For independent uniform branches the two routes to salt equality give approximately 2^-127, not guaranteed uniqueness. Public end salts and sensitive internal salts are distinguished. No practical bulk-precomputation attack was established; the A1 model remains an assumption."),
    ("Password and passphrase composition", "The sequential-search estimates correctly include false-verifier survivors. Four EFF words give about 425633 false matches with a 32-bit verifier; with a five-word passphrase the false-match work is about 4413 times the MHFE term under the stated rates. Independent 30-bit secrets in the 24-word model give about 12195 model years. These are strategy estimates, not lower bounds."),
    ("Cost tables and hidden PIM", "Two through five EFF words carry approximately 25.85/38.77/51.70/64.62 bits. At the assumed rates the four-word row is about 57.93 million MHFE years and 38.62 BIP39 years. Conditional and averaged hidden-PIM formulas agree with exact finite sums; the large-N Q=1024 mean ratio is about 683. Botnet rounding between 8000/s and 1000000/120/s explains about 56 versus 54 million years; this is within the table's approximate precision."),
    ("Cycle walking and alternatives", "Under the stated geometric approximation: mean 2048, median 1420, 95th percentile 6134, 99th percentile 9430; timing-match probability 1/4095 and average minimum walk 1024.250061. The 253-bit alternative and Direction B skipped-gap relations are consistent. The rejection-wrapper theorem error is separately tracked; none of these research modes is suite 3."),
    ("Security and operational boundaries", "The draft discloses lack of authentication, no intrinsic 24-word password check, deterministic leakage, experimental status, limits of self-checks and unproved construction-specific security. Creation refuses fixed points and requires checking recovery from encoded words. External recovery context and reference checks are important. Implementation enforcement of any of these rules was excluded."),
    ("Structure and references", "README's use-case -> definitions -> algorithm/workflow -> rationale -> security -> interoperability sequence is coherent. Part I/Part II are explicitly current versus historical. All 48 local Markdown links and 44 consecutive bibliography entries passed the scoped link/numbering check. Selected primary references were checked semantically; not every one of the 44 publications or prior-art implementations was independently audited."),
]

prior = [
    ("AUD-001-DOC001", "The current README provides a locatable implementation repository link; only the written locator was checked."),
    ("AUD-003-DOC001", "Current password wording explicitly rejects Unicode-17 Cn/noncharacters and accepts Private Use. The old ambiguity is resolved; DOC001 in this report concerns a different single-line rationale."),
    ("AUD-003-DOC002", "Creation now requires the self-check and withholds programmatic output until it passes."),
    ("AUD-003-DOC003", "Current text distinguishes public end salts from secret intermediate salts and explains shortened leaked-salt filters."),
    ("AUD-003-DOC004", "The number of rounds N is defined adjacent to the one-in-N discount."),
    ("AUD-003-DOC005", "The secret-PIM formula replaces the old incorrect ceiling and passes the present independent arithmetic check."),
    ("AUD-003-DOC006", "Not rechecked: CHANGELOG is outside the user-authorized scope."),
]

guide = (WORKSPACE / "multi-chain-wallet-tools/docs/FULL_AUDIT_GUIDE.md").read_text()
check_names = dict(re.findall(r"^### (CHECK-[A-Z]+-\d+) — (.+)$", guide, re.M))
applicable = {
    "CHECK-SEC-001": ("passed", "Threat-model, secret ownership and deterministic-leakage contract review; no implementation trace.", "agent-protocol-review.md"),
    "CHECK-SEC-004": ("passed", "Encryption/inversion, framing, verifier, authentication limits and security-game analysis; no cryptographic primitive implementation certification.", "protocol-algebra.log"),
    "CHECK-SEC-007": ("passed", "Specified password/resource bounds, explicit initiation/cancellation and parameter-refusal semantics.", "protocol-unicode.log"),
    "CHECK-FUN-001": ("passed", "BIP39 entropy/checksum/word-count and Unicode contract analysis, synthetic packing examples.", "protocol-algebra.log"),
    "CHECK-FUN-006": ("passed", "Current recovery states and backup semantics; archived alternatives examined separately.", "agent-appendix-review.md"),
    "CHECK-API-001": ("passed", "Documented Argon2/BLAKE2 input contract compared with primary specifications; local library calls excluded.", "primary-sources.md"),
    "CHECK-API-004": ("passed", "Normative byte framing, normalization and representation boundaries; actual implementation interoperability not run.", "protocol-unicode.log"),
    "CHECK-ARC-001": ("passed", "Ownership of normative README, informative Part I and historical Part II is explicit.", "agent-editorial-review.md"),
    "CHECK-ARC-002": ("passed", "Duplication, structure and all seven applicable prior editorial corrections reviewed.", "agent-editorial-review.md"),
    "CHECK-ARC-003": ("failed", "Theoretical prose overgeneralizations and benchmark evidence mismatch: DOC002, DOC004 and DOC005.", "agent-appendix-review.md"),
    "CHECK-DOC-001": ("failed", "Bounded explanatory defects: DOC001-DOC005; no practical current protocol break established.", "agent-editorial-review.md"),
    "CHECK-DOC-002": ("failed", "Links/numbering/format pass; benchmark provenance and hardware claim need corrections DOC002/DOC003.", "document-links.log"),
    "CHECK-DOC-003": ("passed", "Paired report, categorized IDs, source/procedure hashes, ledger, links and JSON validated before handoff.", "report-validation.json"),
}
excluded_reasons = {
    "SEC": "No executing application is in scope: browser isolation, network traffic, secret lifecycle and persistence enforcement belong to excluded utilities.",
    "FUN": "No wallet derivation, signing, transaction, discovery or provider implementation is in the two audited specification files.",
    "API": "No asynchronous application state, export implementation or monetary API is in scope.",
    "BLD": "The requested artifacts are specification text; dependency, build, CI, release and executable artifact verification were explicitly excluded.",
    "UI": "No executable UI/browser surface is in scope. Written application requirements were reviewed under SEC/FUN/DOC; rendered utility behavior was not tested.",
}
coverage = []
for check_id, title in check_names.items():
    category = check_id.split("-")[1]
    if check_id in applicable:
        outcome, method, evidence = applicable[check_id]
        coverage.append({"checkId": check_id, "category": category, "logicalGroup": title, "scope": "README and supplement, specification level only", "method": method, "outcome": outcome, "snapshot": SNAPSHOT["sourceFingerprint"], "evidence": f"AUD-004-evidence/{evidence}"})
    else:
        coverage.append({"checkId": check_id, "category": category, "logicalGroup": title, "scope": "Excluded executable/tooling surface", "method": "Not applicable to the authorized document artifacts", "outcome": "not-applicable", "snapshot": SNAPSHOT["sourceFingerprint"], "reason": excluded_reasons[category]})
assert len(coverage) == 32

command_checks = []
for path in sorted(EVIDENCE.glob("*.command.json")):
    item = json.loads(path.read_text())
    if item["name"] in {"build-report", "report-format", "validate-report"}:
        continue
    command_checks.append({**item, "outcome": "passed" if item["exitCode"] == 0 else "failed", "evidence": f"AUD-004-evidence/{item['log']}"})

limitations = [
    "Complete textual/analytical review of the requested README and both supplement parts; not an end-to-end project or utility audit.",
    "No mhfe implementation, command-line/browser utility, scripts/check-spec.py, dependency integration, build, CI, runtime memory/erasure, network enforcement or current benchmark was audited or executed.",
    "No actual Argon2 invocation, suite-3 vector reproduction, wallet derivation or browser acceptance test was performed. Toy functions validate equations only.",
    "Statements about implementation 0.4.0, the 17 independently reproduced positive vectors, 32-bit build behavior and historic execution are document claims; implementation-specific truth is not re-established here.",
    "CHANGELOG, citation/package metadata, artwork and vector-file content are outside scope; local link existence does not audit their content.",
    "Selected primary standards and theory were checked; all 44 references were numbered/linked internally, but no exhaustive literature, novelty or third-party implementation audit was performed.",
    "This review is not a formal cryptographic proof or an independent specialist certification. Parallel reviewers share the same AI workflow; they are not independent organizations or independently trained cryptographic implementations.",
    "The model/effort actually dispatched is not exposed in retained metadata. The user's Astra/ultra selection is recorded as user-reported, while the canonical exact values remain null.",
    "AUD-002 is reserved but absent from the repository; its unpublished findings cannot be exhaustively reconciled. Published prior findings were checked only where they concern the two current documents.",
    "Read-only reconnaissance and web calls are retained through source hashes, review workpapers and URLs rather than as complete terminal transcripts or full external-source archives. All executed analytical/format/link checks have command sidecars and log hashes.",
]

record = {
    "schemaVersion": 1,
    "auditId": "AUD-004",
    "auditNumber": 4,
    "date": DATE,
    "title": "Full specification-only audit of MHFE suite 3 README and supplement",
    "reviewer": SNAPSHOT["reviewer"],
    "reviewerPhases": [
        {"name": "Coordinator", "model": None, "reasoningEffort": None, "scope": "Entire text, cross-checking, sources, consolidation and report validation"},
        {"name": "Protocol review agent", "model": None, "reasoningEffort": None, "scope": "Normative algorithm, encoding, recovery and security contracts"},
        {"name": "Appendix review agent", "model": None, "reasoningEffort": None, "scope": "Entire supplement, equations, security arguments and historical research"},
        {"name": "Editorial review agent", "model": None, "reasoningEffort": None, "scope": "Entire text, structure, wording, provenance and earlier corrections"},
    ],
    "snapshot": {"commit": SNAPSHOT["commit"], "commitComplete": True, "workingTree": SNAPSHOT["workingTree"], "sourceFingerprint": SNAPSHOT["sourceFingerprint"], "sourceHashes": SNAPSHOT["sourceHashes"], "evidence": "AUD-004-evidence/snapshot.json", "note": "Snapshot includes pre-existing README, supplement and CHANGELOG edits plus untracked AGENTS.md and scripts/. AUD-004-evidence was created by this audit before the snapshot status capture; it is not a pre-existing source edit."},
    "scope": {"included": ["README.md, all 761 lines", "docs/DESIGN-NOTES.md, all 2116 lines, Parts I and II"], "excluded": SNAPSHOT["excluded"], "executionClass": "Full requested document-scope audit; not full-project end-to-end audit", "baselineOnly": True},
    "procedureHashes": PROCEDURES,
    "checks": command_checks,
    "coverageLedger": coverage,
    "findings": findings,
    "observations": [],
    "informationalAnalysis": [{"topic": t, "assessment": a} for t, a in technical],
    "recommendations": recommendations,
    "priorFindingReview": [{"id": i, "disposition": d, "scope": "Current text only; historical report not changed"} for i, d in prior],
    "pastedEditorialCorrections": {"verified": [1, 2, 3, 4, 5, 6, 8], "excluded": [7], "evidence": "AUD-004-evidence/agent-editorial-review.md"},
    "remediation": [{"id": f["id"], "status": "open", "fixCommit": None, "verificationCommit": None, "evidence": f["evidence"]} for f in findings],
    "assessment": {"critical": 0, "high": 0, "medium": 0, "low": 5, "currentProtocolBreakEstablished": False, "releaseAcceptance": "not assessed or granted; experimental readiness gaps remain", "recommendation": "Correct the five bounded documentation defects; prioritize published conformance evidence, clearer recovery states and construction-specific analysis over arbitrary primitive changes."},
    "limitations": limitations,
}
report_json = AUDITS / f"audit-04-{DATE}.json"
report_md = AUDITS / f"audit-04-{DATE}.md"
report_json.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")


def link(path):
    return f"[{path}]({path})"


lines = [
    "# AUD-004 — Full specification-only audit of MHFE suite 3",
    "",
    "The current specification is substantially coherent. This review found **five Low documentation defects**, no demonstrated practical attack on suite 3, and no confirmed Critical, High or Medium finding. The numerical model is internally consistent at its stated precision, and the normative Feistel/packing rules were algebraically consistent in the checks performed. These results do not prove cryptographic security or implementation conformance.",
    "",
    "The strongest next steps are to publish the suite-3 conformance corpus, make recovery context and result status explicit, calibrate the attack-cost model, and obtain construction-specific cryptographic analysis. There is no evidence from this audit that an arbitrary change of primitives, round count or memory default would improve the protocol. The current experimental warning remains appropriate.",
    "",
    "## Record metadata",
    "",
    "- **Audit number:** 4; **report ID:** AUD-004.",
    f"- **Started (UTC):** {SNAPSHOT['startedAt']}; **completed (UTC):** {DATE}.",
    "- **Reviewer:** Codex coordinator and three parallel protocol, appendix and editorial reviewers. Contributions are retained below; this is one audit, not four independent certifications.",
    "- **Exact model / actual reasoning effort:** unknown / unknown. The user reported selecting Astra at ultra before the review; no exact active service identifier or dispatched setting is available in retained metadata. Both canonical values are null rather than inferred.",
    f"- **Reviewed commit:** `{SNAPSHOT['commit']}` on `{SNAPSHOT['branch']}`.",
    "- **Working tree:** pre-existing edits in README.md, docs/DESIGN-NOTES.md and CHANGELOG.md; untracked AGENTS.md and scripts/. Current dirty source bytes are the audit baseline. The audit's own evidence directory also appears in the captured status because it was reserved first. No source, vector, utility or dependency remediation was applied; no commit or push was made.",
    f"- **Source fingerprint:** `{SNAPSHOT['sourceFingerprint']}`.",
    "- **Artifacts:** no executable/build artifacts examined. The current documentation hashes and safe scoped diff identify the reviewed source.",
    "- **Environment:** Linux x86_64, Python 3.14.4, Node 26.10.0 (Unicode 17.0), pnpm 12.5.1, local Prettier 3.9.9. No toolchain/dependency installation was needed. Rust, Docker and browser versions are not applicable to this authorized scope.",
    "",
    "| Reviewed source | SHA-256 |",
    "| --- | --- |",
]
for path, digest in SNAPSHOT["sourceHashes"].items():
    lines.append(f"| `{path}` | `{digest}` |")
lines += [
    "",
    "Evidence: " + ", ".join(link("AUD-004-evidence/" + p) for p in ["snapshot.json", "reviewed-source.diff", "environment.log", "procedure-hashes.json", "SHA256SUMS", "report-validation.json"]) + ".",
    "",
    "## Finding register",
    "",
    "| Finding / record ID | Category | Kind | Severity | Recorded status | Title |",
    "| --- | --- | --- | --- | --- | --- |",
]
for f in findings:
    lines.append(f"| {f['id']} | DOC | finding | low | open | {f['title']} |")
lines += [
    "",
    "All five have `releaseBlocking: false` as individual defects. That is not release acceptance: suite 3 remains experimental, public interoperability evidence is pending, and utility/release verification is outside this review.",
    "",
    "## Review evidence",
    "",
    "### Scope and methodology",
    "",
    "The user requested a maximally complete and objective audit of **README and the specification appendices only**, explicitly excluding utilities. All 761 README lines and all 2116 supplement lines were read, including historical Part II. CHANGELOG, vectors as executable fixtures, implementation repositories, scripts, dependencies, builds and UI execution are excluded. Linked file existence was checked without turning linked materials into additional audit targets.",
    "",
    "The review followed the wallet-full-audit skill and the shared security context, FULL_AUDIT_GUIDE, AUDIT_STANDARD, AUDIT_TEMPLATE and JSON schema. All 32 CHECK IDs are accounted for below. Relevant tasks are applied at the specification level; application-only tasks are not applicable to these text artifacts. This is a complete execution of the requested document scope, **not a fully executed end-to-end project audit**. The guide's utility/build/browser procedure was not run under a misleading full-audit label.",
    "",
    "Three parallel reviewers supplied separate analyses. The coordinator read the full corpus, reviewed their evidence, checked primary sources and consolidated only reproducible defects. Public synthetic data alone was used. Newly written audit harnesses evaluate equations, Unicode and links; they neither import MHFE nor replace real output-vector verification. Previous findings and the pasted eight-item list served as regression checklists, not as the boundaries of the review.",
    "",
    "Primary source interpretations and retrieval limitations are in " + link("AUD-004-evidence/primary-sources.md") + ". Detailed workpapers are " + ", ".join(link("AUD-004-evidence/" + p) for p in ["agent-protocol-review.md", "agent-appendix-review.md", "agent-editorial-review.md"]) + ".",
    "",
    "### Coverage ledger",
    "",
    "The outcomes below describe the listed **document-level method**. A passed normative review is not a passed runtime enforcement test. `Not-applicable` rows do not imply that the excluded utilities are absent or safe.",
    "",
    "| Check ID | Category / logical group | Tool / build scope | Method | Outcome | Evidence / gap reason |",
    "| --- | --- | --- | --- | --- | --- |",
]
for c in coverage:
    evidence = link(c["evidence"]) if "evidence" in c else c["reason"]
    lines.append(f"| {c['checkId']} | {c['category']} / {c['logicalGroup']} | {c['scope']} | {c['method']} | {c['outcome']} | {evidence} |")
counts = collections.Counter(c["outcome"] for c in coverage)
lines += [
    "",
    f"Ledger totals: {counts['passed']} passed, {counts['failed']} failed due to the tracked documentation findings, {counts['not-applicable']} not applicable to the authorized text scope. These are checklist outcomes, not test-case totals.",
    "",
    "### Checks",
    "",
    "| Check / command | Outcome | Counts / environment | Evidence |",
    "| --- | --- | --- | --- |",
]
descriptions = {
    "environment": "Named workspace toolchain; jsonschema available",
    "format-baseline": "Both scoped Markdown documents conform to local Prettier",
    "diff-check": "No whitespace errors in the scoped baseline diff",
    "document-links": "48 local links; 44 consecutive bibliography entries; 37/33 distinct citations in README/supplement",
    "protocol-algebra": "500 synthetic round trips; 6000 omitted-round comparisons; 22 MEM levels; no Argon2",
    "protocol-unicode": "1112064 scalar values; expansion/contraction and character-domain boundaries; Unicode 17.0",
    "appendix-analytical": "Cost/PIM/cycle formulas; 12000 toy equalities; rejecting-cycle counterexample; no Argon2",
}
for c in command_checks:
    lines.append(f"| `{c['command']}` | {c['outcome']}; exit {c['exitCode']} | {descriptions.get(c['name'], 'See exact retained output')} | {link(c['evidence'])}; {link('AUD-004-evidence/' + c['name'] + '.command.json')} |")
lines += [
    "",
    "All listed executable checks passed. Toy exercises overlap and are deliberately not summed. A passing analytical probe proves only its finite assertions or arithmetic, not actual MHFE outputs, proof assumptions or security. Final report/schema/link/hash checks are recorded separately in report-validation.json and the final command sidecars.",
    "",
    "Initial reconnaissance used an extensionless SECURITY_AUDIT path that did not exist; the actual SECURITY_AUDIT.md and procedure files were then read. Some login-shell reads emitted `Failed to create stream fd: Operation not permitted` while still returning the requested data; later commands used non-login shells. These are retained environment/discovery notes, not application failures. No failed cryptographic check was hidden or converted into a pass, and no assertion or vector was weakened.",
    "",
    "### Technical conclusions by area",
    "",
    "| Area | Conclusion and limits |",
    "| --- | --- |",
]
for title, text in technical:
    lines.append(f"| {title} | {text} |")
lines += ["", "### Findings", ""]
for f in findings:
    lines += [f"#### {f['id']} — Low — {f['title']}", "", "- **Category:** DOC.", "- **Severity:** low.", "- **Status:** open.", f"- **Release blocking:** false. {f['releaseBlockingReason']}", "- **Affected files and builds:** " + "; ".join(f["affectedFiles"]) + "; documentation only."]
    for label, key in [("Reproduction", "reproduction"), ("Expected behavior", "expected"), ("Observed behavior", "observed"), ("Impact and prerequisites", "impact"), ("Recommended fix", "recommendedFix"), ("Required verification", "requiredVerification")]:
        lines.append(f"- **{label}:** {f[key]}")
    lines += ["- **Evidence:** " + "; ".join(link(e) for e in f["evidence"]) + ".", ""]
lines += ["### Remediation and follow-up", "", "This is a review-only baseline. All proposed changes await a separate remediation request; source was preserved. No owner risk acceptance is inferred.", "", "| Finding ID | Status | Fix commit | Verification commit | Evidence |", "| --- | --- | --- | --- | --- |"]
for f in findings:
    lines.append(f"| {f['id']} | open | Not fixed | Not run | {link(f['evidence'][0])} |")
lines += ["", "#### Earlier findings and pasted corrections", "", "These are current-text dispositions; they do not rewrite historical snapshots or claim fresh utility verification.", "", "| Original finding ID | Current-text result |", "| --- | --- |"]
for i, d in prior:
    lines.append(f"| {i} | {d} |")
lines += ["", "All **seven applicable** items in the pasted eight-item editorial list are resolved: unified attack table, correctly ordered precomputation warning, contiguous vector requirements, removed numerical repetition, combined round-count caveat, removed empty redirect section, and separate PIM/MEM scaling explanation. Item 7 concerns CHANGELOG and was not checked. The detailed location-by-location table is in the editorial workpaper. AUD-002 is reserved but not retained locally, so this review cannot claim complete reconciliation with its unpublished contents.", "", "### Informational observations and recommendations", "", "The following are proposed improvements and research/readiness priorities, not additional confirmed vulnerabilities. They intentionally have no finding IDs.", ""]
for item in recommendations:
    lines += [f"#### {item['title']}", "", f"**Priority:** {item['priority']}. **Relevant text:** {item['locations']}.", "", item["text"], ""]
lines += ["### Assessment and limitations", "", "The revised text reads logically and already handles several difficult distinctions well: a verifier versus authentication, external wallet checks versus syntactic validity, secret intermediate salts versus public end salts, round-trip checks versus independent vectors, and conjectures versus theorems. Its five tracked defects are localized documentation problems. Two concern historical mathematical wording and do not alter current suite 3.", "", "The principal unresolved protocol risk is the lack of a construction-specific security proof or independent specialist review; the principal interoperability readiness gap is the unpublished current vector corpus. These are honestly disclosed design/readiness limits, not findings fabricated merely because the scheme is experimental. The cost model is useful as an illustration but should not become a measured guarantee. No production release acceptance is granted by this document-only audit.", ""]
lines += [f"- {item}" for item in limitations]
lines += ["", "#### Procedure fingerprints", "", "The exact procedure/instruction bytes used are pinned below; links and command evidence are validated in the companion record.", "", "| Procedure or instruction | SHA-256 |", "| --- | --- |"]
for path, digest in PROCEDURES.items():
    lines.append(f"| `{path}` | `{digest}` |")
lines += ["", "The final integrity manifest covers retained evidence and the paired reports/index, excluding itself and final validation artifacts to avoid self-referential hashes; the exact manifest scope is recorded during final validation.", ""]
report_md.write_text("\n".join(lines))
print(f"Wrote {report_md.name} and {report_json.name}: {len(findings)} low findings; {len(coverage)} checklist rows.")
