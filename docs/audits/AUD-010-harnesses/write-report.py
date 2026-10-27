"""Assemble AUD-010 from retained local review/evidence files after consolidation.

This writes audit records only, never protocol or implementation files. The
local evidence bundle is required; running it is not another audit execution.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
AUDIT = 'AUD-010'
EVIDENCE = ROOT / f'docs/audits/{AUDIT}-evidence'
DATE = '2026-10-27'
BASE = ROOT / f'docs/audits/{AUDIT}-{DATE}'


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def private_paths(value):
    if isinstance(value, str):
        return value.replace(str(Path.home()), '/home/user')
    if isinstance(value, list):
        return [private_paths(item) for item in value]
    if isinstance(value, dict):
        return {private_paths(key): private_paths(item) for key, item in value.items()}
    return value


def findings():
    result = []
    ids = ('API001', 'API002', 'UI001', 'FUN001')
    for original, suffix in zip(read('python-contracts.json')['findings'], ids):
        result.append({
            'id': f'{AUDIT}-{suffix}', 'category': original['category'], 'kind': 'finding',
            'title': original['title'], 'severity': original['severity'], 'status': 'open',
            'releaseBlocking': original['releaseBlocking'],
            'releaseBlockingReason': original['releaseBlockingReason'],
            'affectedFiles': original['locations'], 'evidence': original['evidence'],
            'reproduction': original['minimalPublicReproduction'],
            'expected': original['expected'], 'observed': original['observed'],
            'impact': original['impact'], 'recommendedFix': original['fixProposal'],
            'requiredVerification': original['verification'],
        })
    original = read('release-skeptic.json')['findings'][0]
    result.append({**{k: original[k] for k in (
        'category', 'title', 'severity', 'status', 'releaseBlocking', 'releaseBlockingReason',
        'reproduction', 'expected', 'observed', 'impact', 'recommendedFix', 'requiredVerification')},
        'id': f'{AUDIT}-DOC001', 'kind': 'finding', 'affectedFiles': original['locations'],
        'evidence': ['release-skeptic.json', 'remote-release-state.json'],
    })
    result.append({
        'id': f'{AUDIT}-DOC002', 'category': 'DOC', 'kind': 'finding',
        'severity': 'low', 'status': 'open', 'releaseBlocking': False,
        'releaseBlockingReason': 'Presentation defect; the underlying changes remain readable.',
        'title': 'Two changelog additions render as inline hyphens inside another item',
        'affectedFiles': [{'file': 'CHANGELOG.md', 'startLine': 30, 'endLine': 41}],
        'reproduction': 'Render the 0.7.0 entry: the optional-profile and independent-script additions follow literal inline "- " text.',
        'expected': 'Distinct additions render as sibling list items, following DOC-01/DOC-02 and CHECK-DOC-001.',
        'observed': 'The text contains "text. - The optional" and "unchanged. - The independent"; Prettier accepts both as prose within the requirement-ID item.',
        'impact': 'The release change list merges three independent additions. No algorithm or requirement is altered.',
        'evidence': ['CHANGELOG.md:30-41', 'format.log'],
        'recommendedFix': 'Put the two additions on separate sibling list items without changing their content.',
        'requiredVerification': 'Render the changelog, inspect list nesting, and rerun formatting/link checks.',
    })
    return result


def ledger():
    items = read('coverage-plan.json')
    outcomes = {
        'SEC-001': ('passed', 'Trace both emergency paths and their documented visible-input/Python-memory limits; no real secrets used.'),
        'SEC-002': ('passed', 'Network-disabled, capability-dropped Docker renderer; secret-bearing CLI has no browser vault or transport.'),
        'SEC-003': ('passed', 'Crypto scripts have no network calls; document resource allowlists and Docker isolation reviewed.'),
        'SEC-004': ('passed', 'All five theorems and supporting proofs manually re-derived/challenged; finite models and public crypto/profile checks. Concrete memory-hardness is not proved.'),
        'SEC-005': ('passed', 'Terminal/read/error paths traced. Immutable Python strings are expressly not guaranteed to be erased; no crash-dump/host-compromise test.'),
        'SEC-006': ('not-applicable', 'No seed-bearing browser application, persistence layer or DOM in this repository. Static PDF HTML is covered by BLD/UI.'),
        'SEC-007': ('failed', 'Out-of-range settings reach the KDF boundary (API002); probes deliberately stop before allocation.'),
        'FUN-001': ('failed', 'Current positive widths and the enumerated encoding/Unicode checks reviewed; unsupported source/stated word counts enter emergency suite 3 (API001).'),
        'FUN-006': ('failed', 'Both default-cost CLI round trips and independent repair arithmetic pass; emergency recovery omits REC-3 and ambiguity metadata (FUN001/UI001).'),
        'API-001': ('passed', 'Actual OpenSSL/cryptography Argon2 calls, lanes, byte widths, work-factor formula and normalization integration checked.'),
        'API-002': ('not-applicable', 'No asynchronous wallet controller/revisions. CLI is synchronous; renderer promise/error control reviewed under BLD.'),
        'API-003': ('passed', 'Public vector/profile JSON, manifests and verifier-record format reviewed; no monetary export or transaction schema exists.'),
        'API-004': ('failed', 'Positive BIP39/encoding interoperability checked; boundary admission omissions remain API001/API002.'),
        'BLD-001': ('passed', 'Tracked PDF manifest/lock/image/action pins, independent hashed Python requirements and package inputs reviewed.'),
        'BLD-002': ('passed', 'All current positive transcripts plus the enumerated and selected fast checks/static review; actual emergency encrypt/decrypt on one public default fixture per suite. Not a fresh complete fast-case or full-cost corpus replay.'),
        'BLD-003': ('failed', 'Hashes/provenance/licenses checked. Fresh pnpm audit reports three version-matched advisories; separately triaged against actual build inputs.'),
        'BLD-004': ('passed', 'Fresh controlled Docker PDF build, 103 regressions and source/output bindings pass. No byte-for-byte reproducibility claim or WASM build.'),
        'BLD-005': ('failed', 'Workflow statically reviewed; current local candidate differs from the old signed tag and advertised release archive (DOC001). No CI dispatch/publication.'),
        'UI-001': ('passed', 'All 130 pages viewed as contact sheets; critical proof/formula pages at full size, strict PDF parsing and all-page text/raster checks.'),
        'UI-002': ('failed', 'Links/destinations and contents pass. CLI omits alternative matching-length notice (UI001).'),
        'UI-003': ('passed', 'Visible-input/output warning and unverified labels reviewed; exact public CLI output checked. No QR/export/browser app exists.'),
        'ARC-001': ('passed', 'Shared Python helpers, independent language boundary and document-converter modules traced; every tracked path classified.'),
        'ARC-002': ('passed', 'Current script/import boundaries and historical/archived exclusions reviewed; no speculative refactor finding.'),
        'ARC-003': ('passed', 'Requirement/profile checker negative controls and bounded independent probes evaluated on actual entry points; table consistency is distinguished from runtime refusal.'),
        'DOC-001': ('failed', 'Current full README/supplement and scope tables reviewed; release-archive claims remain DOC001.'),
        'DOC-002': ('failed', 'Commands, relative links, metadata and licenses checked; malformed changelog list remains DOC002.'),
        'DOC-003': ('passed', 'Nine historical report envelopes checked; original outcomes retained. Completed AUD-010 pair/index/schema/IDs/privacy independently validated.'),
    }
    for item in items:
        suffix = item['checkId'].removeprefix('CHECK-')
        if suffix in outcomes:
            outcome, reason = outcomes[suffix]
        else:
            outcome, reason = item['outcome'], item['reason']
        item.update(outcome=outcome, reason=reason, snapshot='13215935bcdd320539a93e678cec374ba556528f')
        item.pop('expectedEvidence', None)
    return items


def commands():
    result = []
    for path in sorted(EVIDENCE.glob('*.command.json')):
        item = json.loads(path.read_text())
        item['record'] = str(path.relative_to(ROOT))
        result.append(item)
    return result


def report_data():
    snapshot = read('snapshot.json')
    validation = json.loads((ROOT / 'output/documents/verification.json').read_text())
    return private_paths({
        'schemaVersion': 1, 'auditId': AUDIT, 'auditNumber': 10, 'date': DATE,
        'title': 'Specification 0.7.0 pre-release audit: proofs, emergency recovery and PDFs',
        'reviewer': {'name': 'Codex coordinator with five scoped independent AI reviewers',
                     'model': None, 'reasoningEffort': None},
        'completedUtc': datetime.now(timezone.utc).isoformat(),
        'verdict': 'FAIL',
        'verdictReason': 'Two confirmed emergency-input admission defects block release acceptance of the current candidate. The mathematical review found no confirmed defect; upstream dependency advisories and publication alignment remain explicit caveats.',
        'snapshot': {'commit': snapshot['commit'], 'commitComplete': True,
                     'workingTree': 'Tracked baseline clean. Pre-existing untracked interrupted AUD-010 harnesses and docs/drafts. Only audit records/harnesses/index and ignored evidence/build output changed in this audit.',
                     'sourceFingerprint': snapshot['sourceFingerprint']},
        'scope': {
            'trackedFiles': 173, 'completeDocumentRead': ['README.md', 'docs/DESIGN-NOTES.md'],
            'included': ['Suites 3/4 and all optional profiles; every theorem, lemma, corollary and proposition in current supplement',
                         'Normative requirement IDs, public vectors/JSON, independent Python scripts and their dependencies',
                         'PDF converter, workflow/tooling/metadata/licenses, tracked and freshly built PDFs',
                         'Historical audits/harnesses and archived suite 2 classified as retained evidence; no new certification of historical algorithms'],
            'excluded': ['Untracked research drafts and other workspace repositories as full audit targets',
                         'Real funds/secrets, physical coercion plausibility, hardware-wallet/OS/browser compromise, current full Rust implementation audit'],
            'methods': ['Five distinct specialist scopes; coordinator validation and skeptical/completeness follow-ups',
                        'Manual symbolic reasoning plus finite toy-model checks; no formal proof assistant',
                        'Current source execution and bounded boundary probes; retained full-cost replay explicitly separate',
                        'Network-disabled controlled rendering, strict PDF parse, all-page contact review and full-size samples'],
        },
        'procedureHashes': read('procedure-hashes.json'),
        'checks': {'coverage': ledger(), 'commands': commands(),
                   'summary': read('acceptance-summary.json')},
        'findings': findings(), 'observations': [],
        'informationalNotes': read('informational-notes.json'),
        'remediation': [{'id': item['id'], 'status': 'open', 'fixCommit': None,
                         'verificationCommit': None, 'evidence': item['evidence']} for item in findings()],
        'artifacts': {'sourceInputs': validation['inputs'],
                      'freshDocuments': [{'file': item['file'], 'sha256': item['sha256'],
                                           'pages': len(item['pages']), 'mathExpressions': len(item['math'])}
                                          for item in validation['documents']],
                      'trackedDocuments': read('tracked-artifacts.json'),
                      'toolchain': {'hostNode': '26.12.1', 'hostPnpm': '12.5.1', 'python': '3.14.4',
                                    'docker': '29.9.2', 'pdfNode': validation['node'],
                                    'pdfDependencies': validation['dependencies']}},
        'limitations': [
            'No formal proof verification, independent human cryptographer certification, concrete PRP/SPRP proof or proof of Argon2 physical memory/time cost.',
            'Historical complete Argon2 replays bind the current fixture bytes to their historical verifier/environment. New execution covers four default-cost emergency CLI operations, not every current full-cost vector/negative case or extreme work factor.',
            'The passwords command does not execute the separate JavaScript boundary, five settings, six phrase and eight length-detection rows of the suite 3 conformance file. Selected direct boundary/model checks and static review are recorded; not every one of those rows was freshly exercised through the current emergency CLI.',
            'A retained Core test log used a project-copy method in the interrupted attempt. It was not rerun or treated as new in-place implementation verification.',
            'All pages were visually screened at contact-sheet size; only recorded critical samples were inspected at full size. Automated syntax/text/raster checks do not prove mathematical meaning.',
            'Version-matched dependency advisories are recorded with reachability limits. No hostile PDF or denial-of-service exploit was executed.',
            'Git fetch failed on an invalid local Codex checkpoint reference; it was not repaired. Public GitHub tag/main/release metadata was read separately.',
            'Static workflow review and local controlled build do not prove a successful remote CI/release run. No remote CI job was dispatched.',
            'No production fix, vector change, tracked PDF replacement, commit, push, tag, release or publication was performed. Research/novelty recommendations are outside this formal audit record.',
        ],
        'localEvidence': 'docs/audits/AUD-010-evidence/ is local and Git-ignored; logs are not public report assets.',
        'numbering': 'The owner requested completing the interrupted AUD-010 rather than publishing a gap. No prior formal AUD-010 existed. Earlier attempt artifacts and the temporary execution namespace are consolidated here, with original logs unchanged.',
    })


def text(value):
    return value if isinstance(value, str) else json.dumps(value, ensure_ascii=True)


def markdown(data):
    lines = [f"# {AUDIT} — {data['title']}", '', '## Record metadata', '',
             '- **Audit number:** 10.', f'- **Completed (UTC):** {DATE}.',
             '- **Reviewer:** Codex coordinator and five scoped independent AI reviewers; exact model and reasoning effort unknown for every phase.',
             f"- **Reviewed commit:** `{data['snapshot']['commit']}`.",
             f"- **Working tree:** {data['snapshot']['workingTree']}",
             f"- **Source fingerprint:** `{data['snapshot']['sourceFingerprint']}` (173 sorted tracked path/hash/size entries; local snapshot).",
             '- **Verdict: FAIL.** The emergency input-contract findings API001/API002 block acceptance of this candidate. This is a completed audit with open findings, not a release or cryptographic certification.',
             '- **Numbering:** The interrupted attempt and the completed review are consolidated into this single AUD-010 at the owner\'s request; no incomplete record is added to the index.',
             '', '## Finding register', '',
             '| Finding / record ID | Category | Kind | Severity | Recorded status | Release blocking | Title |',
             '| --- | --- | --- | --- | --- | --- | --- |']
    for item in data['findings']:
        lines.append(f"| {item['id']} | {item['category']} | finding | {item['severity']} | open | {str(item['releaseBlocking']).lower()} | {item['title']} |")
    lines += ['', '## Review evidence', '', '### Scope and methodology', '',
              'The full current specification and supplement were read, including their research sections, scope tables and all proof statements and arguments. Separate reviewers covered deniability; A.1–A.5; A.6–A.7; Python/contracts; and PDF/build inputs. Existing reviewers then challenged mathematical transitions, candidate defects, public operations and completeness. The coordinator validated findings, executed checks and reconciled coverage. Every model/effort field remains unknown.',
              '', 'All 173 tracked paths were inventoried and hash-bound. Current code, current protocol documents, corpus metadata and release inputs received their assigned review. Historical audit records and frozen harnesses were checked as retained evidence/provenance, not as current production paths or newly executed old audits. Archived suite 2 is non-normative for current suites. Untracked research drafts are excluded. The per-path and operation ledgers are local evidence.',
              '', 'No confirmed error was found in Theorems 1–5 or their supporting lemmas, corollaries and matching attacks within their stated ideal models. The G/K/W transitions, rejection coupling, adaptive finalization, s_1 factor, fractional credit and constants were manually challenged. This is not formal verification or evidence that concrete primitives satisfy the ideal assumptions. The new recovery-script defects below do not refute those theorems.',
              '', 'Procedure identities:', '', '| Procedure | SHA-256 |', '| --- | --- |']
    lines += [f'| `{path}` | `{digest}` |' for path, digest in data['procedureHashes'].items()]
    lines += ['', '### Coverage ledger', '', '| Check ID | Scope | Outcome | Evidence / gap reason |', '| --- | --- | --- | --- |']
    for item in data['checks']['coverage']:
        lines.append(f"| {item['checkId']} | {item['title']} | {item['outcome']} | {item['reason']} |")
    lines += ['', '### Checks', '', 'The table summarizes commands run from the repository root; brace expressions and upper-case inputs abbreviate separate invocations. Exact commands, UTC timestamps, statuses and log hashes are retained in the JSON companion and **local, Git-ignored evidence** in `docs/audits/AUD-010-evidence/`. Paths in this published record are anonymized. Overlapping groups are not added into one test total.', '',
              '| Check / command | Outcome | Counts / environment |', '| --- | --- | --- |']
    for row in data['checks']['summary']:
        lines.append(f"| {row['command']} | {row['outcome']} | {row['detail']} |")
    lines += ['', 'The initial runtime harness indexed a string as an object and failed before crypto. A corrected run completed suite 3 encryption but stopped at the audit memory-reserve guard; another start also stopped before work. These are retained harness/resource outcomes, not product failures. The remaining operations resumed without repeating the successful encryption. Exact retained stdout was checked against full expected lines after strengthening the harness oracle.',
              '', 'Retained full-cost corpus records match all current fixture hashes: 17 suite 3 transcripts plus seven recovery cases, and ten suite 4 transcripts plus four recovery cases. They used historical Python 3.14.4, cryptography 46.0.5/OpenSSL 3.5.5 and Unicode 17. The actual historical verifier hashes and changed current functions/globals were compared. Fresh Unicode tests and recorded-key replays support compatibility; they do not constitute a full replay on cryptography 50.0.2. The original Core-copy harness is retained locally and was not run.',
              '', '### PDF artifacts', '', '| Artifact | Pages | SHA-256 |', '| --- | --- | --- |']
    for item in data['artifacts']['trackedDocuments'] + data['artifacts']['freshDocuments']:
        lines.append(f"| `{item['file']}` | {item['pages']} | `{item['sha256']}` |")
    lines += ['', 'Both tracked PDFs embed the current Markdown hashes and strictly parse with pypdf 6.10.0. Their extracted body text equals that of the fresh outputs after normalizing only the build-revision header and whitespace. Fresh PDFs are in ignored output; tracked copies were not replaced. The build passed 103 regression cases and all-page text/raster/layout checks for 167 specification and 2,541 supplement expressions. It uses pinned Node 26.10.0/Chromium 156 in Docker; the host Node is 26.12.1. This is a controlled build, not a byte-for-byte reproducibility claim.',
              '', 'All 34 specification and 96 supplement pages were visually screened in contact sheets. Full-size samples include specification page 8 and supplement pages 74, 81, 87, 89 and 93, plus tracked supplement page 74. No clipping or broken formula/table/content pagination was found in these views. The specification contents fits page 3; the larger supplement contents starts on fresh page 2 and continues on page 3. Contact sheets do not resolve every small glyph.',
              '', '### Findings', '']
    for item in data['findings']:
        lines += [f"#### {item['id']} — {item['severity'].capitalize()} — {item['title']}", '']
        fields = [('Category', item['category']), ('Severity', item['severity']), ('Status', 'open'),
                  ('Release blocking', f"{str(item['releaseBlocking']).lower()}; {item['releaseBlockingReason']}"),
                  ('Affected files', item['affectedFiles']), ('Reproduction', item['reproduction']),
                  ('Expected behavior', item['expected']), ('Observed behavior', item['observed']),
                  ('Impact', item['impact']), ('Evidence', item['evidence']),
                  ('Recommended fix', item['recommendedFix']), ('Required verification', item['requiredVerification'])]
        lines += [f'- **{name}:** {text(value)}' for name, value in fields]
        lines.append('')
    lines += ['### Remediation and follow-up', '', '| Finding ID | Status | Fix commit | Verification commit | Evidence |', '| --- | --- | --- | --- | --- |']
    lines += [f"| {item['id']} | open | Not fixed | Not run | Original reproduction retained locally |" for item in data['findings']]
    lines += ['', '### Informational observations and recommendations', '']
    for item in data['informationalNotes']:
        lines += [text(item), '']
    lines += ['### Assessment and limitations', '']
    lines += [f'- {item}' for item in data['limitations']]
    lines += ['', 'The two Medium admission findings should be resolved before shipping the emergency path with its current conformance claims. Low findings do not independently block the release. The intended publication source/version must be settled separately: an existing signed tag does not identify these local additions. Research claims and new-theorem priorities are deliberately outside this audit record.', '']
    return '\n'.join(lines)


def main():
    data = report_data()
    BASE.with_suffix('.json').write_text(json.dumps(data, indent=2) + '\n')
    BASE.with_suffix('.md').write_text(markdown(data))
    print(f'{BASE.name}: {len(data["findings"])} findings; {len(data["checks"]["coverage"])} check IDs')


if __name__ == '__main__':
    main()
