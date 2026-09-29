"""Validate paired audit records, retained evidence and the remediation snapshot."""

import datetime
import hashlib
import json
from pathlib import Path
import re

import jsonschema


EVIDENCE = Path(__file__).resolve().parents[1]
AUDITS = EVIDENCE.parent
ROOT = EVIDENCE.parents[2]
WORKSPACE = ROOT.parent


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


report = read_json(AUDITS / "audit-04-2026-09-30.json")
markdown = (AUDITS / "audit-04-2026-09-30.md").read_text()
schema = read_json(WORKSPACE / "multi-chain-wallet-tools/docs/audit-report.schema.json")
jsonschema.Draft202012Validator(schema).validate(report)
ids = [f["id"] for f in report["findings"]]
assert len(ids) == len(set(ids)) == 5
assert all(f["severity"] == "low" and f["status"] == "open" for f in report["findings"])
for f in report["findings"]:
    assert f"#### {f['id']} — Low — {f['title']}" in markdown
    assert f["id"].split("-")[2].startswith(f["category"])
    for path in f["evidence"]:
        if not path.startswith("https://"):
            assert (AUDITS / path).exists(), path
assert {r["id"] for r in report["remediation"]} == set(ids)
assert all(r["status"] == "verified" for r in report["remediation"])
guide = (WORKSPACE / "multi-chain-wallet-tools/docs/FULL_AUDIT_GUIDE.md").read_text()
expected_checks = set(re.findall(r"^### (CHECK-[A-Z]+-\d+)", guide, re.M))
actual_checks = [r["checkId"] for r in report["coverageLedger"]]
assert len(actual_checks) == len(set(actual_checks)) == 32
assert set(actual_checks) == expected_checks
assert all(check in markdown for check in actual_checks)

command_count = 0
for path in EVIDENCE.glob("*.command.json"):
    command = read_json(path)
    log = EVIDENCE / command["log"]
    assert hashlib.sha256(log.read_bytes()).hexdigest() == command["logSha256"], path
    assert command["startedAt"] <= command["endedAt"], path
    command_count += 1
for name, expected in read_json(EVIDENCE / "procedure-hashes.json").items():
    path = Path(name) if name.startswith("/") else WORKSPACE / name
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, name
remediation = read_json(EVIDENCE / "remediation-snapshot.json")
for path, expected in remediation["sourceHashes"].items():
    assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path
assert report["remediationSnapshot"]["sourceFingerprint"] == remediation["sourceFingerprint"]

links = 0
pending_control_files = {EVIDENCE / "SHA256SUMS", EVIDENCE / "report-validation.json"}
for target in re.findall(r"(?<!!)\[[^\]\n]+\]\(([^\s)]+)\)", markdown):
    if target.startswith(("http://", "https://", "#")):
        continue
    path = (AUDITS / target.split("#", 1)[0]).resolve()
    assert path.exists() or path in pending_control_files, target
    links += 1
assert "audit-04-2026-09-30.md" in (AUDITS / "README.md").read_text()
assert "audit-04-2026-09-30.json" in (AUDITS / "README.md").read_text()
result = {
    "auditId": "AUD-004",
    "validatedAt": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "schemaValid": True,
    "duplicateKeys": False,
    "uniqueFindingIds": len(ids),
    "baselineFindings": {"low": 5, "status": "open at original snapshot"},
    "remediation": {"verified": 5, "snapshot": remediation["sourceFingerprint"]},
    "coverageChecks": 32,
    "pairedIdsTitlesAndSeveritiesAgree": True,
    "retainedCommandLogsVerified": command_count,
    "reportLocalLinksChecked": links,
    "procedureHashesVerified": True,
    "currentSourceHashesVerified": True,
    "indexUpdated": True,
    "hashManifest": "Final integrity command generates SHA256SUMS after this record and its command log are complete; see final-integrity.log.",
    "limitations": "This validates audit artifacts, not MHFE implementation behavior, cryptographic security or the truth of every proof assumption.",
}
(EVIDENCE / "report-validation.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
