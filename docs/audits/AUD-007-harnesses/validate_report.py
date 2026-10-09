"""Validate the published AUD-007 record and its final source bindings."""

import hashlib
import json
import re
import subprocess
from pathlib import Path

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[3]
REPORT = ROOT / "docs/audits/audit-07-2026-10-09.json"
MARKDOWN = ROOT / "docs/audits/audit-07-2026-10-09.md"
SCHEMA = ROOT.parent / "multi-chain-wallet-tools/docs/audit-report.schema.json"


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    report = json.loads(REPORT.read_text(), object_pairs_hook=unique_object)
    Draft202012Validator(json.loads(SCHEMA.read_text())).validate(report)
    assert sha256(SCHEMA) == report["procedureHashes"]["docs/audit-report.schema.json"]
    text = MARKDOWN.read_text()
    assert report["auditId"] == "AUD-007" and report["auditNumber"] == 7
    assert report["date"] in text and report["snapshot"]["commit"] in text
    ids = [finding["id"] for finding in report["findings"]]
    assert len(ids) == len(set(ids)) == 3
    assert set(ids) == {item["id"] for item in report["remediation"]}
    table_rows = [[cell.strip() for cell in line.strip().strip("|").split("|")]
                  for line in text.splitlines() if line.startswith("|")]
    for finding in report["findings"]:
        assert f'#### {finding["id"]} — {finding["severity"].capitalize()}' in text
        assert any(row[:2] == [finding["id"], finding["status"]] for row in table_rows)
    coverage = [item["id"] for item in report["coverage"]]
    guide = ROOT.parent / "multi-chain-wallet-tools/docs/FULL_AUDIT_GUIDE.md"
    expected = set(re.findall(r"CHECK-(?:SEC|FUN|API|BLD|UI|ARC|DOC)-\d{3}", guide.read_text()))
    assert len(coverage) == len(set(coverage)) == 32 and set(coverage) == expected
    assert len(report["reviewerPhases"]) == 11
    final = report["finalSnapshot"]
    for name, digest in final["sourceFiles"].items():
        assert sha256(ROOT / name) == digest, f"Source changed: {name}"
    manifest = "".join(name + "\0" + final["sourceFiles"][name] + "\n"
                       for name in sorted(final["sourceFiles"]))
    assert hashlib.sha256(manifest.encode()).hexdigest() == final["sourceFingerprint"]
    for name, digest in final["implementationFiles"].items():
        assert sha256(ROOT.parent / "mhfe" / name) == digest, f"Implementation changed: {name}"
    for name, digest in report.get("harnessHashes", {}).items():
        assert sha256(ROOT / name) == digest, f"Harness changed: {name}"
    assert subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                   text=True).strip() == final["commit"]
    published = [REPORT, MARKDOWN, Path(__file__).with_name("README.md")]
    for path in published:
        content = path.read_text()
        assert not re.search(r"/home/(?!user(?:/|\b))[^/\s]+", content), "Personal home path"
        assert not re.search(r"[\u0400-\u04ff]", content), "Non-English report text"
    print(json.dumps({"outcome": "passed", "findings": len(ids),
                      "coverageTasks": len(coverage), "reviewers": 11,
                      "finalSourceFingerprint": final["sourceFingerprint"]}))


if __name__ == "__main__":
    main()
