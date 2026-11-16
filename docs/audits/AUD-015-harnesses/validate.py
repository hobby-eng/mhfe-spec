#!/usr/bin/env python3
"""Validate the focused remediation report and exact retained runtime/source evidence."""

import hashlib
import json
from pathlib import Path
import re
import runpy

import jsonschema


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    audits, workspace = here.parent, here.parents[3]
    evidence = audits / "AUD-015-evidence"
    read = runpy.run_path(str(audits / "AUD-011-harnesses/validate.py"))["read_json"]
    path = audits / "AUD-015-2026-11-13.json"
    data, text = read(path), path.with_suffix(".md").read_text()
    procedure = audits / "AUD-011-evidence/procedure"
    jsonschema.Draft202012Validator(read(procedure / "audit-report.schema.json")).validate(data)
    for name, digest in data["procedureHashes"].items():
        assert sha(procedure / name) == digest
    ids = [row["id"] for row in data["findings"]]
    assert ids == ["AUD-015-BLD001"]
    assert data["findings"][0]["status"] == "open" and not data["findings"][0]["releaseBlocking"]
    assert data["findings"][0]["severity"] == "low"
    verified = [row for row in data["remediation"] if row["status"] == "verified"]
    assert {row["id"] for row in verified} == {"AUD-014-BLD001", "AUD-014-DOC001", "AUD-014-DOC002"}
    for row in data["findings"]:
        assert f"{row['id']} — Low — {row['title']}" in text
    for value in [text, path.read_text(), (here / "README.md").read_text()]:
        assert not re.search(r"/home/(?!user/)[^/]+/|[А-Яа-яЁё]", value)
    snapshot = read(evidence / "snapshot-final.json")
    assert data["snapshot"]["sourceFingerprint"] == snapshot["fingerprint"]
    for row in snapshot["files"]:
        assert sha(workspace / row["path"]) == row["sha256"], row["path"]
    for name in snapshot["deletedSinceInitialCapture"]:
        assert not (workspace / name).exists(), name
    old = read(audits / "AUD-014-evidence/snapshot.json")
    lean = [row for row in old["files"] if row["path"].endswith(".lean")]
    assert len(lean) == 35
    assert all(sha(workspace / row["path"]) == row["sha256"] for row in lean)
    context = read(audits / "AUD-014-evidence/model-context.json")
    assert len(context["files"]) == 22
    assert all(sha(workspace / row["path"]) == row["sha256"] for row in context["files"])
    for name, digest in snapshot["baselineReportHashes"].items():
        assert sha(audits / name) == digest
    for name in ["regression-result.json", "regression-no-file-guard-result.json"]:
        result = read(evidence / name)
        assert result["exitCode"] == 0 and len(result["cases"]) == result["caseCount"] == 13
    real = read(evidence / "real-result.json")
    assert real["exitCode"] == 0 and real["inputUnchangedDuringRun"]
    assert all(row["actual"] == row["expected"] for row in real["files"])
    assert real["inputLLBCSha256"] == sha(workspace / "tmp/code-proof-mhfe-core-2026-11-12/lean/llbc/mhfe_core.llbc")
    failure = read(evidence / "install-error-result.json")
    assert failure["controlExit"] == 0 and failure["exitCode"] == 1
    assert all(failure[key] for key in ["reportedNothingReplaced", "funsChanged", "manifestUnchanged", "renameErrorSeen"])
    assert read(evidence / "lake-build.command.json")["exitCode"] == 0
    count = 0
    for command in evidence.glob("*.command.json"):
        record = read(command)
        assert sha(command.with_name(command.name.replace(".command.json", ".log"))) == record["logSha256"]
        assert all(record[key].endswith("+00:00") for key in ["startedUtc", "endedUtc"])
        count += 1
    assert len(data["checks"]["applicability"]) == 32
    assert {row["id"] for row in data["checks"]["applicability"]} == set(re.findall(
        r"^### (CHECK-[A-Z]+-\d+)", (procedure / "FULL_AUDIT_GUIDE.md").read_text(), re.M))
    for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
        if not target.startswith(("https://", "http://", "#")):
            assert (audits / target.split("#", 1)[0]).exists(), target
    if "independentFinalReview" in data:
        assert "Pending independent review" not in text
    result = {"schema": "passed", "privacy": "passed", "originalFindingsVerified": 3,
              "newLowFindings": 1, "finalInputHashes": len(snapshot["files"]),
              "unchangedLeanSources": 35, "unchangedModelSources": 22, "commandLogHashes": count,
              "regressionCases": 13, "redundantGuardCases": 13, "realOutputsCompared": 5,
              "installFailureWitness": "reproduced", "canonicalCheckIds": 32,
              "independentFinalReviewRecorded": "independentFinalReview" in data,
              "markdownSha256": sha(path.with_suffix(".md")), "jsonSha256": sha(path)}
    (evidence / "report-validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
