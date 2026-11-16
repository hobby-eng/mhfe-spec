#!/usr/bin/env python3
"""Validate the paired trial-count report against retained proof and source evidence."""

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
    evidence = audits / "AUD-016-evidence"
    read = runpy.run_path(str(audits / "AUD-011-harnesses/validate.py"))["read_json"]
    path = audits / "AUD-016-2026-11-14.json"
    data, text = read(path), path.with_suffix(".md").read_text()
    procedure = audits / "AUD-011-evidence/procedure"
    jsonschema.Draft202012Validator(read(procedure / "audit-report.schema.json")).validate(data)
    for name, digest in data["procedureHashes"].items():
        assert sha(procedure / name) == digest
    ids = [row["id"] for row in data["findings"]]
    assert ids == ["AUD-016-DOC001", "AUD-016-DOC002"]
    assert [row["severity"] for row in data["findings"]] == ["medium", "low"]
    assert [row["releaseBlocking"] for row in data["findings"]] == [True, False]
    assert {row["id"] for row in data["remediation"]} == set(ids)
    for row in data["findings"]:
        assert row["status"] == "open"
        assert f"{row['id']} — {row['severity'].capitalize()} — {row['title']}" in text
    for value in [text, path.read_text(), (here / "README.md").read_text(), (here / "PROPOSED-WORDING.md").read_text()]:
        assert not re.search(r"/home/(?!user/)[^/]+/|[А-Яа-яЁё]", value)
    snapshot = read(evidence / "snapshot.json")
    assert len(snapshot["files"]) == 85 and data["snapshot"]["sourceFingerprint"] == snapshot["fingerprint"]
    for row in snapshot["files"]:
        assert sha(workspace / row["path"]) == row["sha256"], row["path"]
    lean, ec = read(evidence / "lean-summary.json"), read(evidence / "ec-summary.json")
    assert len(lean) == len({r["module"] for r in lean}) == 42 and all(r["exitCode"] == 0 for r in lean)
    assert len(ec) == len({r["file"] for r in ec}) == 23 and all(r["exitCode"] == 0 for r in ec)
    kernel = read(evidence / "kernel-summary.json")
    assert kernel["requested"] == kernel["observed"] and len(kernel["observed"]) == 42 and kernel["exitCode"] == 0
    checkpoint, inventory = read(evidence / "checkpoint-inventory.json"), read(evidence / "audit-inventory.json")
    assert len(checkpoint["roots"]) == 6185 and checkpoint["theorems"] == 4003
    assert len(inventory["roots"]) == 6193 and len(inventory["theoremAxioms"]) == 4004 and not inventory["localAxioms"]
    assert set(inventory["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    controls = read(evidence / "control-summary.json")
    assert len(controls) == 3 and all(r["exitCode"] == 1 and r["markerFound"] and r["gateRejected"] for r in controls)
    ec_controls = (evidence / "ec-checker-selftest.log").read_text()
    assert len(re.findall(r"^ok      ", ec_controls, re.M)) == 4
    assert read(evidence / "ec-checker-selftest.command.json")["exitCode"] == 0
    assert read(evidence / "ec-KnownPair.command.json")["exitCode"] == 1
    assert read(evidence / "ec-resume-KnownPair.command.json")["exitCode"] == 1
    assert read(evidence / "ec-retry2-KnownPair.command.json")["exitCode"] == 0
    for name in ["ec-initial-summary.json", "ec-attempt-2-summary.json"]:
        assert any(r["exitCode"] == 1 for r in read(evidence / name))
    count = 0
    for command in evidence.glob("*.command.json"):
        record = read(command)
        assert sha(command.with_name(command.name.replace(".command.json", ".log"))) == record["logSha256"]
        assert all(record[key].endswith("+00:00") for key in ["startedUtc", "endedUtc"])
        count += 1
    assert len(data["checks"]["applicability"]) == 32
    assert {r["id"] for r in data["checks"]["applicability"]} == set(re.findall(
        r"^### (CHECK-[A-Z]+-\d+)", (procedure / "FULL_AUDIT_GUIDE.md").read_text(), re.M))
    for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
        if not target.startswith(("https://", "http://", "#")):
            assert (audits / target.split("#", 1)[0]).exists(), target
    if "independentFinalReview" in data:
        assert "Pending independent review" not in text
    result = {"schema": "passed", "privacy": "passed", "findings": ids, "frozenInputs": 85,
              "leanModules": 42, "kernelModules": 42, "ecSources": 23,
              "namespaceInventory": [6185, 4003], "sourceOriginInventory": [6193, 4004],
              "leanControlsRejected": 3, "ecControlCases": 4, "knownPairFailuresRetained": 2,
              "commandLogHashes": count, "canonicalCheckIds": 32,
              "independentFinalReviewRecorded": "independentFinalReview" in data,
              "markdownSha256": sha(path.with_suffix(".md")), "jsonSha256": sha(path)}
    (evidence / "report-validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
