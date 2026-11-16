#!/usr/bin/env python3
"""Validate the comparison report, later-state inputs and all retained command/log identities."""

import ast
import hashlib
import json
from pathlib import Path
import re
import runpy

import jsonschema


def main():
    here = Path(__file__).resolve().parent
    audits, workspace = here.parent, here.parents[3]
    evidence = audits / "AUD-013-evidence"
    read = runpy.run_path(str(audits / "AUD-011-harnesses/validate.py"))["read_json"]
    report = next(audits.glob("AUD-013-*.json"))
    data, text = read(report), report.with_suffix(".md").read_text()
    jsonschema.Draft202012Validator(read(audits / "AUD-011-evidence/procedure/audit-report.schema.json")).validate(data)
    ids = [item["id"] for item in data["findings"]]
    assert len(ids) == len(set(ids)) == 2
    assert set(re.findall(r"AUD-013-(?:SEC|FUN|API|BLD|DOC|UI|ARC)\d{3,}", text)) == set(ids)
    for item in data["findings"]:
        assert f"{item['id']} — {item['severity'].capitalize()} — {item['title']}" in text
        assert item["status"] == "open" and not item["releaseBlocking"]
    verified = [item for item in data["remediation"] if item["id"].startswith("AUD-011-")]
    assert len(verified) == 4 and all(item["status"] == "verified" for item in verified)
    for published in [text, report.read_text(), (here / "README.md").read_text()]:
        assert not re.search(r"/home/(?!user/)[^/]+/|[А-Яа-яЁё]", published)
    snapshot = read(evidence / "snapshot.json")
    for name, digest in snapshot["files"].items():
        assert hashlib.sha256((workspace / name).read_bytes()).hexdigest() == digest, name
    command_count = 0
    for path in evidence.rglob("*.command.json"):
        record = read(path)
        log = path.with_name(path.name.replace(".command.json", ".log"))
        assert hashlib.sha256(log.read_bytes()).hexdigest() == record["logSha256"], path.name
        assert all(record[key].endswith("+00:00") for key in ["startedUtc", "endedUtc"])
        command_count += 1
    for label, records in data["checks"]["targetedCurrentEasyCrypt"].items():
        assert len(records) == 4 and all(item["exitCode"] == 0 for item in records), label
    for name in ["current-checker-selftest-corrected", "current-checker-selftest-main"]:
        assert read(evidence / (name + ".command.json"))["exitCode"] == 0
        assert len(re.findall(r"^ok      ", (evidence / (name + ".log")).read_text(), re.M)) == 4
    port = evidence / "port-tools-final"
    assert ast.literal_eval((port / "diff.log").read_text()) == data["checks"]["headerCounts"]
    assert len(read(port / "parser-probes.json")) == 12
    for name in ["snapshot.tsv", "port.tsv", "diff.tsv"]:
        assert (port / name).read_bytes() == (workspace / "tmp/lean-review-2026-11-11/out-v4.35/decls" / name).read_bytes()
    tasks = data["checks"]["applicability"]
    assert len(tasks) == len({item["id"] for item in tasks}) == 32
    assert {item["id"] for item in tasks} == set(re.findall(r"^### (CHECK-[A-Z]+-\d+)",
        (audits / "AUD-011-evidence/procedure/FULL_AUDIT_GUIDE.md").read_text(), re.M))
    for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
        if not target.startswith(("https://", "http://", "#")):
            assert (audits / target.split("#", 1)[0]).exists(), target
    result = {"schema": "passed", "privacy": "passed", "findingIds": ids,
              "priorFindingsVerifiedAtLaterHashes": len(verified), "currentInputsUnchanged": len(snapshot["files"]),
              "targetedProofModulesPerToolchain": 4, "parserProbePairs": 12,
              "canonicalProcedureIds": 32, "commandLogHashes": command_count,
              "reportSha256": hashlib.sha256(report.with_suffix(".md").read_bytes()).hexdigest(),
              "jsonSha256": hashlib.sha256(report.read_bytes()).hexdigest()}
    (evidence / "report-validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
