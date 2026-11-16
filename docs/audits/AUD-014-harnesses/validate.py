#!/usr/bin/env python3
"""Validate report parity, retained evidence, frozen inputs, and the actual proof-check results."""

import collections
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
    evidence = audits / "AUD-014-evidence"
    read_json = runpy.run_path(str(audits / "AUD-011-harnesses/validate.py"))["read_json"]
    path = audits / "AUD-014-2026-11-13.json"
    data, text = read_json(path), path.with_suffix(".md").read_text()
    schema = audits / "AUD-011-evidence/procedure/audit-report.schema.json"
    jsonschema.Draft202012Validator(read_json(schema)).validate(data)
    findings = data["findings"]
    ids = [row["id"] for row in findings]
    assert ids == ["AUD-014-BLD001", "AUD-014-DOC001", "AUD-014-DOC002"]
    assert set(re.findall(r"AUD-014-(?:SEC|FUN|API|BLD|DOC|UI|ARC)\d{3,}", text)) == set(ids)
    for row in findings:
        assert f"{row['id']} — {row['severity'].capitalize()} — {row['title']}" in text
        assert row["status"] == "open"
    assert [row["releaseBlocking"] for row in findings] == [True, False, False]
    assert {row["id"] for row in data["remediation"]} == set(ids)
    for value in [text, path.read_text(), (here / "README.md").read_text()]:
        assert not re.search(r"/home/(?!user/)[^/]+/|[А-Яа-яЁё]", value)
        # No time zone name: the records keep times in UTC.
        assert not re.search(r"\b(?:Africa|America|Antarctica|Asia|Atlantic|Australia|Europe|Indian|Pacific)/[A-Z]", value)
    for name, digest in data["procedureHashes"].items():
        assert sha(schema.parent / name) == digest, name
    snapshot = read_json(evidence / "snapshot.json")
    assert snapshot["inputFingerprint"] == data["snapshot"]["sourceFingerprint"]
    for row in snapshot["files"]:
        assert sha(workspace / row["path"]) == row["sha256"], row["path"]
    context = read_json(evidence / "model-context.json")
    for row in context["files"]:
        assert sha(workspace / row["path"]) == row["sha256"], row["path"]
    graph = read_json(evidence / "module-graph.json")
    compilation = read_json(evidence / "compile-summary.json")
    assert len(compilation) == len(graph["order"]) == 28
    assert {row["module"] for row in compilation} == set(graph["order"])
    assert all(row["exitCode"] == 0 for row in compilation)
    for name in graph["order"]:
        prefix = "compile-resume-" if name == "MhfeCore.Proofs.Cipher" else "compile-"
        assert read_json(evidence / (prefix + name + ".command.json"))["exitCode"] == 0
    kernel = read_json(evidence / "kernel-summary.json")
    assert kernel["requested"] == kernel["observed"] == graph["order"]
    assert kernel["exitCode"] == 0
    inv = read_json(evidence / "axiom-inventory.json")
    assert len(inv["roots"]) == 2539 and len(inv["theorems"]) == 1416
    assert inv["localAxioms"] == []
    assert set(inv["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    actual = {row["name"]: row["axioms"] for row in inv["theoremAxioms"]}
    named = data["checks"]["inventory"]["namedTheorems"]
    assert len(named) == len({row["name"] for row in named}) == 135
    for row in named:
        assert actual[row["name"]] == row["axioms"]
    counts = collections.Counter(tuple(row["axioms"]) for row in named)
    assert counts == {("propext", "Classical.choice", "Quot.sound"): 113,
                      ("propext", "Quot.sound"): 14, ("propext",): 8}
    controls = read_json(evidence / "control-summary.json")
    assert len(controls) == 3
    assert all(row["exitCode"] == 1 and row["gateRejected"] and row["markerFound"] for row in controls)
    for name in ["aeneas-result.json", "fresh-aeneas-result.json"]:
        result = read_json(evidence / name)
        assert result["exitCode"] == 0
        assert all(row["originalSha256"] == row["generatedSha256"] for row in result["files"])
    assert read_json(evidence / "charon-result.json")["hasErrors"] is False
    probe = read_json(evidence / "pipeline-probe.json")
    assert probe["translatorExit"] == 7 and probe["wrapperExit"] == 0
    assert probe["diagnosticSeen"] and probe["downstreamCodeCreated"]
    assert sha(evidence / "pipeline-probe-inner.log") == probe["rawLogSha256"]
    provenance = read_json(evidence / "provenance-result.json")
    assert provenance["fullCodeByteIdentity"] and provenance["symlinkEntries"] == 21
    assert provenance["kinds"] == {"E": 156, "T": 10, "R": 8}
    for name in ["contract-witnesses", "lake-build", "regenerate-charon", "regenerate-aeneas",
                 "regenerate-fresh-aeneas", "axiom-inventory", "kernel-exact"]:
        assert read_json(evidence / (name + ".command.json"))["exitCode"] == 0
    command_count = 0
    for command_path in evidence.glob("*.command.json"):
        record = read_json(command_path)
        log = command_path.with_name(command_path.name.replace(".command.json", ".log"))
        assert sha(log) == record["logSha256"], command_path
        assert all(record[key].endswith("+00:00") for key in ["startedUtc", "endedUtc"])
        command_count += 1
    tasks = data["checks"]["applicability"]
    assert len(tasks) == len({row["id"] for row in tasks}) == 32
    assert {row["id"] for row in tasks} == set(re.findall(
        r"^### (CHECK-[A-Z]+-\d+)", (schema.parent / "FULL_AUDIT_GUIDE.md").read_text(), re.M))
    for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", text):
        if not target.startswith(("https://", "http://", "#")):
            assert (audits / target.split("#", 1)[0]).exists(), target
    final = data.get("independentFinalReview")
    if final:
        assert final["recordAddedAfterReview"] and final["reviewedDiffSha256"]
        assert "Pending independent review" not in text
    result = {"schema": "passed", "privacy": "passed", "findings": ids,
              "frozenInputsUnchanged": len(snapshot["files"]), "importedModelSourcesUnchanged": len(context["files"]),
              "activeModules": 28, "kernelModules": 28, "namedTheorems": 135,
              "inventoryDeclarations": 2539, "inventoryTheorems": 1416,
              "negativeControlsRejected": 3, "canonicalProcedureIds": 32,
              "commandLogHashes": command_count, "independentFinalReviewRecorded": bool(final),
              "markdownSha256": sha(path.with_suffix(".md")), "jsonSha256": sha(path)}
    (evidence / "report-validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
