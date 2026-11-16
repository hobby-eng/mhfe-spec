#!/usr/bin/env python3
"""Validate the Lean report pair, fresh artifacts, privacy and original command evidence."""

import hashlib
import json
from pathlib import Path
import re
import runpy

import jsonschema


def main():
    """Reject mismatched snapshots, statuses, finding IDs, logs or source references."""
    here = Path(__file__).resolve().parent
    audits, workspace = here.parent, here.parents[3]
    evidence = audits / "AUD-012-evidence"
    shared = runpy.run_path(str(audits / "AUD-011-harnesses/validate.py"))
    read = shared["read_json"]
    report = next(audits.glob("AUD-012-*.json"))
    data, markdown = read(report), report.with_suffix(".md").read_text()
    schema = read(audits / "AUD-011-evidence/procedure/audit-report.schema.json")
    jsonschema.Draft202012Validator(schema).validate(data)
    ids = [item["id"] for item in data["findings"]]
    assert len(ids) == len(set(ids)) == 4
    assert set(re.findall(r"AUD-012-(?:SEC|FUN|API|BLD|DOC|UI|ARC)\d{3,}", markdown)) == set(ids)
    for item in data["findings"]:
        assert f"{item['id']} — {item['severity'].capitalize()} — {item['title']}" in markdown
        assert item["status"] == "open"
    source, kernel = data["checks"]["compile"], data["checks"]["kernel"]
    assert len(source) == len(kernel) == 40
    assert {item["module"] for item in source} == {item["module"] for item in kernel}
    assert all(item["exitCode"] == 0 for item in source + kernel)
    for text in [markdown, report.read_text(), (here / "README.md").read_text()]:
        assert not re.search(r"/home/(?!user/)[^/]+/", text)
        assert not re.search(r"[А-Яа-яЁё]", text)
    count = 0
    for path in evidence.glob("*.command.json"):
        record = read(path)
        log = path.with_name(path.name.replace(".command.json", ".log"))
        assert hashlib.sha256(log.read_bytes()).hexdigest() == record["logSha256"]
        count += 1
    snapshot = read(evidence / "snapshot.json")
    lengths = {}
    for item in snapshot["files"]:
        path = workspace / item["path"]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == item["sha256"]
        if path.suffix == ".lean":
            lengths[path.name] = item["lines"]
    for filename, line in re.findall(r"([A-Za-z0-9]+\.lean):(\d+)", markdown):
        if filename in lengths:
            assert 0 < int(line) <= lengths[filename], (filename, line, lengths[filename])
    for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", markdown):
        if not target.startswith(("http://", "https://", "#")):
            assert (audits / target.split("#", 1)[0]).exists(), target
    inventory = read(evidence / "checkpoint-inventory.json")
    assert len(inventory["roots"]) == 6036 and inventory["theorems"] == 3888
    assert not inventory["local_axioms"]
    assert set(inventory["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    artifacts = read(evidence / "fresh-artifacts.json")["files"]
    assert len(artifacts) == 40
    for item in artifacts:
        digest = hashlib.sha256()
        with (evidence / item["path"]).open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
        assert digest.hexdigest() == item["sha256"], item["path"]
    result = {"schema": "passed", "privacy": "passed", "sourceUnchanged": True,
              "findingIds": ids, "moduleCounts": [40, 40], "commandLogHashes": count,
              "sourceLineReferences": "in bounds", "freshArtifactsUnchanged": len(artifacts),
              "reportSha256": hashlib.sha256(report.with_suffix('.md').read_bytes()).hexdigest(),
              "jsonSha256": hashlib.sha256(report.read_bytes()).hexdigest()}
    (evidence / "report-validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
