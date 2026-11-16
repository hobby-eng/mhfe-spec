#!/usr/bin/env python3
"""Validate the AUD-011 report pair and retained local evidence without modifying sources."""

import hashlib
import json
from pathlib import Path
import re

import jsonschema


def no_duplicates(pairs):
    """Reject duplicate JSON keys instead of allowing silent overwrite."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    """Read strict JSON from one retained file."""
    return json.loads(path.read_text(), object_pairs_hook=no_duplicates)


def main():
    """Fail on report, privacy, hash, source identity or evidence inconsistencies."""
    here = Path(__file__).resolve().parent
    audits = here.parent
    evidence = audits / "AUD-011-evidence"
    report = next(audits.glob("AUD-011-*.json"))
    data = read_json(report)
    md = report.with_suffix(".md").read_text()
    jsonschema.Draft202012Validator(
        read_json(evidence / "procedure/audit-report.schema.json")
    ).validate(data)
    ids = [item["id"] for item in data["findings"]]
    assert len(ids) == len(set(ids))
    assert set(re.findall(r"AUD-011-(?:SEC|FUN|API|BLD|DOC|UI|ARC)\d{3,}", md)) == set(ids)
    for item in data["findings"]:
        assert f"{item['id']} — {item['severity'].capitalize()} — {item['title']}" in md
        assert item["status"] == "open"
    assert len(data["checks"]["strictCompiles"]) == 18
    assert all(item["exitCode"] == 0 for item in data["checks"]["strictCompiles"])
    for text in [md, report.read_text(), (here / "README.md").read_text()]:
        assert not re.search(r"/home/(?!user/)[^/]+/", text)
        assert not re.search(r"[А-Яа-яЁё]", text)
    checked_logs = 0
    for record in evidence.rglob("*.command.json"):
        command = read_json(record)
        log = record.with_name(record.name.replace(".command.json", ".log"))
        assert hashlib.sha256(log.read_bytes()).hexdigest() == command["logSha256"]
        checked_logs += 1
    workspace = here.parents[3]
    snapshot = read_json(evidence / "snapshot.json")
    for item in snapshot["files"]:
        assert hashlib.sha256((workspace / item["path"]).read_bytes()).hexdigest() == item["sha256"]
    for target in re.findall(r"\[[^\]]*\]\(([^)]+)\)", md):
        if target.startswith(("https://", "http://", "#")):
            continue
        assert (audits / target.split("#", 1)[0]).exists(), target
    lengths = {path.name: len(path.read_text().splitlines()) for path in
               (workspace / "tmp/easycrypt-mhfe-2026-11-09/src").glob("*.ec")}
    for name, line in re.findall(r"([A-Za-z0-9]+\.ec):(\d+)", md):
        if name in lengths:
            assert 0 < int(line) <= lengths[name], (name, line)
    result = {"schema": "passed", "duplicateKeys": "none", "findingIds": ids,
              "privacy": "passed", "commandLogsChecked": checked_logs,
              "sourceUnchanged": True, "sourceLineReferences": "in bounds",
              "reportSha256": hashlib.sha256(report.with_suffix('.md').read_bytes()).hexdigest(),
              "jsonSha256": hashlib.sha256(report.read_bytes()).hexdigest()}
    (evidence / "report-validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
