"""Reconstruct baseline text in memory and retain only the remediation diff."""

import datetime
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess


EVIDENCE = Path(__file__).resolve().parents[1]
ROOT = EVIDENCE.parents[2]
baseline = json.loads((EVIDENCE / "snapshot.json").read_text())
patch = (EVIDENCE / "reviewed-source.diff").read_text()
sections = re.split(r"(?=^diff --git )", patch, flags=re.M)


def baseline_text(path):
    """Apply the retained safe diff to HEAD bytes without creating another checkout."""
    original = subprocess.check_output(
        ["git", "show", f"{baseline['commit']}:{path}"], cwd=ROOT
    ).decode().splitlines(keepends=True)
    section = next(
        (s for s in sections if s.startswith(f"diff --git a/{path} b/{path}\n")),
        None,
    )
    if section is None:
        return "".join(original)
    result = []
    cursor = 0
    in_hunk = False
    for line in section.splitlines(keepends=True):
        match = re.match(r"@@ -(\d+)(?:,\d+)? \+\d+(?:,\d+)? @@", line)
        if match:
            start = max(0, int(match.group(1)) - 1)
            result.extend(original[cursor:start])
            cursor = start
            in_hunk = True
        elif in_hunk and line.startswith(" "):
            assert original[cursor] == line[1:], (path, cursor, "context mismatch")
            result.append(original[cursor])
            cursor += 1
        elif in_hunk and line.startswith("-"):
            assert original[cursor] == line[1:], (path, cursor, "removal mismatch")
            cursor += 1
        elif in_hunk and line.startswith("+"):
            result.append(line[1:])
        elif in_hunk and line.startswith("\\ No newline"):
            raise AssertionError("Unexpected missing-newline marker in this documented baseline")
    result.extend(original[cursor:])
    return "".join(result)



def capture():
    diffs = []
    source_hashes = {}
    for path, expected in baseline["sourceHashes"].items():
        before = baseline_text(path)
        assert hashlib.sha256(before.encode()).hexdigest() == expected, path
        after = (ROOT / path).read_text()
        source_hashes[path] = hashlib.sha256(after.encode()).hexdigest()
        diffs.extend(difflib.unified_diff(
            before.splitlines(keepends=True),
            after.splitlines(keepends=True),
            fromfile=f"baseline/{path}",
            tofile=f"remediated/{path}",
        ))
    (EVIDENCE / "remediation.diff").write_text("".join(diffs))
    result = {
        "auditId": "AUD-004",
        "phase": "explicitly authorized documentation remediation",
        "capturedAt": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "authorization": "The user explicitly requested that all issues be fixed after the baseline review, and requested a Russian summary of changes and proposed improvements.",
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "fixCommit": None,
        "verificationCommit": None,
        "baselineFingerprint": baseline["sourceFingerprint"],
        "sourceHashes": source_hashes,
        "sourceFingerprint": hashlib.sha256(json.dumps(source_hashes, sort_keys=True).encode()).hexdigest(),
        "diff": "remediation.diff",
        "baselineReconstruction": "Both source texts reconstructed in memory from recorded HEAD and scoped diff; SHA-256 matched the initial snapshot exactly. No second checkout or source copy was created.",
    }
    (EVIDENCE / "remediation-snapshot.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    capture()
