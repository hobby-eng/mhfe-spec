#!/usr/bin/env python3
"""Freeze the current trial-count proof/specification/document inputs without copying projects."""

import datetime
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    workspace = Path(__file__).resolve().parents[4]
    evidence = Path(__file__).resolve().parents[1] / "AUD-016-evidence"
    lean = workspace / "tmp/lean-review-2026-11-11/port-v4.35"
    ec = workspace / "tmp/easycrypt-mhfe-2026-11-09"
    paths = [*(lean / "MhfeLean/Chapters").glob("*.lean"), lean / "MhfeLean.lean",
             *[lean / name for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain",
                 "README.md", "MhfeLean/Chapters/README.md", "check.sh", "check-selftest.sh"]],
             *(ec / "src").glob("*.ec"), *[ec / name for name in ["README.md", "ASSUMPTIONS.md",
                 "DESIGN.md", "INDEX.md", "SHA256SUMS", "check.sh", "check-selftest.sh",
                 "LEAN-COMPARISON.md", "HANDOFF.md"]],
             workspace / "tmp/lean-review-2026-11-11/PORT-v4.35.md",
             workspace / "tmp/lean-review-2026-11-11/review-2026-11-13/TRIALS-REVIEW.md",
             workspace / "mhfe_spec/README.md", workspace / "mhfe_spec/docs/DESIGN-NOTES.md"]
    rows = []
    for path in sorted(set(paths)):
        data = path.read_bytes()
        rows.append({"path": str(path.relative_to(workspace)), "bytes": len(data),
                     "sha256": hashlib.sha256(data).hexdigest()})
    def git(*args):
        return subprocess.check_output(["git", "-C", str(workspace / "mhfe_spec"), *args], text=True).strip()
    value = {"capturedUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
             "specCommit": git("rev-parse", "HEAD"), "specOriginMain": git("rev-parse", "origin/main"),
             "files": rows, "leanChapters": len(list((lean / "MhfeLean/Chapters").glob("*.lean"))),
             "easycryptSources": len(list((ec / "src").glob("*.ec")))}
    value["fingerprint"] = hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest()
    target = evidence / "snapshot.json"
    assert not target.exists(), "Preserve a prior snapshot rather than overwriting it"
    target.write_text(json.dumps(value, indent=2) + "\n")
    print({key: val for key, val in value.items() if key != "files"})


if __name__ == "__main__":
    main()
