"""Record one AUD-010 check without changing its command, output or exit status.

Run from the repository root:
    python3 docs/audits/AUD-010-harnesses/record.py NAME -- COMMAND [ARG ...]
Only public test inputs may be used. Evidence remains local and Git-ignored.
"""

import datetime
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "docs/audits/AUD-010-evidence"


def main():
    """Execute an unchanged check and retain its output and identity."""
    if len(sys.argv) < 4 or sys.argv[2] != "--":
        raise SystemExit("usage: record.py NAME -- COMMAND [ARG ...]")
    name, command = sys.argv[1], sys.argv[3:]
    if not name or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-_" for c in name):
        raise SystemExit("invalid check name")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    log, record = EVIDENCE / f"{name}.log", EVIDENCE / f"{name}.command.json"
    if log.exists() or record.exists():
        raise SystemExit("choose a new name: existing evidence must not be overwritten")
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with log.open("wb") as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    item = {
        "command": shlex.join(command),
        "argv": command,
        "startUtc": started,
        "endUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "exitCode": result.returncode,
        "logSha256": hashlib.sha256(log.read_bytes()).hexdigest(),
        "environmentOverrides": {
            key: os.environ[key] for key in (
                "PYTHONPATH", "PYTHONDONTWRITEBYTECODE", "MHFE_PDF_DEPENDENCIES",
                "CARGO_HOME", "RUSTUP_HOME", "CARGO_TARGET_DIR"
            ) if key in os.environ
        },
    }
    record.write_text(json.dumps(item, indent=2) + "\n", encoding="utf-8")
    print(f"{name}: exit {result.returncode}; {log.relative_to(ROOT)}")
    print(log.read_text(encoding="utf-8", errors="replace")[-3500:])
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
