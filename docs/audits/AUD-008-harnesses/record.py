"""Capture a bounded, offline audit command without altering historical evidence."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "docs/audits/AUD-008-evidence"


def utc_now():
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command or Path(args.name).name != args.name:
        parser.error("provide a safe log name and a command after --")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    started = utc_now()
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    ended = utc_now()
    (EVIDENCE / (args.name + ".log")).write_bytes(result.stdout)
    record = {
        "command": command,
        "startedAt": started,
        "endedAt": ended,
        "exitCode": result.returncode,
        "logSha256": hashlib.sha256(result.stdout).hexdigest(),
    }
    (EVIDENCE / (args.name + ".command.json")).write_text(json.dumps(record, indent=2) + "\n")
    sys.stdout.buffer.write(result.stdout)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
