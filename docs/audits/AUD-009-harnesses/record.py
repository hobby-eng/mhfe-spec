"""Record a bounded audit command without changing reviewed sources."""

import datetime
import hashlib
import json
import pathlib
import subprocess
import sys


def main():
    """Write an original command log and its UTC execution record."""
    root = pathlib.Path(__file__).resolve().parents[3]
    evidence = root / "docs/audits/AUD-009-evidence"
    evidence.mkdir(exist_ok=True)
    name, *command = sys.argv[1:]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (evidence / (name + ".log")).open("wb") as stream:
        result = subprocess.run(command, cwd=root, stdout=stream,
                                stderr=subprocess.STDOUT, check=False)
    ended = datetime.datetime.now(datetime.timezone.utc).isoformat()
    log = evidence / (name + ".log")
    record = {"command": command, "cwd": str(root), "startedUtc": started,
              "endedUtc": ended, "exitCode": result.returncode,
              "logSha256": hashlib.sha256(log.read_bytes()).hexdigest()}
    (evidence / (name + ".command.json")).write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record))
    print(log.read_text(encoding="utf-8", errors="replace")[-12000:])
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())
