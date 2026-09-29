"""Retain exact command evidence for the specification-only AUD-004 review."""

import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


evidence = Path(__file__).resolve().parents[1]
root = evidence.parents[2]
name, command = sys.argv[1:]
started = utc_now()
result = subprocess.run(
    ["/bin/bash", "--noprofile", "--norc", "-c", command],
    cwd=root,
    stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT,
)
ended = utc_now()
log_path = evidence / f"{name}.log"
log_path.write_bytes(result.stdout)
record = {
    "name": name,
    "command": command,
    "shell": "/bin/bash --noprofile --norc -c",
    "cwd": str(root),
    "startedAt": started,
    "endedAt": ended,
    "exitCode": result.returncode,
    "log": log_path.name,
    "logSha256": hashlib.sha256(result.stdout).hexdigest(),
}
(evidence / f"{name}.command.json").write_text(json.dumps(record, indent=2) + "\n")
sys.stdout.buffer.write(result.stdout)
sys.exit(result.returncode)
