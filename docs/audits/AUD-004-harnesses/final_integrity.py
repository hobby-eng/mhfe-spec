"""Hash the completed audit and source without a self-referential control loop."""

import hashlib
import json
from pathlib import Path
import subprocess


EVIDENCE = Path(__file__).resolve().parents[1]
AUDITS = EVIDENCE.parent
ROOT = EVIDENCE.parents[2]
excluded = {"SHA256SUMS", "final-integrity.log", "final-integrity.command.json"}
paths = [path for path in EVIDENCE.rglob("*") if path.is_file() and path.name not in excluded]
paths += [
    ROOT / "README.md",
    ROOT / "docs/DESIGN-NOTES.md",
    AUDITS / "README.md",
    AUDITS / "audit-04-2026-09-30.md",
    AUDITS / "audit-04-2026-09-30.json",
]
paths = sorted(set(paths))
manifest = EVIDENCE / "SHA256SUMS"
manifest.write_text("".join(
    f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT)}\n"
    for path in paths
))
result = subprocess.run(
    ["sha256sum", "--check", "--quiet", str(manifest)], cwd=ROOT, capture_output=True, text=True
)
assert result.returncode == 0, result.stdout + result.stderr
commands = 0
for path in EVIDENCE.glob("*.command.json"):
    if path.name in excluded:
        continue
    command = json.loads(path.read_text())
    assert hashlib.sha256((EVIDENCE / command["log"]).read_bytes()).hexdigest() == command["logSha256"]
    commands += 1
print(f"PASS: {len(paths)} source/report/evidence SHA-256 entries checked from repository root.")
print(f"PASS: {commands} completed command sidecars match their retained logs.")
print("Excluded only SHA256SUMS and final-integrity.log/final-integrity.command.json to avoid self-reference.")
print(f"Manifest SHA-256: {hashlib.sha256(manifest.read_bytes()).hexdigest()}")
