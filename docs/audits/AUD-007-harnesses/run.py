"""Capture and run bounded document-release checks for AUD-007. No full-size Argon2.

Run from the mhfe_spec root: python3 -B docs/audits/AUD-007-harnesses/run.py capture|checks|integrity.
Public wordlists and vector fixtures are read from the adjacent authoritative mhfe checkout.
"""

import hashlib
import json
import re
import runpy
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "docs/audits/AUD-007-evidence"
WORDLIST = ROOT.parent / "workingspace/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bip39-3.0.0/src/language/english.rs"
PROCEDURE_ROOT = ROOT.parent / "multi-chain-wallet-tools"
PROCEDURES = ["docs/FULL_AUDIT_GUIDE.md", "docs/audits/AUDIT_STANDARD.md", "docs/audits/AUDIT_TEMPLATE.md", "docs/audit-report.schema.json"]


def now():
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args]).decode().strip()


def save(name, data):
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / name).write_text(json.dumps(data, indent=2) + "\n")


def capture():
    if (EVIDENCE / "snapshot.json").exists():
        raise ValueError("Existing snapshot must not be overwritten.")
    names = git(ROOT, "ls-files").splitlines()
    source = {name: digest((ROOT / name).read_bytes()) for name in names if not name.startswith("docs/audits/") and (ROOT / name).is_file()}
    manifest = "".join(name + "\0" + source[name] + "\n" for name in sorted(source))
    save("snapshot.json", {"capturedAt": now(), "commit": git(ROOT, "rev-parse", "HEAD"), "commitComplete": False, "branch": git(ROOT, "branch", "--show-current"), "workingTree": git(ROOT, "status", "--short"), "sourceFiles": source, "sourceFingerprint": digest(manifest.encode()), "fingerprintMethod": "Sorted path + NUL + SHA-256 + LF; tracked non-audit files only; untracked drafts excluded.", "implementationCommit": git(ROOT.parent / "mhfe", "rev-parse", "HEAD"), "implementationWorkingTree": git(ROOT.parent / "mhfe", "status", "--short")})
    hashes = {name: digest((PROCEDURE_ROOT / name).read_bytes()) for name in PROCEDURES}
    hashes["workspace/AGENTS.md"] = digest((ROOT.parent / "AGENTS.md").read_bytes())
    hashes["mhfe_spec/AGENTS.md"] = digest((ROOT / "AGENTS.md").read_bytes())
    for skill in ("wallet-full-audit", "wallet-release-verification"):
        hashes["skills/" + skill + "/SKILL.md"] = digest((Path.home() / ".codex/skills" / skill / "SKILL.md").read_bytes())
    save("procedure-hashes.json", hashes)
    print(json.dumps({"captured": len(source), "sourceFingerprint": digest(manifest.encode())}))


def command(name, args, cwd=ROOT):
    started = now()
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    log = result.stdout + result.stderr
    (EVIDENCE / (name + ".log")).write_text(log)
    record = {"name": name, "command": args, "cwd": str(cwd), "startedAt": started, "endedAt": now(), "exitCode": result.returncode, "logSha256": digest(log.encode())}
    save(name + ".command.json", record)
    print(f"{name}: exit {result.returncode}")
    return result.returncode == 0


def recorded_keys():
    old = runpy.run_path(str(ROOT / "docs/audits/AUD-003-harnesses/notation_check.py"))
    words = old["load_wordlist"](WORDLIST)
    counts = {}
    for suite, folder, schema, function in (("suite3", "vectors/suite3", "mhfe-suite-3-vector-v2", "check_suite3"), ("suite2", "vectors/archive/suite-2", None, "check_suite2")):
        count = 0
        for path in sorted((ROOT / folder).glob("*.json")):
            data = json.loads(path.read_text())
            if not isinstance(data, dict) or path.name == "validation-cases.json" or (schema and data.get("schema") != schema):
                continue
            old[function](str(path), words)
            count += 1
        counts[suite] = count
    assert counts == {"suite3": 17, "suite2": 9}, counts
    save("recorded-keys.json", {"outcome": "passed", "counts": counts, "argon2Recomputed": False})
    print(json.dumps(counts))


def checks():
    zero12 = ROOT.parent / "mhfe/tests/fixtures/suite3-vectors/zero-12.json"
    outcomes = [command("documents", [sys.executable, "-B", "scripts/check-spec.py", "documents", str(WORDLIST)]), command("analysis", [sys.executable, "-B", "scripts/check-spec.py", "analysis", str(WORDLIST), str(zero12)]), command("format", ["pnpm", "format:check"]), command("diff", ["git", "diff", "--check"]), command("audit-record", [sys.executable, "-B", "docs/audits/AUD-005-harnesses/record.py", "validate"])]
    for name, folder in (("suite3", "vectors/suite3"), ("suite4", "vectors/suite4"), ("suite2", "vectors/archive/suite-2")):
        outcomes.append(command("checksums-" + name, ["sha256sum", "--check", "SHA256SUMS"], ROOT / folder))
    recorded_keys()
    if not all(outcomes):
        raise SystemExit(1)


def integrity():
    initial = json.loads((EVIDENCE / "snapshot.json").read_text())
    changed = [name for name, expected in initial["sourceFiles"].items() if not (ROOT / name).is_file() or digest((ROOT / name).read_bytes()) != expected]
    save("final-integrity.json", {"checkedAt": now(), "sourceChanged": changed, "headUnchanged": initial["commit"] == git(ROOT, "rev-parse", "HEAD")})
    print(json.dumps({"sourceChanged": changed}))
    if changed:
        raise SystemExit(1)


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    {"capture": capture, "checks": checks, "integrity": integrity}[sys.argv[1]]()
