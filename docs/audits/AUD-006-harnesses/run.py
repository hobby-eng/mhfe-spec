"""AUD-006 baseline checks of mhfe_spec: run each check, record its command, times, exit code and log hash.

Usage, from the repository root:
    python3 -B docs/audits/AUD-006-harnesses/run.py <bip39 english.rs> <mhfe suite 3 zero-12.json>
Exit status is non-zero if any check fails. Evidence is written to docs/audits/AUD-006-evidence/ (local only).
"""
import hashlib, json, re, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "docs/audits/AUD-006-evidence"


def now():
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def run(name, command, cwd=ROOT):
    start = now()
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
    end = now()
    log = result.stdout + result.stderr
    (EVIDENCE / f"{name}.log").write_text(log)
    record = {"command": " ".join(command), "cwd": ".", "startedAt": start, "endedAt": end,
              "exitCode": result.returncode, "logSha256": hashlib.sha256(log.encode()).hexdigest()}
    (EVIDENCE / f"{name}.command.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"{name}: exit {result.returncode}")
    return result.returncode == 0


def anchors(text):
    out = set()
    for heading in re.findall(r"^#+\s+(.*)$", text, re.M):
        slug = re.sub(r"[^\w\- ]", "", heading.strip().lower()).replace(" ", "-")
        out.add(slug)
    return out


def link_check():
    """Every in-repository Markdown link resolves to a file, and every #anchor to a heading."""
    broken = []
    for md in sorted(ROOT.rglob("*.md")):
        rel = md.relative_to(ROOT)
        if any(p in ("node_modules", "drafts") or p.endswith("-evidence") for p in rel.parts) or rel.parts[:2] == ("docs", "archive"):
            continue
        # Link syntax quoted inside code is text, not a link.
        text = re.sub(r"```.*?```", "", md.read_text(), flags=re.S)
        text = re.sub(r"`[^`\n]*`", "", text)
        for target in re.findall(r"\]\(([^)\s]+)\)", text):
            if re.match(r"[a-z]+:", target):
                continue
            path, _, anchor = target.partition("#")
            dest = (md.parent / path).resolve() if path else md
            if not dest.exists():
                broken.append(f"{rel}: {target} (missing file)")
            elif anchor and dest.suffix == ".md" and anchor not in anchors(dest.read_text()):
                broken.append(f"{rel}: {target} (missing anchor)")
    return broken


def main():
    wordlist, zero12 = sys.argv[1], sys.argv[2]
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    ok = [
        run("check-spec-documents", ["python3", "-B", "scripts/check-spec.py", "documents", wordlist]),
        run("check-spec-analysis", ["python3", "-B", "scripts/check-spec.py", "analysis", wordlist, zero12]),
        run("aud005-record-validate", ["python3", "-B", "docs/audits/AUD-005-harnesses/record.py", "validate"]),
        run("prettier-check", ["npx", "--no-install", "prettier", "--check", "README.md", "CHANGELOG.md",
                               "docs/DESIGN-NOTES.md", "vectors/README.md", "vectors/suite3/README.md",
                               "vectors/suite4/README.md", "vectors/profiles/README.md", "docs/archive/README.md"]),
        run("sha256sums-suite3", ["sha256sum", "-c", "SHA256SUMS"], cwd=ROOT / "vectors/suite3"),
        run("sha256sums-suite4", ["sha256sum", "-c", "SHA256SUMS"], cwd=ROOT / "vectors/suite4"),
        run("sha256sums-suite2", ["sha256sum", "-c", "SHA256SUMS"], cwd=ROOT / "vectors/archive/suite-2"),
        run("git-diff-check", ["git", "diff", "--check"]),
    ]
    broken = link_check()
    (EVIDENCE / "link-check.json").write_text(json.dumps({"broken": broken}, indent=2) + "\n")
    print(f"link-check: {len(broken)} broken")
    ok.append(not broken)
    sys.exit(0 if all(ok) else 1)


main()
