"""Capture document metadata or validate the AUD-005 report; never run MHFE."""

import hashlib
import json
import platform
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "docs/audits/AUD-005-evidence"
REPORT = ROOT / "docs/audits/audit-05-2026-09-30"
PUBLICATION = ROOT / "docs/audits/AUD-005-publication.json"
REVIEWED_COMMIT = "8ece0b67d22bb2f7886ee27376969b8db6237e89"
SOURCES = ("README.md", "docs/DESIGN-NOTES.md")
PROCEDURES = (
    "multi-chain-wallet-tools/docs/FULL_AUDIT_GUIDE.md",
    "multi-chain-wallet-tools/docs/audits/AUDIT_STANDARD.md",
    "multi-chain-wallet-tools/docs/audits/AUDIT_TEMPLATE.md",
    "multi-chain-wallet-tools/docs/audit-report.schema.json",
    "AGENTS.md",
    "mhfe_spec/AGENTS.md",
)


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(name, value):
    (EVIDENCE / name).write_text(json.dumps(value, indent=2) + "\n")


def git(*arguments):
    return subprocess.check_output(
        ["git", *arguments], cwd=ROOT, text=True
    ).strip()


def source_files(originals=None):
    """Fingerprints of the reviewed documents, taken from `originals` where a file was edited later."""
    originals = originals or {}
    result = {}
    for name in SOURCES:
        data = originals[name] if name in originals else (ROOT / name).read_bytes()
        result[name] = {
            "sha256": digest(data),
            "sizeBytes": len(data),
            "lineCount": len(data.splitlines()),
        }
    return result


def capture():
    if git("rev-parse", "HEAD") != REVIEWED_COMMIT:
        raise ValueError("Reviewed HEAD changed; create a new snapshot deliberately.")
    files = source_files()
    for name, metadata in files.items():
        committed = subprocess.check_output(
            ["git", "show", f"HEAD:{name}"], cwd=ROOT
        )
        if digest(committed) != metadata["sha256"]:
            raise ValueError(f"Reviewed document differs from HEAD: {name}")
    manifest = "".join(f"{name}\0{files[name]['sha256']}\n" for name in SOURCES)
    snapshot = {
        "capturedAt": now(),
        "commit": REVIEWED_COMMIT,
        "commitComplete": True,
        "branch": git("branch", "--show-current"),
        "workingTree": git("status", "--short"),
        "preExistingChanges": "Untracked AGENTS.md; reviewed documents match HEAD.",
        "sourceFiles": files,
        "sourceFingerprint": digest(manifest.encode()),
        "fingerprintMethod": "SHA-256 of path + NUL + file SHA-256 + LF, in sourceFiles order.",
    }
    save("snapshot.json", snapshot)
    hashes = {name: digest((ROOT.parent / name).read_bytes()) for name in PROCEDURES}
    skill = Path.home() / ".codex/skills/wallet-full-audit/SKILL.md"
    hashes[str(skill)] = digest(skill.read_bytes())
    save("procedure-hashes.json", hashes)
    (EVIDENCE / "environment.log").write_text(
        f"Captured: {now()}\nOS: {platform.platform()}\n"
        f"Python: {sys.version}\nExecutable: {sys.executable}\n"
        "No application toolchain, browser, vector or benchmark was executed.\n"
    )
    return {"outcome": "passed", "sourceFiles": files, "sourceFingerprint": snapshot["sourceFingerprint"]}


def first_published_bytes(publication):
    """Recover the bytes first published with the record for every file edited afterwards.

    A later edit is listed in subsequentEdits. Its hash must match both the current file and
    publishedFiles, and its reverse patch must lead back to the first published bytes, so the
    audited documents stay recoverable after the commit is amended.
    """
    originals = {}
    for edit in publication.get("subsequentEdits", []):
        name = edit["document"]
        current = (ROOT / name).read_bytes()
        if digest(current) != edit["editedSha256"] or publication["publishedFiles"].get(name) != edit["editedSha256"]:
            raise ValueError(f"Subsequent edit does not match the file: {name}")
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "document"
            path.write_bytes(current)
            subprocess.run(
                ["patch", "--silent", str(path)], input=edit["reversePatchToFirstPublication"].encode(),
                check=True, capture_output=True,
            )
            original = path.read_bytes()
        if digest(original) != edit["firstPublicationSha256"]:
            raise ValueError(f"Reverse patch does not recover the published bytes: {name}")
        originals[name] = original
    return originals


def check_baseline_patch(patch, originals):
    """Check that the baseline reverse patch applies to the published documents.

    The check runs on copies in a temporary folder, so that documents edited after publication are
    checked in their published form.
    """
    with tempfile.TemporaryDirectory() as folder:
        for name in SOURCES:
            path = Path(folder) / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(originals[name] if name in originals else (ROOT / name).read_bytes())
        subprocess.run(["git", "apply", "--check"], input=patch, cwd=folder, check=True, capture_output=True)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def validate():
    import jsonschema

    record = json.loads(REPORT.with_suffix(".json").read_text(), object_pairs_hook=unique_object)
    schema = json.loads((ROOT.parent / PROCEDURES[3]).read_text())
    jsonschema.Draft202012Validator(schema).validate(record)
    markdown = REPORT.with_suffix(".md").read_text()
    snapshot = json.loads((EVIDENCE / "snapshot.json").read_text())
    if record["snapshot"] != snapshot:
        raise ValueError("Baseline report snapshot changed.")
    # An authorized amend changes HEAD. Bind follow-up checks to the exact document bytes.
    current_snapshot = record.get("remediationAddendum", snapshot)
    source_snapshot = "remediation" if "remediationAddendum" in record else "baseline"
    originals = {}
    if PUBLICATION.exists():
        publication = json.loads(PUBLICATION.read_text(), object_pairs_hook=unique_object)
        if publication["auditedSourceFiles"] != current_snapshot["sourceFiles"]:
            raise ValueError("Publication is not bound to the audited document bytes.")
        for name, expected in publication["publishedFiles"].items():
            if digest((ROOT / name).read_bytes()) != expected:
                raise ValueError(f"Published file changed: {name}")
        originals = first_published_bytes(publication)
        patch = publication["baselineReversePatch"].encode()
        if digest(patch) != publication["baselineReversePatchSha256"]:
            raise ValueError("Publication reverse patch hash mismatch.")
        check_baseline_patch(patch, originals)
        current_snapshot = publication
        source_snapshot = "publication"
    if "remediationAddendum" not in record and git("rev-parse", "HEAD") != REVIEWED_COMMIT:
        raise ValueError("Baseline HEAD changed.")
    if source_files(originals) != current_snapshot["sourceFiles"]:
        raise ValueError("Reviewed document bytes changed.")
    hashes = json.loads((EVIDENCE / "procedure-hashes.json").read_text())
    if record["procedureHashes"] != hashes:
        raise ValueError("Report procedure hashes differ from capture.")
    for name, expected in hashes.items():
        path = Path(name) if Path(name).is_absolute() else ROOT.parent / name
        if digest(path.read_bytes()) != expected:
            raise ValueError(f"Procedure changed: {name}")
    ids = [finding["id"] for finding in record["findings"]]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate finding IDs.")
    for finding in record["findings"]:
        row = f"| {finding['id']} | {finding['category']} | finding | {finding['severity']} | {finding['status']} |"
        if row not in markdown or f"#### {finding['id']} —" not in markdown:
            raise ValueError(f"Markdown finding mismatch: {finding['id']}")
    for item in record["remediation"]:
        if f"| {item['id']} | {item['status']} |" not in markdown:
            raise ValueError(f"Remediation mismatch: {item['id']}")
    guide = (ROOT.parent / PROCEDURES[0]).read_text()
    expected_checks = re.findall(r"^### (CHECK-[A-Z]+-\d+)", guide, re.M)
    actual_checks = [item["checkId"] for item in record["coverageLedger"]]
    if len(actual_checks) != 32 or sorted(actual_checks) != sorted(expected_checks):
        raise ValueError("Coverage ledger does not match all 32 procedure IDs.")
    for check in record["coverageLedger"]:
        if f"| {check['checkId']} |" not in markdown:
            raise ValueError(f"Missing Markdown coverage: {check['checkId']}")
    for target in re.findall(r"\]\(([^)]+)\)", markdown):
        parsed = urlsplit(target)
        if parsed.scheme or not parsed.path:
            continue
        if not (REPORT.parent / unquote(parsed.path)).exists():
            raise ValueError(f"Missing report link: {target}")
    if "local evidence only" not in markdown or "Local only:" not in markdown:
        raise ValueError("Local evidence must be labelled.")
    git("check-ignore", "docs/audits/AUD-005-evidence/snapshot.json")
    staged = git("diff", "--cached", "--name-only")
    if any("-evidence/" in path for path in staged.splitlines()):
        raise ValueError("Audit evidence is staged.")
    result = {
        "outcome": "passed", "validatedAt": now(), "findings": len(ids),
        "coverageRows": len(actual_checks), "duplicateKeys": False,
        "sourceUnchanged": True, "evidenceIgnoredAndNotStaged": True,
        "sourceSnapshot": source_snapshot,
        "scope": "Audit/publication records, document metadata and file hashes only; no MHFE execution or vector recomputation.",
    }
    save("report-validation.json", result)
    return result


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in ("capture", "validate"):
        raise SystemExit("Usage: python3 docs/audits/AUD-005-harnesses/record.py capture|validate")
    EVIDENCE.mkdir(exist_ok=True)
    mode = sys.argv[1]
    name = "record-capture" if mode == "capture" else "record-validation"
    if mode == "validate" and "remediationAddendum" in json.loads(REPORT.with_suffix(".json").read_text()):
        name = "remediation-validation"
    if mode == "validate" and PUBLICATION.exists():
        name = "publication-validation"
    started = now()
    code = 0
    try:
        result = capture() if mode == "capture" else validate()
    except Exception as error:
        result = {"outcome": "failed", "error": f"{type(error).__name__}: {error}"}
        code = 1
    log = json.dumps(result, indent=2) + "\n"
    (EVIDENCE / f"{name}.log").write_text(log)
    save(f"{name}.command.json", {
        "command": f"python3 docs/audits/AUD-005-harnesses/record.py {mode}",
        "cwd": str(ROOT), "startedAt": started, "endedAt": now(),
        "exitCode": code, "logSha256": digest(log.encode()),
    })
    # Exclude the manifest itself; it records the final bytes of every other local record.
    manifest = "".join(
        f"{digest(path.read_bytes())}  {path.name}\n"
        for path in sorted(EVIDENCE.iterdir())
        if path.is_file() and path.name != "SHA256SUMS"
    )
    (EVIDENCE / "SHA256SUMS").write_text(manifest)
    print(log, end="")
    raise SystemExit(code)


if __name__ == "__main__":
    main()
