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
EDITED_HARNESS_FILES = frozenset(
    str(path.relative_to(ROOT))
    for path in (Path(__file__).resolve(), Path(__file__).resolve().with_name("README.md"))
)
EDITED_DOCUMENTS = frozenset(
    (
        "README.md",
        "CHANGELOG.md",
        "CITATION.cff",
        "docs/audits/AUD-004-publication.json",
        "docs/DESIGN-NOTES.md",
        "vectors/README.md",
        "vectors/suite3/README.md",
    )
)
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


def public_metadata(value):
    """Compare published paths with their normalized view."""
    if isinstance(value, str):
        value = value.replace(Path.home().name, "user")
        if re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?\+00:00", value):
            return value[:-6] + "Z"
        return value
    if isinstance(value, list):
        return [public_metadata(item) for item in value]
    if isinstance(value, dict):
        return {public_metadata(key): public_metadata(item) for key, item in value.items()}
    return value


def report_snapshot(snapshot, record):
    """Map only a presented commit identity; captured evidence and source hashes stay original."""
    result = public_metadata(snapshot)
    bindings = record.get("recordEdits", {}).get("commitBindings", [])
    commits = {}
    for binding in bindings:
        original = binding["originalCommit"]
        replacement = binding["mappedCommit"]
        if not re.fullmatch(r"[0-9a-f]{40}", original) or not re.fullmatch(r"[0-9a-f]{40}", replacement):
            raise ValueError("Invalid presentation commit binding.")
        if original in commits:
            raise ValueError("Duplicate presentation commit binding.")
        commits[original] = replacement
    result["commit"] = commits.get(result["commit"], result["commit"])
    return result


def reverse_patch_bytes(current, patch):
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "document"
        path.write_bytes(current)
        subprocess.run(
            ["patch", "--silent", "--batch", "--fuzz=0", str(path)], input=patch,
            check=True, capture_output=True, timeout=10,
        )
        return path.read_bytes()


def original_patch(entry, key, presentation_key="patchPresentation"):
    patch = entry[key]
    presentation = entry.get(presentation_key)
    if presentation is not None and presentation["kind"] == "local-original-evidence":
        path = EVIDENCE / presentation["file"]
        if path.resolve().parent != EVIDENCE.resolve():
            raise ValueError("Original patch must stay in the local evidence folder.")
        original = path.read_bytes()
        if patch is not None or digest(original) != presentation["originalSha256"]:
            raise ValueError("Original patch evidence changed.")
        return original
    if presentation is not None:
        if presentation["kind"] != "normalized-home-paths" or digest(patch.encode()) != presentation["normalizedSha256"]:
            raise ValueError("Procedure patch presentation changed.")
        patch = patch.replace("/home/user/", str(Path.home()) + "/")
        if digest(patch.encode()) != presentation["originalSha256"]:
            raise ValueError("Original procedure patch cannot be reconstructed on this host.")
    return patch.encode()


def procedure_patch(change):
    return original_patch(change, "reversePatchToAuditedVersion")


def edited_document_bytes(publication, name, current):
    bindings = publication.get("documentEdits", {}).get("documentBindings", [])
    matches = [item for item in bindings if item["document"] == name]
    if not matches:
        return current
    if len(matches) != 1 or name not in EDITED_DOCUMENTS:
        raise ValueError(f"Unauthorized document edit binding: {name}")
    binding = matches[0]
    if digest(current) != binding["presentationSha256"]:
        raise ValueError(f"Edited document changed: {name}")
    patch = original_patch(binding, "reversePatchToOriginal")
    if digest(patch) != binding["reversePatchSha256"]:
        raise ValueError(f"Document edit patch changed: {name}")
    original = reverse_patch_bytes(current, patch)
    if digest(original) != binding["originalSha256"]:
        raise ValueError(f"Document edit does not recover the original bytes: {name}")
    return original


def published_bytes(publication, name, current):
    current = edited_document_bytes(publication, name, current)
    expected = publication["publishedFiles"][name]
    bindings = publication.get("recordEdits", {}).get("documentBindings", [])
    matches = [item for item in bindings if item["document"] == name]
    if not matches:
        if digest(current) != expected:
            raise ValueError(f"Published file changed: {name}")
        return current
    if len(matches) != 1:
        raise ValueError(f"Duplicate record edit binding: {name}")
    if name not in EDITED_HARNESS_FILES:
        raise ValueError(f"A record edit cannot replace source or artifact assertions: {name}")
    binding = matches[0]
    if binding["originalSha256"] != expected or digest(current) != binding["currentSha256"]:
        raise ValueError(f"Record edit binding changed: {name}")
    patch = original_patch(binding, "reversePatchToHistorical")
    if digest(patch) != binding["reversePatchSha256"]:
        raise ValueError(f"Record edit patch changed: {name}")
    original = reverse_patch_bytes(current, patch)
    if digest(original) != expected:
        raise ValueError(f"Record edit does not recover the historical bytes: {name}")
    return original


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


def first_published_bytes(publication, historical_files=None):
    """Recover the bytes first published with the record for every file edited afterwards.

    A later edit is listed in subsequentEdits. Its hash must match both the current file and
    publishedFiles, and its reverse patch must lead back to the first published bytes, so the
    audited documents stay recoverable after the commit is amended.
    """
    originals = {}
    historical_files = historical_files or {}
    for edit in publication.get("subsequentEdits", []):
        name = edit["document"]
        current = historical_files.get(name)
        if current is None:
            current = (ROOT / name).read_bytes()
        if digest(current) != edit["editedSha256"] or publication["publishedFiles"].get(name) != edit["editedSha256"]:
            raise ValueError(f"Subsequent edit does not match the file: {name}")
        original = reverse_patch_bytes(current, original_patch(edit, "reversePatchToFirstPublication"))
        if digest(original) != edit["firstPublicationSha256"]:
            raise ValueError(f"Reverse patch does not recover the published bytes: {name}")
        originals[name] = original
    return originals


def audited_procedure_bytes(publication, name, current, expected):
    """Recover the audited bytes of a procedure file that changed after the audit.

    The workspace instructions are not under version control, so a later change is listed in
    procedureChanges with the current hash and a reverse patch to the audited bytes. The audited
    hash recorded by the audit is never replaced; an unlisted change still fails.
    """
    for change in (publication or {}).get("procedureChanges", []):
        if change["file"] != name or change["currentSha256"] != digest(current):
            continue
        if change["auditedSha256"] != expected:
            raise ValueError(f"Procedure change does not start from the audited bytes: {name}")
        audited = reverse_patch_bytes(current, procedure_patch(change))
        if digest(audited) != expected:
            raise ValueError(f"Reverse patch does not recover the audited procedure: {name}")
        return audited
    raise ValueError(f"Procedure changed: {name}")


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
    markdown = REPORT.with_suffix(".md").read_text()
    snapshot = json.loads((EVIDENCE / "snapshot.json").read_text())
    if record["snapshot"] != report_snapshot(snapshot, record):
        raise ValueError("Baseline report snapshot changed.")
    # An authorized amend changes HEAD. Bind follow-up checks to the exact document bytes.
    current_snapshot = record.get("remediationAddendum", snapshot)
    source_snapshot = "remediation" if "remediationAddendum" in record else "baseline"
    originals = {}
    publication = None
    if PUBLICATION.exists():
        publication = json.loads(PUBLICATION.read_text(), object_pairs_hook=unique_object)
        if publication["auditedSourceFiles"] != current_snapshot["sourceFiles"]:
            raise ValueError("Publication is not bound to the audited document bytes.")
        historical_files = {
            name: published_bytes(publication, name, (ROOT / name).read_bytes())
            for name in publication["publishedFiles"]
        }
        originals = first_published_bytes(publication, historical_files)
        patch = original_patch(publication, "baselineReversePatch", "baselinePatchPresentation")
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
    if record["procedureHashes"] != public_metadata(hashes):
        raise ValueError("Report procedure hashes differ from capture.")
    procedures = {}
    changed_procedures = []
    for name, expected in hashes.items():
        path = Path(name) if Path(name).is_absolute() else ROOT.parent / name
        current = path.read_bytes()
        if digest(current) == expected:
            procedures[name] = current
        else:
            procedures[name] = audited_procedure_bytes(publication, name, current, expected)
            changed_procedures.append(name)
    # The report is checked against the schema and guide as they were when the audit ran.
    schema = json.loads(procedures[PROCEDURES[3]])
    jsonschema.Draft202012Validator(schema).validate(record)
    ids = [finding["id"] for finding in record["findings"]]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate finding IDs.")
    rows = [tuple(cell.strip() for cell in line.split("|")[1:]) for line in markdown.splitlines() if line.startswith("|")]
    for finding in record["findings"]:
        expected = (finding["id"], finding["category"], "finding", finding["severity"], finding["status"])
        if not any(row[:5] == expected for row in rows) or f"#### {finding['id']} —" not in markdown:
            raise ValueError(f"Markdown finding mismatch: {finding['id']}")
    for item in record["remediation"]:
        if not any(row[:2] == (item["id"], item["status"]) for row in rows):
            raise ValueError(f"Remediation mismatch: {item['id']}")
    guide = procedures[PROCEDURES[0]].decode()
    expected_checks = re.findall(r"^### (CHECK-[A-Z]+-\d+)", guide, re.M)
    actual_checks = [item["checkId"] for item in record["coverageLedger"]]
    if len(actual_checks) != 32 or sorted(actual_checks) != sorted(expected_checks):
        raise ValueError("Coverage ledger does not match all 32 procedure IDs.")
    for check in record["coverageLedger"]:
        if not any(row[0] == check["checkId"] for row in rows):
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
        "procedureChangesRecovered": changed_procedures,
        "scope": "Audit/publication records, document metadata and file hashes only; no MHFE execution or vector recomputation.",
    }
    if record.get("recordEdits"):
        result["recordEditOnly"] = True
        result["newAudit"] = False
        save("edit-report-validation.json", result)
    else:
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
    edited = mode == "validate" and bool(json.loads(REPORT.with_suffix(".json").read_text()).get("recordEdits"))
    if edited:
        name = "edit-" + name
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
        if path.is_file() and path.name not in ("SHA256SUMS", "edit-SHA256SUMS")
    )
    (EVIDENCE / ("edit-SHA256SUMS" if edited else "SHA256SUMS")).write_text(manifest)
    print(json.dumps(public_metadata(result), indent=2) if edited else log, end="\n" if edited else "")
    raise SystemExit(code)


if __name__ == "__main__":
    main()
