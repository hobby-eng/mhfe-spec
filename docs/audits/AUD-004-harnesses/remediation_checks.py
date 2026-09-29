"""Check edited document links and frozen protocol syntax, not MHFE utilities."""

from collections import Counter
import hashlib
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit

from remediation_snapshot import ROOT, baseline_text


def without_fences(text):
    return re.sub(r"^```.*?^```[^\n]*$", "", text, flags=re.M | re.S)


def anchors(path):
    counts = Counter()
    result = set()
    for line in without_fences(path.read_text()).splitlines():
        match = re.match(r"^#{1,6}\s+(.+?)\s*#*$", line)
        if match:
            slug = re.sub(r"[^\w\- ]", "", match.group(1).lower()).replace(" ", "-")
            result.add(slug + ("" if counts[slug] == 0 else f"-{counts[slug]}"))
            counts[slug] += 1
    return result


def code_blocks(text):
    # Complete fenced bytes, including spaces and quoted domain labels, stay unchanged.
    return re.findall(r"^```[^\n]*\n.*?^```[^\n]*$", text, flags=re.M | re.S)


paths = [ROOT / "README.md", ROOT / "docs/DESIGN-NOTES.md"]
readme = paths[0].read_text()
original = baseline_text("README.md")
assert code_blocks(readme) == code_blocks(original), "A README fenced protocol block changed"
old_table = original.split("| Component", 1)[1].split("```", 1)[0]
new_table = readme.split("| Component", 1)[1].split("```", 1)[0]
assert old_table == new_table, "Frozen suite parameter table changed"
old_packing = original.split("### Packing\n", 1)[1].split("### Permutation", 1)[0]
new_packing = readme.split("### Packing\n", 1)[1].split("### Permutation", 1)[0]
assert old_packing == new_packing, "Packing definition changed"
old_core = original.split("### Permutation\n", 1)[1].split("### Creating", 1)[0]
new_core = readme.split("### Permutation\n", 1)[1].split("### Creating", 1)[0]
assert old_core == new_core, "Permutation or primitive definition changed"
rationale = readme.split("## Rationale\n", 1)[1].split("## Backward Compatibility", 1)[0]
assert len(re.findall(r"^\*\*Why .+?\?\*\*", rationale, re.M)) == 9
print("PASS: complete README fenced blocks, parameter table, packing and permutation definitions unchanged; all nine Rationale answers retained")

references = readme.split("## References\n", 1)[1]
defined = [int(n) for n in re.findall(r"^(\d+)\. ", references, re.M)]
assert defined == list(range(1, len(defined) + 1)), "Bibliography is not consecutive"
assert len(defined) >= 44, "Existing bibliography entries were lost"
checked = 0
for path in paths:
    contents = without_fences(path.read_text())
    for target in re.findall(r"(?<!!)\[[^\]\n]+\]\(([^\s)]+)\)", contents):
        if urlsplit(target).scheme:
            continue
        filename, _, fragment = target.partition("#")
        resolved = path.parent / unquote(filename) if filename else path
        assert resolved.exists(), (path.name, target, "missing target")
        if fragment and resolved.suffix == ".md":
            assert unquote(fragment) in anchors(resolved), (path.name, target, "missing anchor")
        checked += 1
    cited = {int(n) for n in re.findall(r"\[(\d+)\](?!\()", contents)}
    assert cited.issubset(defined), (path.name, cited - set(defined))
    print(f"{path.relative_to(ROOT)} SHA-256 {hashlib.sha256(path.read_bytes()).hexdigest()}")
print(f"PASS: {checked} current local links; {len(defined)} consecutive bibliography entries; all cited numbers resolve")
print("Scope: document syntax and selected frozen-definition invariants. Manual review separately checks unchanged password acceptance and each wording correction. No actual MHFE or Argon2 execution.")
