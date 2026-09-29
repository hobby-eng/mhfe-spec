"""Check links and citation numbering in the two audited documents only."""

from collections import Counter
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[4]
DOCUMENTS = [ROOT / "README.md", ROOT / "docs/DESIGN-NOTES.md"]


def without_fences(text):
    return re.sub(r"^```.*?^```[^\n]*$", "", text, flags=re.M | re.S)


def anchors(path):
    counts = Counter()
    result = set()
    for line in without_fences(path.read_text()).splitlines():
        match = re.match(r"^#{1,6}\s+(.+?)\s*#*$", line)
        if not match:
            continue
        # All referenced headings here are ordinary ASCII prose headings.
        slug = re.sub(r"[^\w\- ]", "", match.group(1).lower()).replace(" ", "-")
        suffix = "" if counts[slug] == 0 else f"-{counts[slug]}"
        counts[slug] += 1
        result.add(slug + suffix)
    return result


references = DOCUMENTS[0].read_text().split("## References\n", 1)[1]
defined = [int(n) for n in re.findall(r"^(\d+)\. ", references, flags=re.M)]
assert defined == list(range(1, 45)), defined
checked = 0
for path in DOCUMENTS:
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
    print(f"{path.relative_to(ROOT)}: {len(cited)} distinct numeric references; all resolve")
print(f"PASS: {checked} local links and 44 consecutive bibliography entries")
print("Scope: Markdown destination/heading checks only; no utility execution or external reachability claim.")
