"""Check shared bibliography identity/order and current document links for AUD-007."""

import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
FILES = ["README.md", "CHANGELOG.md", "docs/DESIGN-NOTES.md", "vectors/README.md", "vectors/suite3/README.md", "vectors/suite4/README.md", "vectors/profiles/README.md", "docs/archive/README.md"]


def references(text):
    parts = re.split(r"(?m)^(\d+)\. ", text.split("## References\n", 1)[1])
    return {int(parts[i]): " ".join(parts[i + 1].split()) for i in range(1, len(parts), 2)}


def anchors(text):
    used, out = {}, set(re.findall(r"<a\s+(?:name|id)=[\"']([^\"']+)", text))
    for heading in re.findall(r"^#+\s+(.*)$", text, re.M):
        heading = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", heading)
        slug = re.sub(r"[^\w\- ]", "", heading.strip().lower()).replace(" ", "-")
        number = used.get(slug, 0)
        used[slug] = number + 1
        out.add(slug if number == 0 else slug + "-" + str(number))
    return out


def main():
    main_text = (ROOT / "README.md").read_text()
    notes = (ROOT / "docs/DESIGN-NOTES.md").read_text()
    current = references(main_text)
    old = references(subprocess.check_output(["git", "show", "HEAD:README.md"], cwd=ROOT).decode())
    assert len(current) == 64 and current == old, "Bibliography differs from HEAD."
    body = main_text.split("## References")[0] + "\n" + notes.split("## References")[0]
    body = re.sub(r"```.*?```", "", body, flags=re.S)
    seen = []
    for match in re.finditer(r"\[(\d+)\](?:\s*[-–]\s*\[(\d+)\])?", body):
        values = range(int(match[1]), int(match[2]) + 1) if match[2] else [int(match[1])]
        for number in values:
            if number not in seen:
                seen.append(number)
    assert seen == list(range(1, 65)), seen
    broken, count = [], 0
    for name in FILES:
        for link in re.findall(r"\]\(([^)\s]+)\)", (ROOT / name).read_text()):
            if re.match(r"[a-z]+:", link):
                continue
            target, _, anchor = link.partition("#")
            dest = (ROOT / name).parent / target if target else ROOT / name
            count += 1
            if not dest.exists() or (anchor and dest.suffix == ".md" and anchor not in anchors(dest.read_text())):
                broken.append([name, link])
    assert not broken, broken
    print(json.dumps({"references": len(current), "firstCitationOrder": seen, "referenceDefinitionsUnchangedFromHead": True, "localLinks": count, "brokenLinks": broken}))


if __name__ == "__main__":
    main()
