"""Check the relative links and heading anchors of the current Markdown documents.

Covers every tracked Markdown file except the untracked drafts, the archived suite 2 documents and
the retained audit records, which are historical evidence. Exits non-zero on a missing target or
an unknown anchor.
"""
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
SKIP = ("docs/drafts/", "docs/archive/", "docs/audits/")


def slugs(path):
    out, seen, fence = set(), {}, False
    for line in open(path, encoding="utf-8"):
        if line.startswith("```"):
            fence = not fence
            continue
        match = None if fence else re.match(r"^(#{1,6})\s+(.*)", line)
        if match:
            text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", re.sub(r"`([^`]*)`", r"\1", match.group(2).strip()))
            base = re.sub(r"[^\w\- ]", "", re.sub(r"[*_]", "", text).lower()).replace(" ", "-")
            count = seen.get(base, 0)
            seen[base] = count + 1
            out.add(base if count == 0 else f"{base}-{count}")
    return out


def main():
    files = [f for f in subprocess.check_output(["git", "-C", ROOT, "ls-files", "*.md"], text=True).split() if not f.startswith(SKIP)]
    bad, cache, total = 0, {}, 0
    for name in files:
        path = os.path.join(ROOT, name)
        text = re.sub(r"```.*?```", "", open(path, encoding="utf-8").read(), flags=re.S)
        for target in re.findall(r"\]\(([^)\s]+)\)", text):
            if re.match(r"^[a-z]+:", target):
                continue
            total += 1
            file_part, _, anchor = target.partition("#")
            resolved = os.path.normpath(os.path.join(os.path.dirname(path), file_part)) if file_part else path
            if not os.path.exists(resolved):
                print(f"{name}: missing {target}")
                bad += 1
            elif anchor and resolved.endswith(".md"):
                cache.setdefault(resolved, slugs(resolved))
                if anchor not in cache[resolved]:
                    print(f"{name}: unknown anchor {target}")
                    bad += 1
    print(f"{len(files)} files, {total} relative links, {bad} bad")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
