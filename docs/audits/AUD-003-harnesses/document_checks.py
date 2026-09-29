"""AUD-002 audit harness: structural checks of the specification documents.

Checks the BIP 3 preamble, internal and cross-file links and anchors, the reference list and its
use, and the BIP39 wordlist facts that "Reading words" states. Run from the repository root with
the path of the wordlist source as the only argument.
"""

import os
import re
import sys

DOCS = ["README.md", "docs/DESIGN-NOTES.md", "CHANGELOG.md", "vectors/README.md"]
results = []


def report(label, ok, detail=""):
    results.append(ok)
    print(f"{'PASS' if ok else 'FAIL'}  {label}{': ' + detail if detail else ''}")


def github_slug(heading):
    text = re.sub(r"`|\*|_(?=\w)|(?<=\w)_", "", heading.strip().lower())
    text = re.sub(r"\$`[^`]*`\$", "", text)
    text = re.sub(r"[^\w\- ]", "", text)
    return text.replace(" ", "-")


def anchors(path):
    slugs, counts = set(), {}
    in_code = False
    for line in open(path):
        if line.startswith("```"):
            in_code = not in_code
        if in_code:
            continue
        match = re.match(r"^(#{1,6})\s+(.*)$", line)
        if match:
            slug = github_slug(match.group(2))
            count = counts.get(slug, 0)
            slugs.add(slug if count == 0 else f"{slug}-{count}")
            counts[slug] = count + 1
    return slugs


def links(path):
    text = re.sub(r"```.*?```", "", open(path).read(), flags=re.S)
    return re.findall(r"\]\(([^)\s]+)\)", text)


def main():
    readme = open("README.md").read()

    # BIP 3 preamble: required headers in order, optional ones where BIP 3 places them.
    preamble = re.search(r"```\n((?:  [A-Za-z-]+: .*\n)+)```", readme).group(1)
    fields = [line.split(":")[0].strip() for line in preamble.splitlines()]
    bip3_order = ["BIP", "Layer", "Title", "Authors", "Deputies", "Status", "Type", "Assigned", "License",
                  "Discussion", "Version", "Requires", "Replaces", "Proposed-Replacement"]
    required = ["BIP", "Title", "Authors", "Status", "Type", "Assigned", "License"]
    report("preamble has every BIP 3 required header", all(f in fields for f in required), ", ".join(fields))
    report("preamble headers in BIP 3 order", fields == sorted(fields, key=bip3_order.index))
    title = re.search(r"Title: (.*)", preamble).group(1)
    report("title at most 50 characters", len(title) <= 50, f"{len(title)} characters")
    status = re.search(r"Status: (.*)", preamble).group(1)
    report("status is a BIP 3 value", status in ("Draft", "Complete", "Deployed", "Closed"), status)
    version = re.search(r"Version: (.*)", preamble).group(1)
    report("preamble version equals the draft notice", f"specification version {version}" in readme, version)

    # Links and anchors.
    for path in DOCS:
        base = os.path.dirname(path)
        broken, checked = [], 0
        for target in links(path):
            if target.startswith(("http://", "https://", "mailto:")):
                continue
            checked += 1
            file_part, _, fragment = target.partition("#")
            target_path = os.path.normpath(os.path.join(base, file_part)) if file_part else path
            exists = os.path.exists(target_path)
            ok = exists and (not fragment or not target_path.endswith(".md") or fragment in anchors(target_path))
            if not ok:
                broken.append(target)
        report(f"{path}: every relative link and anchor resolves", not broken,
               f"{checked} checked" + (f", broken {broken}" if broken else ""))

    # Reference list: numbered 1..N, every entry cited in README or the supplement.
    references = readme.split("\n## References\n", 1)[1]
    numbers = [int(n) for n in re.findall(r"^(\d+)\. ", references, flags=re.M)]
    report("references numbered consecutively", numbers == list(range(1, len(numbers) + 1)), f"1..{len(numbers)}")
    body = readme.split("\n## References\n", 1)[0]
    supplement = open("docs/DESIGN-NOTES.md").read()

    def cited(text):
        # Math spans such as $`Feistel^r[32,96]`$ use brackets for parameters, not citations.
        text = re.sub(r"\$`[^`]*`\$", "", text)
        found = set()
        for group in re.findall(r"\[(\d+(?:\]?\s*[-,]\s*\[?\d+)*)\]", text):
            parts = re.split(r"\]?\s*,\s*\[?", group)
            for part in parts:
                if "-" in part:
                    low, high = (int(x.strip("[] ")) for x in part.split("-"))
                    found.update(range(low, high + 1))
                else:
                    found.add(int(part.strip("[] ")))
        return found

    in_readme, in_supplement = cited(body), cited(supplement)
    unknown = (in_readme | in_supplement) - set(numbers)
    report("every citation names an existing reference", not unknown, f"unknown {sorted(unknown)}" if unknown else "")
    uncited = set(numbers) - in_readme - in_supplement
    report("every reference is cited", not uncited, f"uncited {sorted(uncited)}" if uncited else "")
    only_supplement = sorted(set(numbers) - in_readme)
    print(f"INFO  cited in README: {len(in_readme & set(numbers))}; only in the supplement: {only_supplement}")

    # Reading words: first four letters unique; three-letter words that begin longer words.
    words = re.findall(r'"([a-z]+)"', open(sys.argv[1]).read())
    prefixes = {w[:4] for w in words}
    report("first four letters identify every BIP39 word", len(prefixes) == 2048)
    short = [w for w in words if len(w) == 3 and any(o != w and o.startswith(w) for o in words)]
    report("some three-letter words begin longer words (e.g. act)", "act" in short, f"{len(short)} such words")
    ambiguous = []
    for w in words:
        for n in range(4, len(w) + 1):
            prefix = w[:n]
            owners = [o for o in words if o.startswith(prefix)]
            exact = prefix in words
            if not exact and len(owners) != 1:
                ambiguous.append(prefix)
    report("every >=4-letter prefix of a word resolves to exactly one word", not ambiguous,
           f"{len(ambiguous)} ambiguous" if ambiguous else "")

    print(f"summary: {results.count(True)} PASS, {results.count(False)} FAIL")


if __name__ == "__main__":
    main()
