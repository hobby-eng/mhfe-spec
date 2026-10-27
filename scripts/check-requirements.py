"""Check the requirement identifiers of the specification.

Every sentence that states a requirement with MUST, SHOULD, REQUIRED, RECOMMENDED or SHALL in
capitals, with or without NOT, ends with exactly one identifier <sup>CODE-n</sup>, and no other
sentence carries one. Requirements stand in paragraphs and list items, never in headings, tables
or block quotes. Each identifier is unique, its code is the one that the appendix "Requirement
identifiers" gives for the section holding the sentence, and the appendix lists every number in
use for each code, together with the retired ones. Every <sup> element is such an identifier.

With --self-test, the check also runs on altered copies of the document. Each copy breaks one rule
and must fail exactly the checks for that rule.
"""

import argparse
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
KEY_WORD = re.compile(r"\b(MUST|SHOULD|REQUIRED|RECOMMENDED|SHALL)\b")
MARKER = re.compile(r"<sup>([A-Z][A-Z0-9]*)-([1-9][0-9]*)</sup>")
SUP = re.compile(r"<sup>[^<]*</sup>")
CODE_SPAN = re.compile(r"`+[^`]*`+")
# Final punctuation, closing quotes, brackets or emphasis, then an identifier, a space or the end.
SENTENCE_END = re.compile(r"[.!?][\"')\]*_]*(?=<sup>|\s|$)")
ABBREVIATIONS = ("e.g.", "i.e.", "etc.", "vs.", "et al.", "cf.")
APPENDIX = "Appendix: Requirement identifiers"
BOILERPLATE = "The key words **MUST**"


def slug(title):
    """The anchor that GitHub and the PDF build give a heading."""
    plain = re.sub(r"[`*_]", "", title).lower()
    return re.sub(r"[^\w\- ]", "", plain).replace(" ", "-")


def without_fences(lines):
    """The lines with fenced blocks blanked, so that line numbers stay valid."""
    kept, fence = [], False
    for line in lines:
        if line.startswith("```"):
            fence = not fence
            kept.append("")
        else:
            kept.append("" if fence else line)
    return kept


def headings(lines):
    found, seen = [], {}
    for number, line in enumerate(lines, 1):
        match = re.match(r"^(#{1,6}) (.*)", line)
        if match:
            base = slug(match.group(2))
            count = seen.get(base, 0)
            seen[base] = count + 1
            anchor = f"{base}-{count}" if count else base
            found.append((number, len(match.group(1)), match.group(2), anchor))
    return found


def appendix_table(lines, heads):
    """The codes of the appendix: code -> (anchor, numbers in use, retired numbers).

    A cell reads "none", "`X-1`" or "`X-1` to `X-n`", optionally followed by
    "; retired: `X-k`, `X-m`" for numbers within that range that are no longer used.
    """
    start = next((number for number, _, title, _ in heads if title == APPENDIX), None)
    if start is None:
        raise ValueError(f'no heading "{APPENDIX}"')
    codes = {}
    for line in lines[start:]:
        if line.startswith("#"):
            break
        row = re.match(r"^\| `([A-Z][A-Z0-9]*)` +\| \[[^\]]+\]\(#([^)]+)\) +\| (.*?) *\|$", line)
        if not row:
            continue
        code, anchor, cell = row.groups()
        in_use, retired = cell.split("; retired: ") if "; retired: " in cell else (cell, "")
        if in_use == "none":
            numbers = set()
        else:
            bounds = re.fullmatch(rf"`{code}-(\d+)`(?: to `{code}-(\d+)`)?", in_use)
            if not bounds:
                raise ValueError(f"unreadable identifiers for {code}: {cell}")
            numbers = set(range(int(bounds.group(1)), int(bounds.group(2) or bounds.group(1)) + 1))
        gone = {int(n) for n in re.findall(rf"`{code}-(\d+)`", retired)}
        if not gone <= numbers:
            raise ValueError(f"retired identifiers outside the range of {code}: {cell}")
        if code in codes:
            raise ValueError(f"code {code} is listed twice")
        codes[code] = (anchor, numbers - gone, gone)
    if not codes:
        raise ValueError("the appendix lists no codes")
    return codes


def blocks(lines):
    """Paragraphs and list items outside headings, tables and block quotes: (first line, text)."""
    found, current = [], None
    for number, line in enumerate(lines, 1):
        if not line.strip() or line.startswith(("#", "|", ">")):
            current = None
            continue
        item = re.match(r"^\s*([-*]|\d+\.)\s", line)
        if item or current is None:
            current = [number, line.strip()]
            found.append(current)
        else:
            current[1] += " " + line.strip()
    return found


def sentences(text):
    """The sentences of a block; an identifier stays with the sentence it follows."""
    protected = [match.span() for match in CODE_SPAN.finditer(text)]
    protected += [match.span() for match in SUP.finditer(text)]
    start = 0
    for match in SENTENCE_END.finditer(text):
        if any(begin <= match.start() < end for begin, end in protected):
            continue
        marker = MARKER.match(text, match.end())
        if not marker and text[: match.start() + 1].endswith(ABBREVIATIONS):
            continue
        end = marker.end() if marker else match.end()
        yield text[start:end].strip()
        start = end
    if text[start:].strip():
        yield text[start:].strip()


def has_key_word(text):
    return KEY_WORD.search(SUP.sub("", CODE_SPAN.sub("", text))) is not None


def check(document):
    """Return (name, passed, message, details) for each check of the document text."""
    lines = without_fences(document.split("\n"))
    heads = headings(lines)
    try:
        codes = appendix_table(lines, heads)
    except ValueError as error:
        return [("appendix", False, f"the appendix is readable: {error}", [])]
    by_anchor = {anchor: code for code, (anchor, _, _) in codes.items()}
    anchors = {anchor for _, _, _, anchor in heads}

    def code_at(number):
        """The code of the innermost section around a line, walking out through uncoded headings."""
        level = 7
        for head_line, head_level, _, anchor in reversed(heads):
            if head_line > number or head_level >= level:
                continue
            if anchor in by_anchor:
                return by_anchor[anchor]
            level = head_level
        return None

    unmarked, misplaced, used, seen = [], [], {}, 0
    for number, text in blocks(lines):
        parts = list(sentences(text))
        if text.startswith(BOILERPLATE):
            parts = parts[1:]
        for sentence in parts:
            markers = MARKER.findall(sentence)
            seen += len(markers)
            if not has_key_word(sentence):
                if markers:
                    unmarked.append(f"line {number}: an identifier after a sentence without a key word")
                continue
            if len(markers) != 1:
                unmarked.append(f"line {number}: a requirement sentence with {len(markers)} identifiers")
                continue
            if not re.search(MARKER.pattern + "$", sentence):
                unmarked.append(f"line {number}: the identifier does not end its sentence")
            code, value = markers[0]
            section = code_at(number)
            if code != section:
                misplaced.append(f"line {number}: {code}-{value} in a section of code {section}")
            used.setdefault((code, int(value)), []).append(number)

    elsewhere = [
        f"line {number}: state requirements in a paragraph or list item"
        for number, line in enumerate(lines, 1)
        if line.startswith(("#", "|", ">")) and has_key_word(line)
    ]
    text = "\n".join(lines)
    outside = len(MARKER.findall(text)) - seen
    stray = [f"{outside} identifiers outside a paragraph or list item"] if outside else []
    malformed = [tag.group(0) for tag in SUP.finditer(text) if not MARKER.fullmatch(tag.group(0))]
    stray += [f"not an identifier: {tag}" for tag in malformed]
    twice = sorted(f"{code}-{value}" for (code, value), found in used.items() if len(found) > 1)
    mismatched = []
    for code, (_, numbers, gone) in sorted(codes.items()):
        actual = {value for (other, value) in used if other == code}
        if actual != numbers:
            mismatched.append(f"{code}: appendix {sorted(numbers)}, text {sorted(actual)}")
        if actual & gone:
            mismatched.append(f"{code}: retired identifiers in use {sorted(actual & gone)}")
    unknown = sorted({code for code, _ in used} - set(codes))
    if unknown:
        mismatched.append(f"codes missing from the appendix: {', '.join(unknown)}")
    missing = sorted(anchor for anchor in by_anchor if anchor not in anchors)
    checks = [
        ("sections", "every appendix section exists", missing),
        ("sentences", f"every requirement sentence ends with one identifier: {len(used)}", unmarked),
        ("codes", "every identifier has the code of its section", misplaced),
        ("unique", "identifiers are unique", twice),
        ("placement", "no heading, table or block quote states a requirement", elsewhere),
        ("stray", "every <sup> is an identifier in a paragraph or list item", stray),
        ("appendix", "the appendix lists exactly the identifiers in use", mismatched),
    ]
    return [(name, not details, message, details) for name, message, details in checks]


def altered(document):
    """Copies of the document, each breaking one rule, with the checks each one must fail."""

    def change(text, old, new):
        return text.replace(old, new, 1) if text and old in text else None

    def last(code):
        return max((int(n) for c, n in MARKER.findall(document) if c == code), default=0)

    pw, app = last("PW"), last("APP")
    short = change(document, f"`PW-1` to `PW-{pw}`", f"`PW-1` to `PW-{pw - 1}`")
    foreign = change(short, f"<sup>PW-{pw}</sup>", f"<sup>APP-{app + 1}</sup>")
    foreign = change(foreign, f"`APP-{app}` |", f"`APP-{app + 1}` |")
    no_key_word = "in its section."
    bcp14 = "[12], [13]."
    kdf = next((line for line in document.split("\n") if line.startswith("| KDF ")), None)
    table = lambda new: change(document, kdf, kdf.replace("output", new, 1)) if kdf else None
    return [
        ("an identifier removed", {"sentences"}, change(short, f"<sup>PW-{pw}</sup>", "")),
        ("an identifier repeated", {"unique"}, change(short, f"PW-{pw}</sup>", f"PW-{pw - 1}</sup>")),
        ("an identifier under another code", {"codes"}, foreign),
        (
            "an identifier after a sentence without a key word",
            {"sentences"},
            change(document, no_key_word, no_key_word + "<sup>CON-2</sup>"),
        ),
        (
            "an identifier before the final period",
            {"sentences"},
            change(document, "boundaries.<sup>CON-1</sup>", "boundaries<sup>CON-1</sup>."),
        ),
        (
            "an unmarked requirement after the BCP 14 sentence",
            {"sentences"},
            change(document, bcp14, bcp14 + " Readers MUST know them."),
        ),
        ("a requirement in a table", {"placement"}, table("output MUST")),
        ("an identifier in a table", {"stray"}, table("output<sup>PCK-2</sup>")),
        ("a malformed identifier", {"stray"}, change(document, no_key_word, no_key_word + "<sup>X</sup>")),
        ("a shorter appendix range", {"appendix"}, change(document, f"APP-{app}` |", f"APP-{app - 1}` |")),
        (
            "a retired identifier outside the range",
            {"appendix"},
            change(document, "| `PCK-1` ", "| `PCK-1`; retired: `PCK-9` "),
        ),
        ("a renamed section", {"sections", "codes"}, change(document, "# Packing\n", "# Packed\n")),
    ]


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("document", type=Path, nargs="?", default=ROOT / "README.md")
    parser.add_argument(
        "--self-test", action="store_true", help="also check that altered copies are refused"
    )
    args = parser.parse_args()
    document = args.document.read_text(encoding="utf-8")
    results = check(document)
    for _, passed, message, details in results:
        print(f"{'PASS' if passed else 'FAIL'}  {message}")
        for detail in details[:20]:
            print(f"        {detail}")
    ok = all(passed for _, passed, _, _ in results)
    if args.self_test:
        for name, expected, copy in altered(document):
            failed = {key for key, passed, _, _ in check(copy) if not passed} if copy else None
            refused = failed == expected
            outcome = sorted(failed) if failed is not None else "no copy made"
            note = "" if refused else f": failed {outcome}"
            print(f"{'PASS' if refused else 'FAIL'}  refuses a copy with {name}{note}")
            ok = ok and refused
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
