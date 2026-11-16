#!/usr/bin/env python3
"""Builds lean/MhfeCore/Code.lean from the extraction and the translations.

Aeneas writes the extracted definitions to MhfeCore/Extraction/Funs.lean and imports the opaque
items from MhfeCore/Assumptions/FunsExternal.lean, which comes first. The five translated functions
(MhfeCore/Assumptions/Translations.lean) call extracted definitions and are called by others, so they
can sit neither before nor after Funs.lean. This script splits both files into their declaration
blocks (each starts with a `/--` comment) and writes them in dependency order, keeping the
extraction's own order wherever the dependencies allow it.

Checks: every block of Funs.lean that no translated block replaces appears in Code.lean exactly
once and unchanged; every block of Translations.lean appears once; no block comes before a block it
uses. MANIFEST-code.txt records the SHA-256 of the inputs and of Code.lean, and the order of the
blocks; REPLACED-blocks.lean.txt keeps the generated blocks that translated blocks replace.

    splice.py [--extraction DIR] [--record]

DIR holds the generated .lean files to use (default: MhfeCore/Extraction). Without --record, the
new manifest must equal the recorded MANIFEST-code.txt; otherwise nothing is written but
MANIFEST-code.new.txt, and the exit status is 1. With --record, a new MANIFEST-code.txt is written.
The outputs (Code.lean, the replaced blocks, the manifest with --record, and the .lean files of DIR
into MhfeCore/Extraction when DIR is another folder) are first written next to their targets and
then renamed over them, so a failed write leaves the earlier files in place.
"""

import argparse
import hashlib
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "lean")
EXTRACTION = os.path.join(ROOT, "MhfeCore", "Extraction")
TRANS = os.path.join(ROOT, "MhfeCore", "Assumptions", "Translations.lean")
OUT = os.path.join(ROOT, "MhfeCore", "Code.lean")
MANIFEST = os.path.join(ROOT, "MANIFEST-code.txt")
NEW_MANIFEST = os.path.join(ROOT, "MANIFEST-code.new.txt")
REPLACED = os.path.join(ROOT, "REPLACED-blocks.lean.txt")
PRELUDE = os.path.join(ROOT, "MhfeCore", "Assumptions", "CodePrelude.lean.txt")

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:def|impl_def|theorem|abbrev|instance)"
                  r"\s+([^\s(:{\[]+)", re.M)
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def blocks(text):
    """Splits at lines that start a doc comment; returns (prefix, [blocks])."""
    lines = text.splitlines(keepends=True)
    starts = [i for i, line in enumerate(lines) if line.startswith("/--")]
    if not starts:
        return text, []
    prefix = "".join(lines[: starts[0]])
    out = []
    for k, start in enumerate(starts):
        end = starts[k + 1] if k + 1 < len(starts) else len(lines)
        out.append("".join(lines[start:end]))
    return prefix, out


def defined(block):
    # A declaration may put its name on the line after `def`.
    flat = re.sub(r"(def|impl_def|theorem|abbrev)\s*\n\s*", r"\1 ", block)
    names = DECL.findall(flat)
    if not names:
        sys.exit("block without a declaration:\n" + block[:300])
    return names


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_bytes(path):
    with open(path, "rb") as f:
        return f.read()


def read_text(path):
    with open(path, encoding="utf-8", newline="") as f:
        return f.read()


def write(path, text):
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(text)


def main():
    parser = argparse.ArgumentParser(description="Builds MhfeCore/Code.lean.")
    parser.add_argument("--extraction", default=EXTRACTION)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    types_bytes = read_bytes(os.path.join(args.extraction, "Types.lean"))
    funs_bytes = read_bytes(os.path.join(args.extraction, "Funs.lean"))
    trans_bytes = read_bytes(TRANS)
    funs_text = funs_bytes.decode("utf-8")
    if "namespace mhfe_core\n" not in funs_text or "end mhfe_core" not in funs_text:
        sys.exit("Funs.lean has no namespace mhfe_core")
    head, body = funs_text.split("namespace mhfe_core\n", 1)
    body, tail = body.rsplit("end mhfe_core", 1)
    _, extracted = blocks(body)
    _, translated = blocks(trans_bytes.decode("utf-8"))
    # A translated block that defines a name of an extracted block replaces that block; the
    # replaced blocks are written to REPLACED for review.
    extracted_names = {n: i for i, b in enumerate(extracted) for n in defined(b)}
    replaced = []
    for b in translated:
        for n in defined(b):
            if n in extracted_names:
                replaced.append((n, extracted[extracted_names[n]]))
    replaced_names = {n for n, _ in replaced}
    allb = [("E", b) for b in extracted if not (set(defined(b)) & replaced_names)] + \
        [("R" if set(defined(b)) & replaced_names else "T", b) for b in translated]
    replaced_text = ("-- The generated blocks that Translations.lean replaces (not compiled).\n\n"
                     + "".join(b for _, b in replaced))
    names = {}
    for idx, (_, b) in enumerate(allb):
        for n in defined(b):
            if n in names:
                sys.exit(f"{n} is defined twice")
            names[n] = idx
    deps = []
    for idx, (_, b) in enumerate(allb):
        uses = {names[t] for t in TOKEN.findall(b) if t in names and names[t] != idx}
        deps.append(uses)
    # Kahn's algorithm, taking the lowest original index first (translations count after the
    # extraction, so an extracted block keeps its place unless it needs a translation).
    remaining = set(range(len(allb)))
    order = []
    while remaining:
        ready = sorted(i for i in remaining if not (deps[i] & remaining))
        if not ready:
            sys.exit("circular dependency among: " + ", ".join(
                defined(allb[i][1])[0] for i in sorted(remaining)))
        order.append(ready[0])
        remaining.remove(ready[0])
    placed = set()
    for i in order:
        if deps[i] - placed:
            sys.exit("ordering error")
        placed.add(i)
    head = head.replace("public import MhfeCore.Extraction.FunsExternal",
                        "public import MhfeCore.Assumptions.FunsExternal")
    head = ("-- Built by tools/splice.py from MhfeCore/Extraction/Funs.lean (generated by Aeneas) and\n"
            "-- MhfeCore/Assumptions/Translations.lean (written by hand); do not edit.\n") + head
    prelude = read_text(PRELUDE)
    out_text = (head + "namespace mhfe_core\n\n" + prelude + "".join(allb[i][1] for i in order)
                + "end mhfe_core" + tail)
    for kind, b in allb:
        if out_text.count(b) != 1:
            sys.exit("a block does not appear exactly once:\n" + b[:300])
    code_sha = sha256(out_text.encode("utf-8"))
    manifest = (f"Types.lean         {sha256(types_bytes)}\n"
                f"Funs.lean          {sha256(funs_bytes)}\n"
                f"Translations.lean  {sha256(trans_bytes)}\n"
                f"Code.lean          {code_sha}\n\n"
                "Order (E extracted, T translated, R translated in place of a generated block):\n"
                + "".join(f"{allb[i][0]} {defined(allb[i][1])[0]}\n" for i in order))
    summary = (f"Code.lean: {len(extracted)} extracted blocks, {len(translated)} translated blocks, "
               f"{len(replaced)} of them in place of generated ones")
    if not args.record:
        recorded = read_text(MANIFEST) if os.path.exists(MANIFEST) else ""
        if manifest != recorded:
            write(NEW_MANIFEST, manifest)
            sys.exit(f"{summary}\nthe result differs from {os.path.basename(MANIFEST)}; the new "
                     f"manifest is in {os.path.basename(NEW_MANIFEST)} and nothing else was written")
    outputs = {}
    stale = []
    if os.path.realpath(args.extraction) != os.path.realpath(EXTRACTION):
        for name in sorted(os.listdir(args.extraction)):
            if name.endswith(".lean"):
                outputs[os.path.join(EXTRACTION, name)] = read_bytes(os.path.join(args.extraction, name))
        stale = [os.path.join(EXTRACTION, name) for name in sorted(os.listdir(EXTRACTION))
                 if name.endswith(".lean") and os.path.join(EXTRACTION, name) not in outputs]
    outputs[REPLACED] = replaced_text.encode("utf-8")
    outputs[OUT] = out_text.encode("utf-8")
    if args.record:
        outputs[MANIFEST] = manifest.encode("utf-8")
    try:
        for path, data in outputs.items():
            with open(path + ".splice-tmp", "wb") as f:
                f.write(data)
    except OSError:
        for path in outputs:
            if os.path.exists(path + ".splice-tmp"):
                os.remove(path + ".splice-tmp")
        raise
    for path in outputs:
        os.replace(path + ".splice-tmp", path)
    for path in stale:
        os.remove(path)
    if os.path.exists(NEW_MANIFEST):
        os.remove(NEW_MANIFEST)
    print(summary + ("; recorded in " if args.record else "; equal to ")
          + os.path.basename(MANIFEST))


if __name__ == "__main__":
    main()
