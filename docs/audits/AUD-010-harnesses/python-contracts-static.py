"""AUD-010 supplementary bounded static and public-profile checks, without Argon2."""

import ast
import hashlib
import importlib.metadata
import importlib.util
import json
from pathlib import Path
import re
import resource
import sys
import unicodedata

resource.setrlimit(resource.RLIMIT_AS, (192 * 1024 * 1024,) * 2)
resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
sys.dont_write_bytecode = True
root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root.parent / "workingspace/mhfe-python"))


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


suite3 = load("audit_static_suite3", root / "scripts/independent-suite3.py")
profile = load("audit_static_profile", root / "scripts/check-profile-vectors.py")
syntax = []
creation = []
for path in sorted((root / "scripts").glob("*.py")):
    tree = ast.parse(path.read_text())
    syntax.append({"path": str(path.relative_to(root)), "status": "parsed"})
    if path.name.startswith("independent-suite"):
        names = {}
        for optimization in (0, 1):
            compiled = compile(tree, str(path.relative_to(root)), "exec", optimize=optimization)
            function = next(c for c in compiled.co_consts if hasattr(c, "co_name") and c.co_name == "encrypt")
            names[str(optimization)] = function.co_names
        creation.append({"path": str(path.relative_to(root)), "encrypt_globals_by_optimization": names})

rust = root.parent / "workingspace/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bip39-3.0.0/src/language/english.rs"
words = (root / "scripts/bip39-english.txt").read_text().splitlines()
wordlist = {"words": len(words), "matches_bip39_crate_3": words == re.findall(r'"([a-z]+)"', rust.read_text()),
            "sha256": hashlib.sha256((root / "scripts/bip39-english.txt").read_bytes()).hexdigest()}
requirements = (root / "scripts/independent-suite3-requirements.txt").read_text()
pins = []
for block in re.split(r"\n(?=[a-z][a-z0-9-]*==)", requirements):
    pin = re.search(r"^([a-z][a-z0-9-]*)==([^\s\\]+)", block, re.M)
    if pin:
        hashes = re.findall(r"--hash=sha256:([a-f0-9]+)", block)
        pins.append({"name": pin[1], "version": pin[2], "hashes": len(hashes),
                     "all_hash_lengths_64": bool(hashes) and all(len(h) == 64 for h in hashes)})

wallet = json.loads((root / "vectors/profiles/wallet-check.json").read_text())
case = next(c for c in wallet["cases"] if c["id"] == "counter-98918-empty")
state = bytes.fromhex(case["entropy_hex"])
reading = suite3.detected_recovery(state)
phrase = case["mnemonic"]
old_digest = profile.wallet_digest(phrase, "\u209d")
new_digest = profile.wallet_digest(phrase, "w")
print(json.dumps({"syntax": syntax, "creation": creation, "wordlist": wordlist, "dependency_pins": pins,
                  "runtime_unicode": unicodedata.unidata_version,
                  "password_unicode": suite3.unicode18.unidata_version,
                  "unicode18_u209d_nfkd": suite3.unicode18.normalize("NFKD", "\u209d"),
                  "profile_unicode_counterexample": {"input_codepoint": "U+209D", "checker_digest": old_digest,
                       "unicode18_expected_digest": new_digest, "equal": old_digest == new_digest,
                       "scope": "helper only; all current profile Q fixtures are ASCII"},
                  "profile_recovery_result": {"public_fixture": case["id"], "known_digest": case["digest_hex"],
                       "readings": [{"words": r[0], "verified": r[1]} for r in reading],
                       "wallet_check_field_present": False},
                  "cross_length_public_state": {"state_hex": suite3.pack(bytes(16)).hex(),
                       "source_24_words": suite3.entropy_to_phrase(suite3.pack(bytes(16))),
                       "default_recovery_lengths": [r[0] for r in suite3.detected_recovery(suite3.pack(bytes(16)))]},
                  "metadata_versions": {name: importlib.metadata.version(name) for name in ("cryptography", "cffi", "pycparser", "unicodedata2")}}, indent=2))
