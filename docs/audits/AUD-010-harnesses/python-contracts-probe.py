"""AUD-010 bounded public-input probes; never execute an Argon2 implementation."""

import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import resource
import sys

resource.setrlimit(resource.RLIMIT_AS, (192 * 1024 * 1024,) * 2)
resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT.parent / "workingspace/mhfe-python"))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


suite3 = load("audit_suite3", ROOT / "scripts/independent-suite3.py")
suite4 = load("audit_suite4", ROOT / "scripts/independent-suite4.py")
results = []


class ArgonBoundary(Exception):
    pass


def cli_case(label, module, arguments, public_input):
    calls = []

    def boundary(password, salt, pim, level):
        calls.append({"pim": pim, "memory_level": level, "salt_bytes": len(salt)})
        raise ArgonBoundary("stopped before Argon2")

    helper = module if module is suite3 else module.suite3
    original_argon, original_stdin = helper.openssl_argon2id, sys.stdin
    helper.openssl_argon2id = boundary
    sys.stdin = io.StringIO(public_input)
    output, error = io.StringIO(), io.StringIO()
    exception = None
    try:
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(error):
            module.main(arguments)
    except BaseException as caught:
        exception = {"type": type(caught).__name__, "message": str(caught)}
    finally:
        helper.openssl_argon2id, sys.stdin = original_argon, original_stdin
    results.append({"case": label, "arguments": arguments, "argon_boundary_calls": calls,
                    "exception": exception, "stdout": output.getvalue()})


def load_public(name):
    return json.loads((ROOT / name).read_text())


if len(sys.argv) > 1 and sys.argv[1] == "tampered-fixture":
    # No disk mutation: change an expected mask in a published positive transcript in memory.
    import unittest.mock
    suite = int(sys.argv[2])
    module = suite3 if suite == 3 else suite4
    name = "vectors/suite3/zero-12.json" if suite == 3 else "vectors/suite4/same-length-nonzero-12.json"
    vector = load_public(name)
    mask = vector["encryption"]["rounds"][0]["mask_hex"]
    vector["encryption"]["rounds"][0]["mask_hex"] = ("1" if mask[0] != "1" else "0") + mask[1:]
    with unittest.mock.patch("builtins.open", return_value=io.StringIO(json.dumps(vector))):
        module.main(["vector", "--trust-argon2-keys", "public-in-memory-tampered.json"])
    raise SystemExit(0)

v3 = load_public("vectors/suite3/zero-12.json")
v4 = load_public("vectors/suite4/same-length-nonzero-12.json")
p3, p4 = v3["inputs"]["phrase"], v4["inputs"]["phrase"]
password = "public audit password"
new = lambda phrase: phrase + "\n" + password + "\n" + password + "\n"
old = lambda phrase: phrase + "\n" + password + "\n"
cli_case("suite3-three-word-source", suite3, ["encrypt"], new("abandon abandon ability"))
for suite, module, vector in ((3, suite3, v3), (4, suite4, v4)):
    for operation in ("encrypt", "decrypt"):
        for pim, level in ((1024, 0), (0, 22)):
            args = [operation] + (["0"] if suite == 3 and operation == "decrypt" else [])
            args += [str(pim), str(level)]
            text = new(vector["inputs"]["phrase"]) if operation == "encrypt" else old(vector["container"])
            cli_case(f"suite{suite}-{operation}-pim{pim}-mem{level}", module, args, text)
cli_case("suite3-invalid-selected-count", suite3, ["decrypt", "13"], old(v3["container"]))
cli_case("suite3-invalid-checksum", suite3, ["encrypt"], new(" ".join(["abandon"] * 12)))
cli_case("suite4-invalid-checksum", suite4, ["encrypt"], new(" ".join(["abandon"] * 12)))
cli_case("suite3-short-container", suite3, ["decrypt"], old(p3))
cli_case("suite4-24-word-container", suite4, ["decrypt"], old(suite3.entropy_to_phrase(bytes(32))))

ambiguous = bytes.fromhex("4d48464520616d62000000004dda455a85b22f09e43e0ae5de9322dce19210ad")
results.append({"case": "stated-ambiguous-lengths", "all_matches": suite3.matching_short_lengths(ambiguous),
                "returned_lengths": [r[0] for r in suite3.stated_recovery(ambiguous, 12, "")]})
results.append({"case": "three-word-decoding", "entropy_hex": suite3.phrase_to_entropy("abandon abandon ability").hex()})
results.append({"case": "defaults", "settings3": suite3.settings([], 3),
                "memory_kib": suite3.memory_kib(0), "passes": suite3.passes(0)})

# Published positive transcripts use recorded Argon2 keys. A real KDF is forbidden here.
def forbid_argon(*args):
    raise RuntimeError("AUD-010 prohibits Argon2 execution")

suite3.openssl_argon2id = forbid_argon
suite4.suite3.openssl_argon2id = forbid_argon
if not sys.flags.optimize:
    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        suite3.check_password_cases(str(ROOT / "vectors/unicode18/password-encoding.json"))
        suite3.check_password_cases(str(ROOT / "vectors/suite3/validation-cases.json"))
        suite4.check_validation_cases(str(ROOT / "vectors/suite4/validation-cases.json"))
        counts = {}
        for suite, module in ((3, suite3), (4, suite4)):
            paths = sorted(p for p in (ROOT / f"vectors/suite{suite}").glob("*.json")
                           if p.name not in ("negative-cases.json", "validation-cases.json"))
            checked = module.check_files([str(p) for p in paths], True)
            counts[str(suite)] = len(checked)
    results.append({"case": "fast-checks", "password_cases": 41, "suite4_ent_cases": 4,
                    "suite4_refusals_table_consistency_only": 63, "positive_transcripts": counts,
                    "argon_execution": False})

admission_failures = [item["case"] for item in results if item.get("argon_boundary_calls")]
print(json.dumps({"optimization": sys.flags.optimize, "unicode_version": suite3.unicode18.unidata_version,
                  "results": results, "admission_failures": admission_failures}, indent=2))
# Every cli_case above is an invalid input that must be refused before the KDF.
# The raw exploratory probe is retained unchanged in local evidence; this
# published harness also signals the baseline contract failures to its caller.
raise SystemExit(1 if admission_failures else 0)
