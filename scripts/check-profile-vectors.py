"""Check the JSON forms of the optional profile vectors in vectors/profiles/.

The JSON files must hold the cases of the Markdown tables in vectors/profiles/README.md and match
their SHA256SUMS. The wallet-check digests and the password check words are also recomputed from
their definitions: BIP39 seeds with PBKDF2-HMAC-SHA512 and SHA-256 from Python's standard library,
and the EFF large wordlist. The repair words are compared with the tables only; mhfe-core's tests
recompute them.

Use only public wordlists and test vectors.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import unicodedata

ROOT = Path(__file__).resolve().parent.parent
PROFILES = ROOT / "vectors" / "profiles"
FILES = ("password-check-word.json", "repair-words.json", "wallet-check.json")
EFF_SHA256 = "addd35536511597a02fa0a9ff1e5284677b8883b83e986e43f15a3db996b903e"
WALLET_TAG = b"MHFE-WALLET-CHECK-SEED-1"
WEIGHTS = (1, 5, 7, 11, 13)


def table(readme, heading):
    """The rows of the first table under a level-2 heading, as lists of cells."""
    part = readme.split(f"\n## {heading}\n", 1)[1].split("\n## ", 1)[0]
    lines = [line for line in part.split("\n") if line.startswith("|")][2:]
    return [[cell.strip().strip("`") for cell in line.strip("|").split("|")] for line in lines]


def bip39_words(path):
    words = re.findall(r'"([a-z]+)"', path.read_text(encoding="utf-8"))
    if len(words) != 2048:
        raise ValueError(f"{path} does not hold the 2048 English BIP39 words")
    return words


def eff_words(path):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != EFF_SHA256:
        raise ValueError(f"{path} is not the EFF large wordlist with SHA-256 {EFF_SHA256}")
    return [line.split("\t")[1] for line in data.decode("ascii").split("\n") if line]


def mnemonic(entropy, words):
    bits = int.from_bytes(entropy, "big") << 8 | hashlib.sha256(entropy).digest()[0]
    return " ".join(words[bits >> (11 * (23 - i)) & 0x7FF] for i in range(24))


def wallet_digest(phrase, passphrase, length_field=True):
    """T of MHFE-WALLET-CHECK-SEED-1; without length_field, the control that omits BE32(256)."""
    nfkd = lambda text: unicodedata.normalize("NFKD", text).encode("utf-8")
    seed = hashlib.pbkdf2_hmac("sha512", nfkd(phrase), b"mnemonic" + nfkd(passphrase), 2048, 64)
    length = (256).to_bytes(4, "big") if length_field else b""
    return hashlib.sha256(WALLET_TAG + length + seed).hexdigest()


def read_json(name):
    return json.loads((ROOT / name).read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("wordlist", type=Path, help="public BIP39 English wordlist in Rust source form")
    parser.add_argument("eff", type=Path, help="the EFF large wordlist eff_large_wordlist.txt")
    args = parser.parse_args()
    bip39, eff = bip39_words(args.wordlist), eff_words(args.eff)
    readme = (PROFILES / "README.md").read_text(encoding="utf-8")
    results = []

    def report(passed, message):
        results.append(passed)
        print(f"{'PASS' if passed else 'FAIL'}  {message}")

    lines = (PROFILES / "SHA256SUMS").read_text(encoding="ascii").splitlines()
    sums = {name: digest for digest, name in (line.split("  ", 1) for line in lines)}
    matching = tuple(sorted(sums)) == FILES and all(
        hashlib.sha256((PROFILES / name).read_bytes()).hexdigest() == sums[name] for name in FILES
    )
    report(matching, f"SHA256SUMS lists exactly {', '.join(FILES)} and matches them")
    if not matching:
        return 1
    password, repair, wallet = (read_json(f"vectors/profiles/{name}") for name in FILES)

    # Wallet check: the table's passing rows, then every case and control recomputed.
    rows = [
        (int(counter), "" if passphrase == "empty string" else passphrase, digest)
        for counter, passphrase, digest in table(readme, "Optional wallet check: MHFE-WALLET-CHECK-SEED-1")
    ]
    passing = [(c["counter"], c["bip39_passphrase"], c["digest_hex"]) for c in wallet["cases"] if c["passes"]]
    report(rows == passing, f"the wallet-check JSON holds the {len(rows)} passing rows of the table")
    for case in wallet["cases"] + wallet["controls"]:
        entropy = bytes(24) + case["counter"].to_bytes(8, "big")
        phrase = mnemonic(entropy, bip39)
        digest = wallet_digest(phrase, case["bip39_passphrase"], "omits" not in case)
        passes = digest.startswith("0000")
        recorded = (case["entropy_hex"], case["mnemonic"], case["digest_hex"], case["passes"])
        ok = recorded == (entropy.hex(), phrase, digest, passes)
        report(ok, f"wallet check {case['id']}: digest {digest[:8]}, {'passes' if passes else 'fails'}")

    # Repair words: the table's rows, with each container phrase read from its vector file.
    expected = []
    for container, cards in table(readme, "Repair words: MHFE-REPAIR-1"):
        groups = [group.strip().strip("`") for group in cards.split(" / ")]
        if container.startswith("vectors/"):
            phrase = read_json(container)["container"]
        else:
            phrase = " ".join(["abandon"] * 23 + ["art"])
        expected.append((phrase, {str(len(group.split())): group for group in groups}))
    actual = [(case["container"], case["repair_words"]) for case in repair["cases"]]
    report(actual == expected, f"the repair-word JSON holds the {len(expected)} rows of the table")
    for case in repair["cases"]:
        if "container_vector" in case:
            same = read_json(case["container_vector"])["container"] == case["container"]
            report(same, f"repair case {case['id']}: container matches {case['container_vector']}")
    for example in repair["repairs"]:
        words = next(c for c in repair["cases"] if c["id"] == example["case"])["container"].split()
        positions = set(example["unreadable"]) | {int(p) for p in example["replaced"]}
        restored = {int(p): word for p, word in example["restored"].items()}
        ok = restored == {p: words[p - 1] for p in positions}
        ok = ok and all(words[int(p) - 1] != word for p, word in example["replaced"].items())
        report(ok, f"repair example {example['id']}: the restored words are the container's")

    # Password check word: the table's rows, recomputed, and the erasure examples.
    rows = [
        (dice.split(), int(index), text)
        for dice, index, text in table(readme, "Password check word: MHFE-PASSWORD-CHECK-1")
    ]
    recorded = [(c["dice"], c["check_index"], c["password"]) for c in password["cases"]]
    report(rows == recorded, f"the password-check JSON holds the {len(rows)} rows of the table")
    for case in password["cases"]:
        drawn = [int("".join(str(int(r) - 1) for r in roll), 6) for roll in case["dice"]]
        check = sum(w * d for w, d in zip(WEIGHTS, drawn)) % 7776
        ok = check == case["check_index"] and " ".join(eff[i] for i in drawn + [check]) == case["password"]
        report(ok, f"password check {case['id']}: check index {check}")
    for example in password["erasures"]:
        known = [eff.index(token) if token in eff else None for token in example["input"].split(" ")]
        position = known.index(None)
        # The drawn words weigh 1, 5, 7, 11 and 13 and the check word -1; their sum is 0 mod 7776.
        weights = WEIGHTS + (-1,)
        rest = sum(w * i for at, (w, i) in enumerate(zip(weights, known)) if at != position) % 7776
        value = -rest * pow(weights[position] % 7776, -1, 7776) % 7776
        ok = position + 1 == example["position"] and eff[value] == example["recovered"]
        report(ok, f"password erasure {example['id']}: position {position + 1} recovers {eff[value]}")

    print(f"summary: {sum(results)} PASS, {len(results) - sum(results)} FAIL")
    return 0 if all(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
