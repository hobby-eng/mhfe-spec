"""Independent, public-data profile arithmetic for AUD-007; no Argon2 calls."""

import hashlib
import json
import math
import re
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
WORDLIST = ROOT.parent / "workingspace/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bip39-3.0.0/src/language/english.rs"
EFF = ROOT.parent / "mhfe/vendor/eff-large-wordlist/eff_large_wordlist.txt"
FIELD_POLYNOMIAL = 0x805  # x^11 + x^2 + 1
FIELD_SIZE = 2048
WEIGHTS = (1, 5, 7, 11, 13)
DOMAIN = b"MHFE-WALLET-CHECK-SEED-1"
words = re.findall(r'"([a-z]+)"', WORDLIST.read_text())
assert len(words) == FIELD_SIZE
assert hashlib.sha256(("\n".join(words) + "\n").encode()).hexdigest() == "2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda"


def mnemonic(entropy):
    width = len(entropy) * 8
    checksum_width = width // 32
    bits = (int.from_bytes(entropy, "big") << checksum_width) | (hashlib.sha256(entropy).digest()[0] >> (8 - checksum_width))
    return " ".join(words[(bits >> shift) & 2047] for shift in range(width + checksum_width - 11, -1, -11))


def seed(phrase, passphrase):
    return hashlib.pbkdf2_hmac("sha512", unicodedata.normalize("NFKD", phrase).encode(), b"mnemonic" + unicodedata.normalize("NFKD", passphrase).encode(), 2048)


phrase = mnemonic(bytes(16))
assert seed(phrase, "TREZOR").hex() == "c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04"
digests = []
for counter, passphrase, expected in (
    (76562, "TREZOR", "0000e86481bdfe6dbf45e6e41fba4f309fcf09d3f0af2fe3f46736c663840853"),
    (98918, "", "0000ede77b44fbd62025e1d36a45ebe3846cf48f7b3e76ca6a91495fdadc1fb2"),
):
    material = seed(mnemonic(bytes(24) + counter.to_bytes(8, "big")), passphrase)
    actual = hashlib.sha256(DOMAIN + (256).to_bytes(4, "big") + material).hexdigest()
    assert actual == expected
    digests.append(actual)
for counter, passphrase, prefix in ((76562, "", "ebd07f71"), (98918, "TREZOR", "8d2b97fb")):
    assert hashlib.sha256(DOMAIN + (256).to_bytes(4, "big") + seed(mnemonic(bytes(24) + counter.to_bytes(8, "big")), passphrase)).hexdigest().startswith(prefix)
assert hashlib.sha256(DOMAIN + seed(mnemonic(bytes(24) + (76562).to_bytes(8, "big")), "TREZOR")).hexdigest().startswith("f2c9f765")

assert hashlib.sha256(EFF.read_bytes()).hexdigest() == "addd35536511597a02fa0a9ff1e5284677b8883b83e986e43f15a3db996b903e"
eff_rows = [line.split("\t") for line in EFF.read_text().splitlines()]
assert len(eff_rows) == 7776
assert sorted(word for _, word in eff_rows if "-" in word) == ["drop-down", "felt-tip", "t-shirt", "yo-yo"]
for index, (dice, _) in enumerate(eff_rows):
    assert sum((int(digit) - 1) * 6 ** (4 - i) for i, digit in enumerate(dice)) == index
for rolls, expected_index, expected_phrase in (
    ("11111 11112 11113 11114 11115", 104, "abacus abdomen abdominal abide abiding aids"),
    ("66666 66666 66666 66666 66666", 7739, "zoom zoom zoom zoom zoom yelling"),
    ("35214 62431 15543 44126 21365", 4150, "jovial trailing chokehold pavilion cresting ninth"),
    ("24255 61534 11111 66622 26522", 5527, "drop-down t-shirt abacus yo-yo felt-tip rubble"),
):
    indices = [sum((int(digit) - 1) * 6 ** (4 - i) for i, digit in enumerate(dice)) for dice in rolls.split()]
    check = sum(weight * value for weight, value in zip(WEIGHTS, indices)) % 7776
    assert check == expected_index
    assert " ".join(eff_rows[i][1] for i in indices + [check]) == expected_phrase
    for erased in range(6):
        row = indices + [check]
        if erased == 5:
            restored = sum(weight * value for weight, value in zip(WEIGHTS, row)) % 7776
        else:
            restored = ((check - sum(WEIGHTS[i] * row[i] for i in range(5) if i != erased)) * pow(WEIGHTS[erased], -1, 7776)) % 7776
        assert restored == row[erased]
assert [math.gcd(b - a, 7776) - 1 for a, b in zip(WEIGHTS + (-1,), (WEIGHTS + (-1,))[1:])] == [3, 1, 3, 1, 1]


def mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & FIELD_SIZE:
            a ^= FIELD_POLYNOMIAL
    return result


def power(a, exponent):
    result = 1
    while exponent:
        if exponent & 1:
            result = mul(result, a)
        a = mul(a, a)
        exponent >>= 1
    return result


assert len({power(2, i) for i in range(FIELD_SIZE - 1)}) == FIELD_SIZE - 1


def generator(k):
    coefficients = [1]
    for exponent in range(1, k + 1):
        updated = [0] * (len(coefficients) + 1)
        for i, value in enumerate(coefficients):
            updated[i] ^= value
            updated[i + 1] ^= mul(value, power(2, exponent))
        coefficients = updated
    return coefficients


expected_generators = {2: [1, 6, 8], 4: [1, 30, 216, 960, 1024], 6: [1, 126, 1181, 1719, 2029, 1077, 1034], 8: [1, 510, 1509, 1770, 1837, 850, 1339, 600, 680]}
for k, coefficients in expected_generators.items():
    assert generator(k) == coefficients


def parity(data, k):
    dividend = data + [0] * k
    coefficients = generator(k)
    for i in range(len(data)):
        factor = dividend[i]
        for j, coefficient in enumerate(coefficients):
            dividend[i + j] ^= mul(factor, coefficient)
    return dividend[-k:]


cards = (
    ("vectors/suite3/zero-12.json", ("labor extra", "shaft pupil patient jewel", "credit buzz orbit tired sail coffee", "appear include vicious move uphold tiger song satoshi")),
    ("vectors/suite4/same-length-nonzero-12.json", ("motor renew", "pitch lonely onion erode", "toe rather ribbon run enforce notice", "tilt object execute change cube domain vehicle hour")),
    ("vectors/suite4/same-length-nonzero-21.json", ("glove blossom", "share mask pave crystal", "slow issue fame census cabbage clarify", "potato enemy similar myself check gesture fortune shiver")),
)
# The published vector tables use these container names; fail if the fixture contract changes.
for relative, expected_cards in cards:
    vector = json.loads((ROOT / relative).read_text())
    container = vector["container"]
    data = [words.index(word) for word in container.split()]
    for k, expected in zip((2, 4, 6, 8), expected_cards):
        assert " ".join(words[i] for i in parity(data, k)) == expected
data = [words.index(word) for word in ("abandon " * 23 + "art").split()]
for k, expected in zip((2, 4, 6, 8), ("clever gravity", "letter wealth borrow cable", "clap try lift setup innocent gather", "mirror coffee census note proof zebra begin barrel")):
    assert " ".join(words[i] for i in parity(data, k)) == expected

print(json.dumps({"result": "passed", "bip39Anchor": 1, "fullSourceDigests": len(digests), "negativeSourceDigests": 3, "effRows": 7776, "passwordVectors": 4, "erasedPasswordPositions": 24, "generatorPolynomials": 4, "parityCards": 16, "argon2Calls": 0}))
