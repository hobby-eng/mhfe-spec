"""AUD-007 arithmetic and synthetic Feistel filters; not an attack-cost lower bound."""

import hashlib
import itertools
import json
import math

YEAR = 365.25 * 86400
LIST_SIZE = 7776
PBKDF_RATE = 1500000  # Rounded, explicitly extrapolated scenario in the supplement.
checks = []


def check(name, value, target, tolerance=0.1):
    assert abs(value - target) <= tolerance * target, (name, value, target)
    checks.append({"name": name, "value": value, "target": target, "tolerance": tolerance})


rows = [
    ("two words", LIST_SIZE**2, [(86400, 350), (3600000, 8), (PBKDF_RATE, 20)]),
    ("30 bits", 2**30, [(YEAR, 17), (86400000, 6), (60 * PBKDF_RATE, 6)]),
    ("three words", LIST_SIZE**3, [(YEAR, 7500), (1000 * YEAR, 7.5), (86400 * PBKDF_RATE, 1.8)]),
    ("40 bits", 2**40, [(YEAR, 17000), (1000 * YEAR, 17), (86400 * PBKDF_RATE, 4)]),
    ("four words", LIST_SIZE**4, [(YEAR, 58e6), (1000 * YEAR, 58000), (YEAR * PBKDF_RATE, 39)]),
    ("five words", LIST_SIZE**5, [(YEAR, 4.5e11), (1000 * YEAR, 4.5e8), (YEAR * PBKDF_RATE, 300000)]),
]
for label, space, columns in rows:
    for i, (unit, target) in enumerate(columns):
        check(f"table {label} column {i + 1}", space / 2 / unit, target)
for n, bits in [(2, 25.8), (3, 38.8), (4, 51.7), (5, 64.6)]:
    check(f"entropy {n} words", n * math.log2(LIST_SIZE), bits, 0.003)
for label, space, farm, bot in [("30 bits", 2**30, 60, 18), ("four words", LIST_SIZE**4, 640000, 7000), ("five words", LIST_SIZE**5, 5e9, 54e6)]:
    # The document's '~2 months' is a coarse unit, not a claim of exactly 60 days.
    check(f"farm {label}", space / 2 / 90 / (86400 if label == "30 bits" else YEAR), farm, 0.2 if label == "30 bits" else 0.1)
    check(f"botnet {label}", space / 2 / (1000000 / 120) / (3600 if label == "30 bits" else YEAR), bot)
for label, value, target, tolerance in [
    ("PBKDF2 extrapolation", 3120900 * 1000 / 2048, 1.52e6, 0.003),
    ("memory processed GiB", 12 * 12 * 2, 288, 0),
    ("logical traffic lower TB", 288 * 3 * 2**30 / 1e12, 0.9, 0.04),
    ("logical traffic upper TB", 288 * 4 * 2**30 / 1e12, 1.2, 0.04),
    ("PIM 1023 low hours", 60 * 1024 / 3600, 17, 0.01),
    ("PIM 1023 high hours", 120 * 1024 / 3600, 34, 0.01),
    ("21-word four-EFF-word false matches", LIST_SIZE**4 / 2 / 2**32, 426000, 0.001),
    ("false passphrase searches/MHFE work", LIST_SIZE**5 / PBKDF_RATE / 2**32, 4400, 0.004),
    ("24-word 30-bit pair search years", (2**29 + 2**59 / PBKDF_RATE) / YEAR, 12200, 0.005),
    ("suite4 equal half pair mean", 2**32 * (2**32 - 1) / 2**65, 0.5, 1e-8),
    ("suite4 equal-half Poisson probability", -math.expm1(-(2**32 * (2**32 - 1) / 2**65)), 0.39, 0.01),
    ("suite4 five-EFF-word known-pair false matches", LIST_SIZE**5 / 2**64, 1.5, 0.03),
    ("five words chosen from eight min-entropy", 5 * math.log2(LIST_SIZE) - 3, 61.6, 0.001),
    ("extra EFF word low years", 2 * math.log2(LIST_SIZE), 26, 0.01),
    ("extra EFF word high years", 3 * math.log2(LIST_SIZE), 39, 0.01),
    ("public-salt sidechannel fraction", 0.5 / (12 * 12), 1 / 288, 0),
    ("one missing non-last word mean", 1 + 2047 / 256, 9, 0.001),
    ("two missing non-last words mean", 1 + (2048**2 - 1) / 256, 16400, 0.001),
]:
    check(label, value, target, tolerance)
for speed, bits in [(0.1, 23.8), (1, 20.5), (10, 17.2)]:
    check(f"relative cost bits at {speed}/s", math.log2(PBKDF_RATE / speed), bits, 0.002)
opened = [1 + int(p2 == 0) if p1 == 0 else 1 for p1, p2 in itertools.product(range(2), repeat=2)]
check("adaptive opened containers", sum(opened) / len(opened), 1.25, 0)

for width in (64, 80, 96, 112, 128):
    mask = (1 << width) - 1

    def function(i, right):
        return int.from_bytes(hashlib.sha256(bytes([i]) + right.to_bytes(width // 8, "big")).digest(), "big") & mask

    original = (0x0123456789ABCDEF & mask, 0xFEDCBA9876543210 & mask)
    final = original
    for i in range(12):
        left, right = final
        final = (right, left ^ function(i, right))
    for skipped in range(12):
        left, right = original
        other_left, other_right = final
        calls = 0
        for i in range(skipped):
            left, right = right, left ^ function(i, right)
            calls += 1
        for i in range(11, skipped, -1):
            other_left, other_right = other_right ^ function(i, other_left), other_left
            calls += 1
        assert right == other_left and calls == 11

assert len(checks) == 50
print(json.dumps({"arithmeticAssertions": len(checks), "syntheticAlgebraCases": 60, "argon2Calls": 0, "checks": checks}, indent=2))
