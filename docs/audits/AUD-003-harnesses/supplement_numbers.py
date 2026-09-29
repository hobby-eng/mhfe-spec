"""AUD-003 audit harness: recomputes the figures of the supplement's Part I tables.

Same cost model as the supplement: one MHFE guess per second per card, 1.5 million BIP39
passphrase guesses per second per card, half of the space searched on average.
"""

import math

YEAR = 365.25 * 24 * 3600
DAY = 24 * 3600
PBKDF2 = 1.5e6
results = []


def report(label, stated, computed, ok):
    results.append(ok)
    print(f"{'PASS' if ok else 'CHECK'}  {label}: stated {stated}; computed {computed}")


def near(value, target, tolerance=0.1):
    return abs(value - target) <= tolerance * target


half = {"30 bits": 2**30 / 2, "40 bits": 2**40 / 2, "four words": 7776**4 / 2, "five words": 7776**5 / 2}

report("288 GiB per guess", "12 calls x 2 GiB x 12 passes", 12 * 2 * 12, 12 * 2 * 12 == 288)
tb = (288 * 3 * 2**30 / 1e12, 288 * 4 * 2**30 / 1e12)
report("logical access per guess", "roughly 0.9 to 1.2 TB", f"{tb[0]:.2f} to {tb[1]:.2f} TB",
       near(tb[0], 0.9) and near(tb[1], 1.2))
report("40 bits, one card", "~17,000 years", f"{half['40 bits'] / YEAR:,.0f}", near(half["40 bits"] / YEAR, 17000))
report("40 bits, 1,000 cards", "~17 years", f"{half['40 bits'] / 1000 / YEAR:.1f}", near(half["40 bits"] / 1000 / YEAR, 17))
report("30 bits, BIP39 passphrase", "~6 minutes", f"{half['30 bits'] / PBKDF2 / 60:.1f} min",
       near(half["30 bits"] / PBKDF2 / 60, 6))
report("40 bits, BIP39 passphrase", "~4 days", f"{half['40 bits'] / PBKDF2 / DAY:.2f} days",
       near(half["40 bits"] / PBKDF2 / DAY, 4, 0.1))
report("five words, one card", "~4.5 x 10^11 years", f"{half['five words'] / YEAR:.2e}",
       near(half["five words"] / YEAR, 4.5e11))
report("five words, 1,000 cards", "~4.5 x 10^8 years", f"{half['five words'] / 1000 / YEAR:.2e}",
       near(half["five words"] / 1000 / YEAR, 4.5e8))
report("five words, BIP39 passphrase", "~300,000 years", f"{half['five words'] / PBKDF2 / YEAR:,.0f}",
       near(half["five words"] / PBKDF2 / YEAR, 300000))
report("bits of four and five words", "~51.7 and ~64.6", f"{4 * math.log2(7776):.2f}, {5 * math.log2(7776):.2f}",
       round(4 * math.log2(7776), 1) == 51.7 and round(5 * math.log2(7776), 1) == 64.6)

farm = 90
report("farm, 30 bits", "~2 months", f"{half['30 bits'] / farm / DAY:.0f} days", 55 <= half["30 bits"] / farm / DAY <= 70)
report("farm, four words", "~640,000 years", f"{half['four words'] / farm / YEAR:,.0f}",
       near(half["four words"] / farm / YEAR, 640000))
report("farm, five words", "~5 billion years", f"{half['five words'] / farm / YEAR:.2e}",
       near(half["five words"] / farm / YEAR, 5e9))
botnet = 1e6 / 120  # one million computers, one guess in about two minutes each
report("botnet rate", "roughly 8,000 guesses per second", f"{botnet:,.0f}", near(botnet, 8000))
report("botnet, 30 bits", "~18 hours", f"{half['30 bits'] / botnet / 3600:.1f} h", near(half["30 bits"] / botnet / 3600, 18))
report("botnet, four words", "~7,000 years", f"{half['four words'] / botnet / YEAR:,.0f}",
       near(half["four words"] / botnet / YEAR, 7000))
report("botnet, five words", "~54 million years", f"{half['five words'] / botnet / YEAR / 1e6:.1f} million",
       near(half["five words"] / botnet / YEAR, 54e6))

false_matches = half["four words"] / 2**32
report("21 words, four-word password: false matches", "about 426,000", f"{false_matches:,.0f}",
       near(false_matches, 426000, 0.01))
ratio = (7776**5 / PBKDF2) / (2**32 * 1)
report("their passphrase searches against the MHFE work", "about 4,400 times", f"{ratio:,.0f}", near(ratio, 4400, 0.02))
pair = (2**30 / 2) + (2**30 * 2**30 / 2) / PBKDF2
report("24 words, independent 30-bit secrets", "~12,000 years", f"{pair / YEAR:,.0f}", near(pair / YEAR, 12000, 0.05))

median, mean, p99 = math.log(2) * 2048, 2048, math.log(100) * 2048
report("final word, median", "roughly one to two days", f"{median / 60 / 24:.2f} to {2 * median / 60 / 24:.2f} days",
       0.9 < median / 60 / 24 < 1.1 and 1.9 < 2 * median / 60 / 24 < 2.1)
report("final word, 99th percentile", "up to about 13 days", f"{2 * p99 / 60 / 24:.1f} days", round(2 * p99 / 60 / 24) == 13)
report("class size after revealing the last word", "about 2^245", "2^(256-11)", True)
report("secret PIM factor at k = 31", "never more than sixteen", 33 / 2, 33 / 2 <= 16)

print(f"summary: {sum(results)} PASS, {len(results) - sum(results)} CHECK")
