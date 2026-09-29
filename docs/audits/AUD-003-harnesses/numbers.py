"""AUD-002 audit harness: recomputes every number that README.md states, from first principles.

Each line prints the stated value, the recomputed value and PASS or CHECK. CHECK marks a value the
reviewer must judge by hand (for example a rounded range); the script never edits anything.
"""

import math

YEAR = 365.25 * 24 * 3600
DAY = 24 * 3600
GIB_KIB = 2**20
results = []


def report(label, stated, computed, ok):
    results.append(ok)
    print(f"{'PASS' if ok else 'CHECK'}  {label}: stated {stated}; computed {computed}")


def memory_kib(mem):
    return (2 + mem % 2) * 2 ** (20 + mem // 2)


# Work factor.
levels = [memory_kib(mem) / GIB_KIB for mem in range(22)]
report("m(MEM) levels 0..10 in GiB", "2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64", levels[:11],
       levels[:11] == [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64])
report("m(21)", "3 TiB", f"{memory_kib(21) / 2**30} TiB", memory_kib(21) == 3 * 2**30)
report("every level a whole number of GiB", "yes", all(level == int(level) for level in levels),
       all(level == int(level) for level in levels))
factors = {round(levels[i + 1] / levels[i], 6) for i in range(21)}
report("ratios between levels", "1.5 and 4/3 in turn", sorted(factors), factors == {1.5, round(4 / 3, 6)})
report("level 21 within Argon2 limit 2^32-1 KiB", "yes", memory_kib(21) <= 2**32 - 1, memory_kib(21) <= 2**32 - 1)
report("level 22 exceeds 2^32-1 KiB", "yes", f"{memory_kib(22)} KiB", memory_kib(22) > 2**32 - 1)
bits32 = min(32, 4 * 8 - 10 - 1)  # argon2.h ARGON2_MAX_MEMORY_BITS for 32-bit pointers
report("32-bit reference C limit", "2 GiB, so level 0 only", f"2^{bits32} KiB = {2**bits32 / GIB_KIB} GiB",
       2**bits32 == memory_kib(0) and memory_kib(1) > 2**bits32)
hours = (1024 * 1 / 60, 1024 * 2 / 60)
report("PIM 1023 from a 1-2 minute operation", "roughly 17 to 34 hours", f"{hours[0]:.1f} to {hours[1]:.1f} h",
       round(hours[0]) == 17 and round(hours[1]) == 34)
report("t(1023)", "within Argon2 pass limit 2^32-1", 12 * 1024, 12 * 1024 <= 2**32 - 1)

# Motivation: PBKDF2 against MHFE.
ratio = 1.5e6 / 1
report("cost ratio in bits", "about 2^20, about 20 bits", f"log2(1.5e6) = {math.log2(ratio):.2f}",
       20 <= math.log2(ratio) < 21)
word_bits = math.log2(7776)
report("bits per dice word", "about 12.9", f"{word_bits:.3f}", round(word_bits, 1) == 12.9)
report("20 bits in dice words", "roughly one and a half", f"{20 / word_bits:.2f}", 1.4 < 20 / word_bits < 1.7)
four = 7776**4 / 2
report("four words as a BIP39 passphrase, one card", "about 39 years", f"{four / 1.5e6 / YEAR:.1f} years",
       round(four / 1.5e6 / YEAR) == 39)
report("four words as an MHFE password, one card", "about 58 million years", f"{four / YEAR / 1e6:.1f} million",
       round(four / YEAR / 1e6) == 58)

# Security Considerations table (one guess per second per card, half the space on average).
thirty = 2**30 / 2
report("30 bits, one card", "about 17 years", f"{thirty / YEAR:.2f} years", round(thirty / YEAR) == 17)
report("30 bits, 1000 cards", "about 6 days", f"{thirty / 1000 / DAY:.2f} days", round(thirty / 1000 / DAY) == 6)
report("four words, 1000 cards", "about 58,000 years", f"{four / 1000 / YEAR:,.0f} years",
       round(four / 1000 / YEAR, -3) == 58000)
five = 7776**5 / 2
report("five words, one card", "far beyond any attack", f"{five / YEAR:.2e} years", five / YEAR > 1e11)
report("each extra word multiplies the search by", "7,776", 7776, True)

# Final-word cycle walking.
days = (2048 * 1 / 60 / 24, 2048 * 2 / 60 / 24)
report("2,048 permutations of 1-2 minutes", "about one and a half to three days",
       f"{days[0]:.2f} to {days[1]:.2f} days", 1.3 < days[0] < 1.6 and 2.7 < days[1] < 3.0)
report("expected permutations for an 11-bit last word", "about 2,048", 2**11, True)
report("information in the last 24-word word", "3 entropy bits, about 11 bits in total", "3 + 8 checksum bits", True)

# Secret PIM: an attacker trying PIM 0, 1, ... pays sum_{j<=k} (j+1) = (k+1)(k+2)/2 instead of k+1.
for k in (0, 1, 31, 1023):
    factor = ((k + 1) * (k + 2) / 2) / (k + 1)
    report(f"secret PIM factor at k={k}", "(k + 2) / 2", factor, factor == (k + 2) / 2)
report("secret PIM at 1023 in bits", "at most about nine bits (supplement)", f"{math.log2(1025 / 2):.2f}",
       round(math.log2(1025 / 2)) == 9)

# Recovery probabilities (random oracle: a layout with an r-bit verifier matches with 2^-r).
layouts = {12: 128, 15: 96, 18: 64, 21: 32}
p24 = sum(2.0**-r for r in layouts.values())
report("random 24-word source matches a short layout", "about 2^-32", f"2^{math.log2(p24):.6f}",
       abs(math.log2(p24) + 32) < 1e-6)
for words in (12, 15, 18, 21):
    extra = sum(2.0**-r for w, r in layouts.items() if w != words)
    stated = "about 2^-64" if words == 21 else "about 2^-32"
    target = -64 if words == 21 else -32
    report(f"extra match for a correct {words}-word source", stated, f"2^{math.log2(extra):.6f}",
           abs(math.log2(extra) - target) < 1e-6)
report("fixed point of a random permutation", "2^-256", "1/2^256", True)
for words, ent in ((12, 128), (15, 160), (18, 192), (21, 224), (24, 256)):
    r, checksum = 256 - ent, ent // 32
    report(f"{words} words: verifier r and BIP39 checksum", "checksum = first ENT/32 bits of V_r",
           f"r={r}, CS={checksum}", checksum <= r or r == 0)

print(f"summary: {sum(results)} PASS, {len(results) - sum(results)} CHECK")
