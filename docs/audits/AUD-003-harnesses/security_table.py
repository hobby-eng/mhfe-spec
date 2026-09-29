"""AUD-003 addendum harness: recomputes the Security Considerations table as edited on 2026-09-30.

Model of the table: words drawn uniformly from 7,776, half of all passwords tried on average, one
guess per second per graphics card.
"""

import math

YEAR, DAY, HOUR = 365.25 * 24 * 3600, 24 * 3600, 3600
rows = [  # words, stated bits, stated time for one card, stated time for 1,000 cards
    (2, 25.8, ("days", 350), ("hours", 8)),
    (3, 38.8, ("years", 7500), ("years", 7.5)),
    (4, 51.7, ("years", 58e6), ("years", 58000)),
]
units = {"days": DAY, "hours": HOUR, "years": YEAR}
ok_all = True
for words, bits, one, thousand in rows:
    seconds = 7776**words / 2
    computed_bits = words * math.log2(7776)
    one_value = seconds / units[one[0]]
    thousand_value = seconds / 1000 / units[thousand[0]]
    ok = (round(computed_bits, 1) == bits and abs(one_value - one[1]) <= 0.05 * one[1]
          and abs(thousand_value - thousand[1]) <= 0.07 * thousand[1])
    ok_all &= ok
    print(f"{'PASS' if ok else 'FAIL'}  {words} words: {computed_bits:.2f} bits (stated {bits}); "
          f"one card {one_value:,.2f} {one[0]} (stated about {one[1]:,}); "
          f"1,000 cards {thousand_value:,.2f} {thousand[0]} (stated about {thousand[1]:,})")
five = 7776**5 / 2 / YEAR
print(f"{'PASS' if five > 1e11 else 'FAIL'}  5 words: {five:.2e} years on one card (stated far beyond any attack)")
print("summary:", "all rows agree" if ok_all and five > 1e11 else "a row disagrees")
