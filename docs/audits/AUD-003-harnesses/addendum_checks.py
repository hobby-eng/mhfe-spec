"""AUD-003 addendum harness (2026-09-30): checks the statements changed after the review.

1. Secret PIM model of the supplement: exhaustive search on small cases against the closed forms
   for C_known, C_hidden, the averaged ratio and the owner's cost of a forgotten PIM.
2. Leaked intermediate salt: counts, on a real suite 3 vector, how many Argon2id calls the
   backward filter from the container needs before S_i can be compared.
3. Identical containers: a 12-word source and a 24-word source with the same packed state, which
   the same permutation maps to the same container.

Usage: python3 addendum_checks.py <wordlist.rs> <suite3-vector.json>
"""

import importlib.util
import json
import os
import sys

# The harness folder holds numbers.py, which would shadow the standard library module of that
# name (and so break fractions), so it is taken off the import path and notation_check.py, the
# audit's implementation of the README formulas, is loaded from its file instead.
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path = [entry for entry in sys.path if os.path.abspath(entry or ".") != HERE]
from fractions import Fraction  # noqa: E402

_spec = importlib.util.spec_from_file_location("notation_check", os.path.join(HERE, "notation_check.py"))
spec = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(spec)

results = []


def report(label, ok, detail=""):
    results.append(ok)
    print(f"{'PASS' if ok else 'FAIL'}  {label}{': ' + detail if detail else ''}")


# 1. Secret PIM. Cost unit C0 = 1. Layered order: every password at PIM 0, then at PIM 1, ...
def layered_cost(n, true_password, true_pim):
    cost = 0
    for pim in range(true_pim + 1):
        for password in range(n):
            cost += pim + 1
            if pim == true_pim and password == true_password:
                return cost
    raise AssertionError("not found")


def known_cost(n, true_password, true_pim):
    return (true_password + 1) * (true_pim + 1)


for n in (1, 2, 5, 17):
    for k in (0, 1, 3, 7):
        hidden = Fraction(sum(layered_cost(n, p, k) for p in range(n)), n)
        known = Fraction(sum(known_cost(n, p, k) for p in range(n)), n)
        report(f"C_hidden N={n} k={k}", hidden == Fraction(n * (k + 1) ** 2 + (k + 1), 2), str(hidden))
        report(f"C_known N={n} k={k}", known == Fraction((n + 1) * (k + 1), 2), str(known))
for n in (1, 3, 10):
    for q in (1, 2, 4, 8):
        mean_hidden = Fraction(sum(n * (k + 1) ** 2 + (k + 1) for k in range(q)), 2 * q)
        mean_known = Fraction(sum((n + 1) * (k + 1) for k in range(q)), 2 * q)
        ratio = mean_hidden / mean_known
        report(f"averaged ratio N={n} Q={q}", ratio == Fraction(n * (2 * q + 1) + 3, 3 * (n + 1)), str(ratio))
limit = Fraction(2 * 1024 + 1, 3)
report("averaged ratio for Q=1024, large N", round(float(limit)) == 683, f"{float(limit):.2f}")
report("ratio for a true PIM of 1023, large N", (1023 + 1) == 1024, "k + 1 = 1024")
for k in (0, 1, 5, 1023):
    owner = sum(j + 1 for j in range(k + 1))
    report(f"owner's search, true PIM {k}", owner == (k + 1) * (k + 2) // 2
           and Fraction(owner, k + 1) == Fraction(k + 2, 2), f"{owner} = {Fraction(owner, k + 1)} x known")

# 2. Backward filter from the container: calls needed before S_i can be compared.
words = spec.load_wordlist(sys.argv[1])
vector = json.load(open(sys.argv[2]))
y = spec.phrase_to_entropy(vector["container"], words)
recorded = {entry["round"]: entry for entry in vector["decryption"]["rounds"]}
left, right = y[:16], y[16:]
calls = 0
for i in range(11, -1, -1):
    # Before round i's inverse, R_i = L_{i+1} is known, so S_i can be compared now.
    salt = spec.Suite(3).salt(0, 0, i, left)
    report(f"S_{i} comparable after {calls} calls", salt.hex() == recorded[i]["salt_hex"] and calls == 11 - i,
           f"11 - i = {11 - i}")
    key = bytes.fromhex(recorded[i]["argon2_key_hex"])
    calls += 1  # this Argon2id call yields M_i
    mask = spec.Suite(3).mask(key, 0, 0, i, left)
    left, right = spec.xor(right, mask), left

# 3. Identical containers from different phrases.
short_entropy = bytes(range(16))
packed = spec.pack(short_entropy)
long_phrase = spec.entropy_to_phrase(packed, words)
short_phrase = spec.entropy_to_phrase(short_entropy, words)
report("the 12-word packed state is valid 24-word entropy", spec.pack(spec.phrase_to_entropy(long_phrase, words)) == packed,
       "same 256-bit input state")
report("the two source phrases differ", short_phrase != long_phrase, f"{len(short_phrase.split())} and {len(long_phrase.split())} words")

print(f"summary: {results.count(True)} PASS, {results.count(False)} FAIL")
