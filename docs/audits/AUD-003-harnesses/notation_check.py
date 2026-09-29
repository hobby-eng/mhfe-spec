"""AUD-002 audit harness: checks the specification's notation and schemes against the vectors.

Written for this audit from the text of README.md at the reviewed commit only (sections
"Conventions and Terminology", "Suite parameters", "Packing", "Permutation", "Recovering a
mnemonic", "Work factor" and "Appendix: Suite 2"). It shares no code with the implementation or its
own independent checker. Argon2id outputs are taken from the vectors and recomputed only with
--argon2, which runs a few real calls through OpenSSL (Python `cryptography`).

Usage: python3 notation_check.py <wordlist.rs> <suite3-folder> <suite2-folder> [--argon2]
"""

import hashlib
import hmac
import json
import os
import re
import sys
import time
import unicodedata

OFFICIAL_ENGLISH_SHA256 = "2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda"
ROUNDS = 12
LANES = 4


def load_wordlist(path):
    words = re.findall(r'"([a-z]+)"', open(path).read())
    digest = hashlib.sha256(("\n".join(words) + "\n").encode()).hexdigest()
    assert len(words) == 2048 and digest == OFFICIAL_ENGLISH_SHA256, (len(words), digest)
    return words


def be32(value):
    return value.to_bytes(4, "big")


# --- BIP39 -------------------------------------------------------------------------------------


def phrase_to_entropy(phrase, words):
    indexes = [words.index(word) for word in phrase.split()]
    bits = "".join(format(index, "011b") for index in indexes)
    ent = len(bits) * 32 // 33
    entropy = int(bits[:ent], 2).to_bytes(ent // 8, "big")
    checksum = format(hashlib.sha256(entropy).digest()[0] >> (8 - ent // 32), f"0{ent // 32}b")
    assert bits[ent:] == checksum, "BIP39 checksum"
    return entropy


def entropy_to_phrase(entropy, words):
    ent = len(entropy) * 8
    bits = format(int.from_bytes(entropy, "big"), f"0{ent}b")
    bits += format(hashlib.sha256(entropy).digest()[0] >> (8 - ent // 32), f"0{ent // 32}b")
    return " ".join(words[int(bits[i : i + 11], 2)] for i in range(0, len(bits), 11))


# --- Specification formulas ---------------------------------------------------------------------


def memory_kib(mem):
    # m(MEM) = (2 + MEM mod 2) * 2^(20 + floor(MEM / 2)) KiB
    return (2 + mem % 2) * 2 ** (20 + mem // 2)


def passes(pim):
    # t(PIM) = 12 * (PIM + 1)
    return 12 * (pim + 1)


def pack(entropy):
    # r = 256 - ENT; X = E || Trunc_r(SHA-256(E)); r is a multiple of 32, so whole bytes.
    r = 256 - len(entropy) * 8
    return entropy + hashlib.sha256(entropy).digest()[: r // 8]


class Suite:
    def __init__(self, number):
        self.number = number
        suite_id = f"MHFE-BIP39-256-EXPERIMENTAL-{number}".encode("ascii")
        self.ds_salt = suite_id + b"/ROUND-SALT"
        self.ds_mask = suite_id + b"/ROUND-MASK"

    def settings(self, pim, mem):
        # Suite 3 binds BE32(MEM) || BE32(PIM); suite 2 binds BE32(PIM) only (appendix).
        return be32(mem) + be32(pim) if self.number == 3 else be32(pim)

    def salt(self, pim, mem, i, right):
        message = self.ds_salt + self.settings(pim, mem) + be32(i) + right
        return hashlib.blake2b(message, digest_size=32).digest()[:16]

    def mask(self, key, pim, mem, i, right):
        message = self.ds_mask + self.settings(pim, mem) + be32(i) + right
        return hmac.new(key, message, hashlib.sha256).digest()[:16]


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


def forward(suite, x, keys_by_salt, pim, mem):
    left, right = x[:16], x[16:]
    trace = []
    for i in range(ROUNDS):
        salt = suite.salt(pim, mem, i, right)
        key = keys_by_salt[salt]
        mask = suite.mask(key, pim, mem, i, right)
        new_left, new_right = right, xor(left, mask)
        trace.append((i, left, right, salt, key, mask, new_left, new_right))
        left, right = new_left, new_right
    return left + right, trace


def inverse(suite, y, keys_by_salt, pim, mem):
    left, right = y[:16], y[16:]  # L_12, R_12
    trace = []
    for i in range(ROUNDS - 1, -1, -1):
        previous_right = left  # R_i = L_{i+1}
        salt = suite.salt(pim, mem, i, previous_right)
        key = keys_by_salt[salt]
        mask = suite.mask(key, pim, mem, i, previous_right)
        previous_left = xor(right, mask)  # L_i = R_{i+1} XOR M_i
        trace.append((i, left, right, salt, key, mask, previous_left, previous_right))
        left, right = previous_left, previous_right
    return left + right, trace


def detect(x):
    matches = []
    for words, ent in ((12, 128), (15, 160), (18, 192), (21, 224)):
        entropy = x[: ent // 8]
        if pack(entropy) == x:
            matches.append((words, entropy))
    return matches


# --- Vector checks ------------------------------------------------------------------------------


def check_trace(recorded, computed, names, label):
    assert len(recorded) == len(computed) == ROUNDS, label
    for entry, values in zip(recorded, computed):
        for name, value in zip(names, values):
            expected = entry[name]
            actual = value if isinstance(value, int) else value.hex()
            assert expected == actual, f"{label} round {values[0]} {name}: {expected} != {actual}"


def check_suite3(path, words):
    vector = json.load(open(path))
    suite = Suite(3)
    inputs = vector["inputs"]
    pim, mem = inputs["pim"], inputs["memory_level"]
    assert vector["suite_id"] == "MHFE-BIP39-256-EXPERIMENTAL-3"
    assert vector["argon2"] == {
        "variant": "Argon2id",
        "version": 0x13,
        "memory_kib": memory_kib(mem),
        "passes": passes(pim),
        "lanes": LANES,
        "output_bytes": 32,
    }, "Argon2id parameters"
    password = inputs["password"].encode()
    assert password.hex() == inputs["password_utf8_hex"]
    nfkd = unicodedata.normalize("NFKD", inputs["password"]).encode()
    assert nfkd.hex() == inputs["password_nfkd_utf8_hex"], "NFKD (Python unicodedata)"
    entropy = phrase_to_entropy(inputs["phrase"], words)
    x = pack(entropy)
    packing = vector["packing"]
    assert packing["words"] == len(inputs["phrase"].split())
    assert packing["entropy_hex"] == entropy.hex() and packing["state_hex"] == x.hex()
    assert packing["verifier_hex"] == x[len(entropy) :].hex()
    keys = {}
    for direction in ("encryption", "decryption"):
        for entry in vector[direction]["rounds"]:
            keys[bytes.fromhex(entry["salt_hex"])] = bytes.fromhex(entry["argon2_key_hex"])
    names = ("round", "left_before_hex", "right_before_hex", "salt_hex", "argon2_key_hex",
             "mask_hex", "left_after_hex", "right_after_hex")
    assert vector["encryption"]["input_state_hex"] == x.hex()
    y, trace = forward(suite, x, keys, pim, mem)
    check_trace(vector["encryption"]["rounds"], trace, names, f"{path} encryption")
    assert vector["encryption"]["output_state_hex"] == y.hex()
    assert vector["container"] == entropy_to_phrase(y, words), "container words"
    y_from_words = phrase_to_entropy(vector["container"], words)
    x_back, trace = inverse(suite, y_from_words, keys, pim, mem)
    check_trace(vector["decryption"]["rounds"], trace, names, f"{path} decryption")
    assert vector["decryption"]["output_state_hex"] == x_back.hex() == x.hex()
    matches = detect(x_back)
    expected = [{"words": w, "verified": True, "phrase": entropy_to_phrase(e, words)} for w, e in matches]
    if len(matches) != 1:
        expected.append({"words": 24, "verified": False, "phrase": entropy_to_phrase(x_back, words)})
    assert vector["recovery"] == expected, f"recovery {vector['recovery']} != {expected}"
    return pim, mem, len(matches)


def check_suite2(path, words):
    vector = json.load(open(path))
    suite = Suite(2)
    encryption, decryption = vector["encryption"], vector["decryption"]
    pim, mem = encryption["pim"], 0
    assert encryption["effective_passes"] == passes(pim)
    entropy = phrase_to_entropy(vector["source_mnemonic"], words)
    x = pack(entropy)
    assert encryption["packed_plaintext_hex"] == x.hex()
    keys = {}
    for record in (encryption, decryption):
        for entry in record["trace"]["rounds"]:
            keys[bytes.fromhex(entry["salt_hex"])] = bytes.fromhex(entry["argon2_key_hex"])
    names = ("round", "input_left_hex", "input_right_hex", "salt_hex", "argon2_key_hex", "mask_hex",
             "output_left_hex", "output_right_hex")
    y, trace = forward(suite, x, keys, pim, mem)
    check_trace(encryption["trace"]["rounds"], trace, names, f"{path} encryption")
    assert encryption["encrypted_entropy_hex"] == y.hex()
    assert encryption["encrypted_mnemonic"] == entropy_to_phrase(y, words)
    x_back, trace = inverse(suite, phrase_to_entropy(encryption["encrypted_mnemonic"], words), keys, pim, mem)
    check_trace(decryption["trace"]["rounds"], trace, names, f"{path} decryption")
    assert decryption["recovered_mnemonic"] == vector["source_mnemonic"]
    return pim


def argon2_probe(label, salt_hex, key_hex, password, pim, memory):
    from cryptography.hazmat.primitives.kdf.argon2 import Argon2id

    start = time.time()
    kdf = Argon2id(salt=bytes.fromhex(salt_hex), length=32, iterations=passes(pim), lanes=LANES,
                   memory_cost=memory)
    key = kdf.derive(password)
    assert key.hex() == key_hex, f"{label}: Argon2id output differs"
    print(f"argon2 {label}: m={memory} KiB t={passes(pim)} p={LANES} matches ({time.time() - start:.1f} s)")


def main():
    words = load_wordlist(sys.argv[1])
    suite3_dir, suite2_dir = sys.argv[2], sys.argv[3]
    print(f"wordlist: 2048 words, SHA-256 {OFFICIAL_ENGLISH_SHA256} (official english.txt)")
    positive = sorted(f for f in os.listdir(suite3_dir) if f.endswith(".json") and f != "negative-cases.json")
    for name in positive:
        pim, mem, matches = check_suite3(os.path.join(suite3_dir, name), words)
        print(f"suite 3 {name}: PIM {pim}, MEM {mem}, {matches} verifier match(es): every salt, mask, "
              "state, container word and recovery result reproduced from the specification text")
    suite2 = sorted(f for f in os.listdir(suite2_dir) if f.endswith(".json") and f != "validation-cases.json")
    for name in suite2:
        pim = check_suite2(os.path.join(suite2_dir, name), words)
        print(f"suite 2 {name}: PIM {pim}: every salt, mask, state and container word reproduced")
    print(f"summary: suite 3 positive vectors {len(positive)}/{len(positive)}, suite 2 vectors {len(suite2)}/{len(suite2)}")
    if "--argon2" in sys.argv:
        probes = [("zero-12.json", 0), ("zero-12-pim-1.json", 0), ("zero-12-memory-level-1.json", 0)]
        for name, index in probes:
            vector = json.load(open(os.path.join(suite3_dir, name)))
            entry = vector["encryption"]["rounds"][index]
            password = bytes.fromhex(vector["inputs"]["password_nfkd_utf8_hex"])
            argon2_probe(f"suite 3 {name} round {index}", entry["salt_hex"], entry["argon2_key_hex"], password,
                         vector["inputs"]["pim"], memory_kib(vector["inputs"]["memory_level"]))
        vector = json.load(open(os.path.join(suite2_dir, "zero-12-pim-0.json")))
        entry = vector["encryption"]["trace"]["rounds"][0]
        argon2_probe("suite 2 zero-12-pim-0.json round 0", entry["salt_hex"], entry["argon2_key_hex"],
                     bytes.fromhex(vector["password_utf8_hex"]), 0, 512 * 1024)


if __name__ == "__main__":
    main()
