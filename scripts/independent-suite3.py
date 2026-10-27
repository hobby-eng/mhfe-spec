"""Independent implementation of MHFE suite 3 for checking the vectors and other implementations.

Written from the specification alone. It shares no code with mhfe-core or mhfe: Argon2id comes from
OpenSSL through Python `cryptography`, BLAKE2b, HMAC and SHA-256 from Python's standard library,
and the Unicode 18.0.0 character database of the password rule from `unicodedata2`, because
Python's own `unicodedata` is an older Unicode version. Install the packages with
`python3 -m pip install --require-hashes -r scripts/independent-suite3-requirements.txt`.

In an emergency, when no other compatible software is available, `encrypt` and `decrypt` also
create and recover a real container. They ask for the phrase and the password at the terminal and show them as typed, as they show the result. Run them only on a trusted offline computer, with nobody watching the screen: Python does not erase the secrets from memory, and nothing here protects them beyond that.

Usage:
    python3 scripts/independent-suite3.py encrypt [PIM] [MEM]
    python3 scripts/independent-suite3.py decrypt [WORDS] [PIM] [MEM]
    python3 scripts/independent-suite3.py vector [--trust-argon2-keys] [--record <file>] <file.json> ...
    python3 scripts/independent-suite3.py passwords vectors/suite3/validation-cases.json

`encrypt` makes a 24-word container from an original seed phrase of 12 to 24 words and recovers it
once before showing it. `decrypt` recovers a 24-word container under the length rules of the
specification; WORDS is the stated length of the original phrase, 0 or omitted when it is unknown.
PIM and MEM are the PIM and the memory level used at creation, 0 when omitted. The optional
16-bit wallet check is not evaluated: a 24-word reading is confirmed only by a known address. For example,
`decrypt 12 0 0` recovers the container of a 12-word phrase made with the default settings. Words
may be typed in any letter case, and by their first four letters.

`vector` checks vector files and negative-cases.json: it recomputes every value in both
directions, including every Argon2id call, about ten seconds each at the defaults. With
--trust-argon2-keys it takes the recorded Argon2id outputs as given, looked up by their salt, and
checks everything else within a second: packing, salts, masks, rounds, container and recovery.
Negative cases have no recorded keys and need the full check.

`passwords` checks every password-encoding case of the validation fixture: the NFKD result or the
error that the password rule of the specification gives, including the Unicode 18 rule for
unassigned code points.

--record adds the checked files to a JSON record: the SHA-256 of this script, the
Python, `cryptography`, `unicodedata2` and OpenSSL versions, and for each file its SHA-256 and how it was checked
("full" or "recorded-argon2-keys"). Runs with the same script add to the record; a file whose
bytes changed, or a changed script, starts its entry again.

The BIP39 English wordlist is read from bip39-english.txt next to this script, or from the file
named by the environment variable BIP39_ENGLISH_WORDLIST (one word per line).

Taken from mhfe at commit 8be344293a184a91f7d7a2260c5fdcceb229ec3d (MIT License, copyright 2026
Sergei Semenov) and extended with the emergency commands.
"""

import hashlib
import hmac
import importlib.metadata
import json
import os
import platform
import sys

try:
    import unicodedata2 as unicode18
except ImportError:
    sys.exit("Needs unicodedata2: python3 -m pip install --require-hashes -r scripts/independent-suite3-requirements.txt")

# The password rule uses this exact Unicode version (the specification, "Password encoding").
UNICODE_VERSION = "18.0.0"
if unicode18.unidata_version != UNICODE_VERSION:
    sys.exit(f"unicodedata2 has Unicode {unicode18.unidata_version}, the password rule needs {UNICODE_VERSION}")
# Longest password after NFKD, in bytes.
MAX_PASSWORD_BYTES = 1024

SUITE_ID = b"MHFE-BIP39-256-EXPERIMENTAL-3"
DS_SALT = SUITE_ID + b"/ROUND-SALT"
DS_MASK = SUITE_ID + b"/ROUND-MASK"
SCHEMA = "mhfe-suite-3-vector-v2"
NEGATIVE_SCHEMA = "mhfe-suite-3-negative-case-v2"
ROUNDS = 12
LANES = 4
# Argon2 version 1.3, as the specification and RFC 9106 write it.
ARGON2_VERSION = 0x13
KEY_BYTES = 32
# Entropy bytes of the short phrase lengths, in the order detection tests them.
SHORT_LENGTHS = {12: 16, 15: 20, 18: 24, 21: 28}


def english_wordlist():
    default = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bip39-english.txt")
    words = open(os.environ.get("BIP39_ENGLISH_WORDLIST", default), encoding="ascii").read().split()
    # The SHA-256 of BIP39's english.txt, 2048 words each followed by a line feed.
    digest = hashlib.sha256("".join(word + "\n" for word in words).encode()).hexdigest()
    assert digest == "2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda", "not the BIP39 English wordlist"
    return words


WORDS = english_wordlist()


def phrase_to_entropy(phrase):
    indexes = [WORDS.index(word) for word in phrase.split()]
    bits = "".join(format(index, "011b") for index in indexes)
    checksum_bits = len(bits) // 33
    entropy = int(bits[:-checksum_bits], 2).to_bytes((len(bits) - checksum_bits) // 8, "big")
    expected = format(hashlib.sha256(entropy).digest()[0], "08b")[:checksum_bits]
    assert bits[-checksum_bits:] == expected, "invalid BIP39 checksum"
    return entropy


def entropy_to_phrase(entropy):
    checksum_bits = len(entropy) * 8 // 32
    bits = format(int.from_bytes(entropy, "big"), f"0{len(entropy) * 8}b")
    bits += format(hashlib.sha256(entropy).digest()[0], "08b")[:checksum_bits]
    return " ".join(WORDS[int(bits[i:i + 11], 2)] for i in range(0, len(bits), 11))


def memory_kib(level):
    return (2 + level % 2) << (20 + level // 2)


def passes(pim):
    return 12 * (pim + 1)


def be32(value):
    return value.to_bytes(4, "big")


def openssl_argon2id(password, salt, pim, level):
    """K_i: Argon2id version 1.3, four lanes, 32 bytes, empty secret and associated data."""
    from cryptography.hazmat.primitives.kdf.argon2 import Argon2id

    kdf = Argon2id(
        salt=salt, length=32, iterations=passes(pim), lanes=LANES, memory_cost=memory_kib(level)
    )
    return kdf.derive(password)


def round_values(argon2, password, pim, level, round_index, right):
    """The salt input, salt, Argon2id output, mask input and mask of one round."""
    message = be32(level) + be32(pim) + be32(round_index) + right
    salt_input, mask_input = DS_SALT + message, DS_MASK + message
    salt = hashlib.blake2b(salt_input, digest_size=32).digest()[:16]
    key = argon2(password, salt, pim, level)
    mask = hmac.new(key, mask_input, hashlib.sha256).digest()[:16]
    return salt_input, salt, key, mask_input, mask


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


def forward(x, argon2, password, pim, level):
    left, right = x[:16], x[16:]
    rounds = []
    for index in range(ROUNDS):
        values = round_values(argon2, password, pim, level, index, right)
        before = left + right
        left, right = right, xor(left, values[-1])
        rounds.append((index, before, *values, left + right))
    return left + right, rounds


def inverse(y, argon2, password, pim, level):
    left, right = y[:16], y[16:]
    rounds = []
    for index in reversed(range(ROUNDS)):
        values = round_values(argon2, password, pim, level, index, left)
        before = left + right
        left, right = xor(right, values[-1]), left
        rounds.append((index, before, *values, left + right))
    return left + right, rounds


def pack(entropy):
    return entropy + hashlib.sha256(entropy).digest()[: 32 - len(entropy)]


def matching_short_lengths(x):
    return [
        words
        for words, length in SHORT_LENGTHS.items()
        if hashlib.sha256(x[:length]).digest()[: 32 - length] == x[length:]
    ]


def detected_recovery(x):
    """Step 3 of recovery with detection: one match, the 24-word reading, or all of them."""
    lengths = matching_short_lengths(x)
    if len(lengths) == 1:
        return [(lengths[0], True, read_as(x, lengths[0]))]
    candidates = [(words, True, read_as(x, words)) for words in lengths]
    return candidates + [(24, False, read_as(x, 24))]


# Negative cases recorded before the length rules of recovery, which keep the reading of the
# stated length alone; the corpus holds them byte for byte.
STATED_READING_ONLY = {"selected-24-words"}


def stated_recovery(x, words, name):
    """Recovery under the length rules of the specification: detection always runs, and a matching
    layout takes precedence over a stated length. None where a stated short length matches
    nothing (VERIFIER_MISMATCH)."""
    lengths = matching_short_lengths(x)
    if words == 0:
        return detected_recovery(x)
    if words == 24 and name in STATED_READING_ONLY:
        return [(24, False, read_as(x, 24))]
    if words in lengths:
        return [(words, True, read_as(x, words))]
    if words == 24:
        return [(w, True, read_as(x, w)) for w in lengths] + [(24, False, read_as(x, 24))]
    if not lengths:
        return None
    return detected_recovery(x)


def read_as(x, words):
    return entropy_to_phrase(x[: SHORT_LENGTHS.get(words, 32)])


class PasswordRefused(Exception):
    """A password the rule refuses; `code` is the error the specification names."""

    def __init__(self, code):
        super().__init__(code)
        self.code = code


def encode_password(raw):
    """P_enc = UTF8(NFKD(P)) under the password rule of the specification, from UTF-8 bytes."""
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        raise PasswordRefused("INVALID_PASSWORD_UTF8") from None
    if any(map(is_refused_in_password, text)):
        raise PasswordRefused("CONTROL_CHARACTER_IN_PASSWORD")
    # Stabilized normalization fails on a code point that Unicode 18.0.0 leaves unassigned (Cn),
    # the noncharacters included; Private Use (Co) is assigned.
    if any(unicode18.category(character) == "Cn" for character in text):
        raise PasswordRefused("UNASSIGNED_CHARACTER")
    encoded = unicode18.normalize("NFKD", text).encode("utf-8")
    if not encoded:
        raise PasswordRefused("EMPTY_PASSWORD")
    if len(encoded) > MAX_PASSWORD_BYTES:
        raise PasswordRefused("PASSWORD_TOO_LONG")
    return encoded


def check_password_cases(path):
    """Every password case of the validation fixture: its NFKD bytes, or their count, or its error.

    A case gives its input either as UTF-8 hex or as a piece repeated `count` times; a long result
    is given by its length in bytes.
    """
    cases = json.load(open(path, encoding="utf-8"))["passwords"]
    for case in cases:
        if "input_utf8_hex" in case:
            raw = bytes.fromhex(case["input_utf8_hex"])
        else:
            raw = bytes.fromhex(case["repeat_utf8_hex"]) * case["count"]
        try:
            encoded = encode_password(raw)
        except PasswordRefused as refusal:
            assert refusal.code == case.get("expected_error"), (
                f"password case {case['id']}: refused with {refusal.code}, expected {case.get('expected_error')}"
            )
            if "expected_nfkd_bytes" in case:
                length = len(unicode18.normalize("NFKD", raw.decode("utf-8")).encode("utf-8"))
                assert length == case["expected_nfkd_bytes"], f"password case {case['id']}: {length} bytes"
            continue
        assert "expected_error" not in case, f"password case {case['id']}: accepted, expected {case['expected_error']}"
        if "expected_nfkd_utf8_hex" in case:
            assert encoded.hex() == case["expected_nfkd_utf8_hex"], f"password case {case['id']}: {encoded.hex()}"
        else:
            assert len(encoded) == case["expected_nfkd_bytes"], f"password case {case['id']}: {len(encoded)} bytes"
    print(f"{path}: all {len(cases)} password cases reproduced with Unicode {UNICODE_VERSION}")


def encrypt(phrase, password_text, pim=0, level=0):
    """The container, after the creation check: one recovery that must give the packed state back."""
    assert len(phrase.split()) in (12, 15, 18, 21, 24), "the original phrase has 12, 15, 18, 21 or 24 words"
    password = encode_password(password_text.encode("utf-8"))
    x = pack(phrase_to_entropy(phrase))
    y, _ = forward(x, openssl_argon2id, password, pim, level)
    assert inverse(y, openssl_argon2id, password, pim, level)[0] == x, "the creation check failed"
    return entropy_to_phrase(y)


def decrypt(container, password_text, words=0, pim=0, level=0):
    """The readings that recovery gives (length, verified, phrase), or None for VERIFIER_MISMATCH,
    and every short length whose check the recovered state passes."""
    assert len(container.split()) == 24, "a suite 3 container has 24 words"
    assert words in (0, 12, 15, 18, 21, 24), "the stated length is 12, 15, 18, 21 or 24 words, or 0"
    password = encode_password(password_text.encode("utf-8"))
    x = inverse(phrase_to_entropy(container), openssl_argon2id, password, pim, level)[0]
    return stated_recovery(x, words, ""), matching_short_lengths(x)


def ask(prompt):
    """A line from standard input, shown as typed; the prompt goes to standard error."""
    print(prompt, end="", file=sys.stderr, flush=True)
    return sys.stdin.readline().rstrip("\n")


def ask_phrase(prompt):
    """A phrase in any letter case and spacing, each word in full or by its first four letters."""
    tokens = ask(prompt).lower().split()
    return " ".join(next((w for w in WORDS if w.startswith(t)), t) if len(t) >= 4 else t for t in tokens)


def ask_new_password():
    password = ask("Password: ")
    if ask("Password again: ") != password:
        sys.exit("the two passwords differ")
    return password


def settings(arguments, count):
    """The integer arguments, 0 where omitted; the last two are the PIM and the memory level."""
    values = [int(value) for value in arguments] + [0] * (count - len(arguments))
    assert 0 <= values[-2] <= 1023 and 0 <= values[-1] <= 21, "the PIM is 0 to 1023, the memory level 0 to 21"
    return values


def recorded_keys_by_salt(vector):
    """The --trust-argon2-keys source of K_i: the recorded output for each recorded salt."""
    keys = {}
    for direction in ("encryption", "decryption"):
        for entry in vector[direction]["rounds"]:
            keys[entry["salt_hex"]] = bytes.fromhex(entry["argon2_key_hex"])

    def argon2(password, salt, pim, level):
        assert salt.hex() in keys, f"salt {salt.hex()} was not recorded"
        return keys[salt.hex()]

    return argon2


def is_refused_in_password(character):
    """Control characters (General_Category Cc) and the line and paragraph separators."""
    return unicode18.category(character) == "Cc" or character in "\u2028\u2029"


def check_password(record):
    password = bytes.fromhex(record["password_nfkd_utf8_hex"])
    assert encode_password(record["password"].encode("utf-8")) == password, (
        "the password rule does not give password_nfkd_utf8_hex"
    )
    return password


def check_header(record, schema):
    """The layout name, the suite and what wrote the file."""
    assert record["schema"] == schema, record["schema"]
    assert record["suite_id"] == SUITE_ID.decode()
    generator = record["generator"]
    assert generator["program"] == "mhfe test-vectors"
    assert generator["version"] and generator["argon2"], "the generator is not named"


def check_vector(vector, trust_keys):
    check_header(vector, SCHEMA)
    inputs = vector["inputs"]
    pim, level = inputs["pim"], inputs["memory_level"]
    assert inputs["password"].encode().hex() == inputs["password_utf8_hex"]
    password = check_password(
        {"password": inputs["password"], "password_nfkd_utf8_hex": inputs["password_nfkd_utf8_hex"]}
    )
    assert vector["argon2"] == {
        "variant": "Argon2id",
        "version": ARGON2_VERSION,
        "memory_kib": memory_kib(level),
        "passes": passes(pim),
        "lanes": LANES,
        "output_bytes": KEY_BYTES,
    }, vector["argon2"]
    argon2 = recorded_keys_by_salt(vector) if trust_keys else openssl_argon2id

    entropy = phrase_to_entropy(inputs["phrase"])
    x = pack(entropy)
    assert vector["packing"] == {
        "words": len(inputs["phrase"].split()),
        "entropy_hex": entropy.hex(),
        "verifier_hex": x[len(entropy):].hex(),
        "state_hex": x.hex(),
    }, vector["packing"]

    assert vector["encryption"]["input_state_hex"] == x.hex()
    y, forward_rounds = forward(x, argon2, password, pim, level)
    check_rounds(vector["encryption"]["rounds"], forward_rounds, "encryption")
    assert y.hex() == vector["encryption"]["output_state_hex"]
    assert entropy_to_phrase(y) == vector["container"]

    container_state = phrase_to_entropy(vector["container"])
    assert vector["decryption"]["input_state_hex"] == container_state.hex()
    recovered, inverse_rounds = inverse(container_state, argon2, password, pim, level)
    check_rounds(vector["decryption"]["rounds"], inverse_rounds, "decryption")
    assert recovered == x
    assert vector["decryption"]["output_state_hex"] == x.hex()
    recorded = [(c["words"], c["verified"], c["phrase"]) for c in vector["recovery"]]
    assert recorded == detected_recovery(recovered), "recovery"


def check_negative_case(case):
    """Recovery with a wrong password or setting: the recorded phrases or error."""
    check_header(case, NEGATIVE_SCHEMA)
    pim, level, words = case["pim"], case["memory_level"], case["words"]
    password = check_password(case)
    x, _ = inverse(phrase_to_entropy(case["container"]), openssl_argon2id, password, pim, level)
    expected, error = stated_recovery(x, words, case["name"]), None
    if expected is None:
        expected, error = [], "VERIFIER_MISMATCH"
    recorded = [(c["words"], c["verified"], c["phrase"]) for c in case["recovery"]]
    assert (recorded, case["error_code"]) == (expected, error), case["name"]
    assert read_as(x, 24) != "", case["name"]


def check_rounds(recorded, computed, label):
    assert len(recorded) == len(computed) == ROUNDS, label
    for entry, (index, before, salt_input, salt, key, mask_input, mask, after) in zip(
        recorded, computed
    ):
        assert entry["round"] == index, label
        assert entry["left_before_hex"] + entry["right_before_hex"] == before.hex(), (label, index)
        assert entry["salt_input_hex"] == salt_input.hex(), (label, index, "salt input")
        assert entry["salt_hex"] == salt.hex(), (label, index, "salt")
        assert entry["argon2_key_hex"] == key.hex(), (label, index, "key")
        assert entry["mask_input_hex"] == mask_input.hex(), (label, index, "mask input")
        assert entry["mask_hex"] == mask.hex(), (label, index, "mask")
        assert entry["left_after_hex"] + entry["right_after_hex"] == after.hex(), (label, index)


def sha256_file(path):
    with open(path, "rb") as file:
        return hashlib.sha256(file.read()).hexdigest()


def check_files(paths, trust_keys):
    """Checks each file and returns the (path, mode) of every file that was checked."""
    checked = []
    for path in paths:
        content = json.load(open(path, encoding="utf-8"))
        if isinstance(content, list):
            if trust_keys:
                print(f"{path}: skipped, negative cases need the full Argon2id check")
                continue
            for case in content:
                check_negative_case(case)
            print(f"{path}: all {len(content)} negative cases reproduced", flush=True)
        else:
            check_vector(content, trust_keys)
            how = "with the recorded Argon2id keys" if trust_keys else "in both directions"
            print(f"{path}: every value reproduced {how}", flush=True)
        checked.append((path, "recorded-argon2-keys" if trust_keys else "full"))
    return checked


def verifier_description():
    """What ran the check, so that a reader can tell which implementation agreed."""
    import cryptography
    from cryptography.hazmat.backends.openssl.backend import backend

    return {
        "program": "scripts/independent-suite3.py",
        "sha256": sha256_file(__file__),
        "python": platform.python_version(),
        "cryptography": cryptography.__version__,
        # The compiled module carries no __version__; the installed package names its version.
        "unicodedata2": (
            f"{importlib.metadata.version('unicodedata2')} (Unicode {unicode18.unidata_version})"
        ),
        "openssl": backend.openssl_version_text(),
    }


def update_record(record_path, checked):
    """Adds the checked files to the record, keeping entries that are still valid.

    Several checks may run side by side and add to one record, so the file is locked while it is
    read and rewritten (fcntl: this development script runs on Linux and macOS).
    """
    import fcntl

    verifier = verifier_description()
    with open(record_path, "a+", encoding="utf-8") as file:
        fcntl.flock(file, fcntl.LOCK_EX)
        file.seek(0)
        text = file.read()
        record = json.loads(text) if text else None
        if record is None or record.get("verifier") != verifier:
            record = {"schema": "mhfe-independent-verification-v1", "verifier": verifier, "files": []}

        entries = {entry["name"]: entry for entry in record["files"]}
        for path, mode in checked:
            name, digest = os.path.basename(path), sha256_file(path)
            entry = entries.get(name)
            if entry is None or entry["sha256"] != digest:
                entry = entries[name] = {"name": name, "sha256": digest, "checks": []}
            if mode not in entry["checks"]:
                entry["checks"] = sorted(entry["checks"] + [mode])
        record["files"] = [entries[name] for name in sorted(entries)]

        file.seek(0)
        file.truncate()
        json.dump(record, file, indent=2)
        file.write("\n")
    print(f"{record_path}: recorded {len(checked)} checked files")


def main(arguments):
    command, arguments = arguments[0], arguments[1:]
    if command == "encrypt":
        pim, level = settings(arguments, 2)
        container = encrypt(ask_phrase("Original seed phrase: "), ask_new_password(), pim, level)
        print(f"{container}\n{SUITE_ID.decode()}, PIM {pim}, memory level {level}")
        return
    if command == "decrypt":
        words, pim, level = settings(arguments, 3)
        readings, matching = decrypt(ask_phrase("Container phrase: "), ask("Password: "), words, pim, level)
        if not readings:
            sys.exit("no reading: the stated length does not match; check the password and settings")
        for length, verified, phrase in readings:
            print(f"{length} words, {'verified' if verified else 'not verified, compare a known address'}: {phrase}")
        others = sorted(set(matching) - {length for length, _, _ in readings})
        if others:
            print(f"the state also passes the check of {' and '.join(map(str, others))} words")
        return
    if command == "passwords":
        for path in arguments:
            check_password_cases(path)
        return
    if command != "vector":
        sys.exit(__doc__)
    trust = "--trust-argon2-keys" in arguments
    arguments = [value for value in arguments if value != "--trust-argon2-keys"]
    record_path = None
    if "--record" in arguments:
        position = arguments.index("--record")
        record_path = arguments[position + 1]
        del arguments[position : position + 2]
    checked = check_files(arguments, trust)
    if record_path is not None:
        update_record(record_path, checked)


if __name__ == "__main__":
    main(sys.argv[1:])
