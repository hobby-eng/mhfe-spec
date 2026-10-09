"""AUD-007: bounded independent Suite 4 and recovery-vector checks.

Run from mhfe_spec: python3 -B docs/audits/AUD-007-harnesses/vectors_probe.py
Requires only Python's standard library and the public BIP39 wordlist from the workspace's
Cargo registry. Override it with --wordlist <english.rs> for another public Rust wordlist file.
No production Python/Rust code is imported; no Argon2 computation is performed. The round
equations, recovery table and GF(2^11) repair decoder are independently interpreted from README.md.
Writes a hash-bound result in the ignored AUD-007-evidence directory and exits nonzero on failure.
"""

import argparse
import hashlib
import hmac
import itertools
import json
import re
import subprocess
import sys
import unicodedata
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "docs/audits/AUD-007-evidence"
WORD_COUNTS = (12, 15, 18, 21, 24)
ROUND_COUNT = 12
HALF_FIELD_BITS = 11
FIELD_SIZE = 1 << HALF_FIELD_BITS
FIELD_POLYNOMIAL = FIELD_SIZE | (1 << 2) | 1  # x^11 + x^2 + 1, README repair profile.
SUITE4_ID = b"MHFE-BIP39-LP-EXPERIMENTAL-4"
WORDLIST_SHA256 = "2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda"


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def utc_now():
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def require(condition, reason):
    if not condition:
        raise AssertionError(reason)


class CapturedInputs:
    """Own one stable byte read per input, and reject concurrent changes before accepting results."""

    def __init__(self):
        self._bytes = {}

    def read(self, path):
        path = path.resolve()
        if path not in self._bytes:
            raw = path.read_bytes()
            require(raw == path.read_bytes(), f"input changed during capture: {path.name}")
            self._bytes[path] = raw
        return self._bytes[path]

    def json(self, path):
        def unique_keys(pairs):
            result = {}
            for key, value in pairs:
                require(key not in result, f"duplicate JSON key: {key}")
                result[key] = value
            return result

        return json.loads(self.read(path), object_pairs_hook=unique_keys)

    def hashes(self):
        result = {}
        for path, raw in self._bytes.items():
            try:
                label = str(path.relative_to(ROOT))
            except ValueError:
                label = str(path).replace(str(Path.home()), "/home/user")
            result[label] = sha256(raw)
        return dict(sorted(result.items()))

    def changed(self):
        return [str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else p.name
                for p, raw in self._bytes.items() if p.read_bytes() != raw]


class Bip39:
    def __init__(self, raw):
        self._words = re.findall(r'"([a-z]+)"', raw.decode())
        self._indexes = {word: index for index, word in enumerate(self._words)}
        require(len(self._words) == len(self._indexes) == 2048, "BIP39 wordlist length")
        canonical = ("\n".join(self._words) + "\n").encode()
        require(sha256(canonical) == WORDLIST_SHA256, "BIP39 public wordlist digest")

    def symbols(self, phrase):
        return [self._indexes[word] for word in phrase.split()]

    def phrase(self, entropy):
        bits = len(entropy) * 8
        checksum_bits = bits // 32
        checksum = hashlib.sha256(entropy).digest()[0] >> (8 - checksum_bits)
        packed = (int.from_bytes(entropy, "big") << checksum_bits) | checksum
        count = (bits + checksum_bits) // HALF_FIELD_BITS
        return " ".join(self._words[(packed >> (HALF_FIELD_BITS * i)) & (FIELD_SIZE - 1)]
                        for i in range(count - 1, -1, -1))

    def entropy(self, phrase):
        symbols = self.symbols(phrase)
        require(len(symbols) in WORD_COUNTS, "unsupported BIP39 word count")
        packed = 0
        for symbol in symbols:
            packed = (packed << HALF_FIELD_BITS) | symbol
        entropy_bits = len(symbols) * HALF_FIELD_BITS * 32 // 33
        checksum_bits = entropy_bits // 32
        entropy = (packed >> checksum_bits).to_bytes(entropy_bits // 8, "big")
        require(self.phrase(entropy) == phrase, "BIP39 checksum/canonical encoding")
        return entropy

    def source_check(self, phrase):
        seed = hashlib.pbkdf2_hmac("sha512", unicodedata.normalize("NFKD", phrase).encode(),
                                   b"mnemonic", 2048, dklen=64)
        return sha256(b"MHFE-WALLET-CHECK-SEED-1" + (256).to_bytes(4, "big") + seed)


class Suite4Replay:
    def __init__(self, words):
        self._words = words

    @staticmethod
    def messages(memory, pim, entropy_bits, index, half):
        settings = b"".join(value.to_bytes(4, "big")
                            for value in (memory, pim, entropy_bits, index))
        return (SUITE4_ID + b"/ROUND-SALT" + settings + half,
                SUITE4_ID + b"/ROUND-MASK" + settings + half)

    @staticmethod
    def xor(left, right):
        require(len(left) == len(right), "XOR width")
        return bytes(a ^ b for a, b in zip(left, right))

    def transcript(self, vector):
        inputs = vector["inputs"]
        entropy = self._words.entropy(inputs["phrase"])
        bits = len(entropy) * 8
        half_bytes = len(entropy) // 2
        require(vector["schema"] == "mhfe-suite-4-vector-v1", "Suite 4 schema")
        require(vector["suite_id"].encode() == SUITE4_ID, "Suite 4 domain")
        require(vector["state"] == {"words": len(inputs["phrase"].split()),
                                    "entropy_bits": bits, "half_bytes": half_bytes,
                                    "state_hex": entropy.hex()}, "Suite 4 state")
        require(inputs["password"].encode().hex() == inputs["password_utf8_hex"], "password UTF8")
        require(unicodedata.normalize("NFKD", inputs["password"]).encode().hex()
                == inputs["password_nfkd_utf8_hex"], "password NFKD")
        memory, pim = inputs["memory_level"], inputs["pim"]
        parameters = {"variant": "Argon2id", "version": 19,
                      "memory_kib": (2 + memory % 2) * 2 ** (20 + memory // 2),
                      "passes": ROUND_COUNT * (pim + 1), "lanes": 4, "output_bytes": 32}
        require(vector["argon2"] == parameters, "recorded Argon2 parameter mapping")
        keys = {}
        output = None
        for direction in ("encryption", "decryption"):
            data = vector[direction]
            state = entropy if direction == "encryption" else output
            require(state.hex() == data["input_state_hex"], direction + " initial state")
            left, right = state[:half_bytes], state[half_bytes:]
            indexes = list(range(ROUND_COUNT))
            if direction == "decryption":
                indexes.reverse()
            require([r["round"] for r in data["rounds"]] == indexes, direction + " round indexes")
            for record in data["rounds"]:
                index = record["round"]
                require(left.hex() == record["left_before_hex"] and
                        right.hex() == record["right_before_hex"], "round input halves")
                half = right if direction == "encryption" else left
                salt_message, mask_message = self.messages(memory, pim, bits, index, half)
                require(salt_message.hex() == record["salt_input_hex"], "salt domain/message")
                require(mask_message.hex() == record["mask_input_hex"], "mask domain/message")
                salt = hashlib.blake2b(salt_message, digest_size=32).digest()[:16]
                require(salt.hex() == record["salt_hex"], "BLAKE2b-256 truncated salt")
                key = bytes.fromhex(record["argon2_key_hex"])
                require(len(key) == 32, "recorded Argon2 key width")
                if direction == "encryption":
                    keys[index] = key
                else:
                    require(keys[index] == key, "inverse recorded key differs")
                mask = hmac.digest(key, mask_message, "sha256")[:half_bytes]
                require(mask.hex() == record["mask_hex"], "HMAC mask truncated to half width")
                if direction == "encryption":
                    left, right = right, self.xor(left, mask)
                else:
                    left, right = self.xor(right, mask), left
                require(left.hex() == record["left_after_hex"] and
                        right.hex() == record["right_after_hex"], "round output halves")
            result = left + right
            require(result.hex() == data["output_state_hex"], direction + " final state")
            if direction == "encryption":
                output = result
                require(output != entropy, "fixed point must be refused")
                require(self._words.phrase(output) == vector["container"], "container BIP39 encoding")
                require(self._words.entropy(vector["container"]) == output, "container BIP39 decoding")
            else:
                require(result == entropy, "recovered entropy")
                require(vector["recovery"] == {"words": len(inputs["phrase"].split()),
                                               "verified": False, "phrase": inputs["phrase"]},
                        "unverified same-length recovery label")

    @staticmethod
    def admitted(container_words, chosen_words=None, selected_suite=None):
        inferred_suite = 3 if container_words == 24 else 4
        suite_ok = selected_suite is None or selected_suite == inferred_suite
        length_ok = chosen_words is None or container_words == 24 or chosen_words == container_words
        return suite_ok and length_ok

    def validation(self, data):
        require(data["schema"] == "mhfe-suite-4-validation-cases-v1", "Suite 4 validation schema")
        separated = []
        for case in data["ent_separation"]:
            bits = case["words"] * HALF_FIELD_BITS * 32 // 33
            require(bits == case["entropy_bits"], "ENT separation width")
            half = bytes.fromhex(case["half_hex"])
            require(len(half) * 8 == bits // 2, "ENT separation half width")
            salt_message, mask_message = self.messages(case["memory_level"], case["pim"], bits,
                                                       case["round"], half)
            require(salt_message.hex() == case["salt_input_hex"], "ENT separation salt message")
            require(mask_message.hex() == case["mask_input_hex"], "ENT separation mask message")
            require(hashlib.blake2b(salt_message, digest_size=32).digest()[:16].hex()
                    == case["salt_hex"], "ENT separation salt")
            require(hmac.digest(bytes.fromhex(case["key_hex"]), mask_message, "sha256")[:len(half)].hex()
                    == case["mask_hex"], "ENT separation mask")
            separated.append((bits, salt_message, mask_message))
        require({b for b, _, _ in separated} == {128, 160, 192, 224}, "ENT separation coverage")
        expected = {(c, w, s) for c in WORD_COUNTS for w in (None,) + WORD_COUNTS
                    for s in (None, 3, 4) if (w is not None or s is not None)
                    and not self.admitted(c, w, s)}
        found = set()
        encrypt_refusals = 0
        for case in data["refusals"]:
            count = len(case["text"].split())
            self._words.entropy(case["text"])
            require(case["expected"] == "rejected", "refusal expectation")
            if case["operation"] == "encrypt-same-length":
                require(count == 24, "only 24-word source is inadmissible to Suite 4")
                encrypt_refusals += 1
                continue
            require(case["operation"] == "decrypt", "unknown refusal operation")
            key = (count, case.get("words"), case.get("suite"))
            require(key not in found, "duplicate recovery refusal")
            require(not self.admitted(*key), "refusal contradicted by recovery table")
            found.add(key)
        require(found == expected and len(found) == 62, "complete 62-case recovery refusal matrix")
        require(encrypt_refusals == 1, "Suite 4 source refusal count")
        groups = {"lengthOnly": sum(w is not None and s is None for _, w, s in found),
                  "suiteOnly": sum(w is None and s is not None for _, w, s in found),
                  "lengthAndSuite": sum(w is not None and s is not None for _, w, s in found)}
        return {"entSeparation": len(separated), "sourceRefusals": encrypt_refusals,
                "recoveryRefusals": len(found), "refusalGroups": groups}

    def negative_structure(self, cases, original):
        require(len(cases) == 4, "Suite 4 recovery case count")
        for case in cases:
            require(case["container"] == original["container"], "negative container basis")
            require(unicodedata.normalize("NFKD", case["password"]).encode().hex()
                    == case["password_nfkd_utf8_hex"], "negative password encoding")
            if case["words"]:
                require(not self.admitted(12, case["words"]), "mismatched length admitted")
                require(case["error_code"] == "LENGTH_CHOICE_NOT_APPLICABLE" and
                        case["recovery"] == [], "mismatched-length refusal")
            else:
                require(case["error_code"] is None and len(case["recovery"]) == 1,
                        "wrong password/settings cannot authenticate Suite 4")
                reading = case["recovery"][0]
                require(reading["words"] == 12 and reading["verified"] is False,
                        "wrong password/settings unverified same-length label")
                require(reading["phrase"] != original["inputs"]["phrase"], "negative changed phrase")
                self._words.entropy(reading["phrase"])
        return {"structurallyChecked": 4, "tableDerivedRefusal": 1,
                "wrongInputOutputsNotRecomputed": 3}


class RepairDecoder:
    """Syndrome equations plus bounded location enumeration, independently of the Rust decoder."""

    @staticmethod
    def multiply(left, right):
        result = 0
        while right:
            if right & 1:
                result ^= left
            right >>= 1
            left <<= 1
            if left & FIELD_SIZE:
                left ^= FIELD_POLYNOMIAL
        return result

    def power(self, base, exponent):
        result = 1
        while exponent:
            if exponent & 1:
                result = self.multiply(result, base)
            base = self.multiply(base, base)
            exponent >>= 1
        return result

    def syndromes(self, symbols, parity):
        result = []
        for exponent in range(1, parity + 1):
            root = self.power(2, exponent)
            value = 0
            for symbol in symbols:
                value = self.multiply(value, root) ^ symbol
            result.append(value)
        return result

    def solve(self, positions, length, syndromes):
        count = len(positions)
        if not count:
            return [] if all(x == 0 for x in syndromes) else None
        rows = [[self.power(2, (row + 1) * (length - 1 - pos)) for pos in positions]
                + [syndromes[row]] for row in range(len(syndromes))]
        for col in range(count):
            pivot = next((r for r in range(col, len(rows)) if rows[r][col]), None)
            if pivot is None:
                return None
            rows[col], rows[pivot] = rows[pivot], rows[col]
            inverse = self.power(rows[col][col], FIELD_SIZE - 2)
            rows[col] = [self.multiply(value, inverse) for value in rows[col]]
            for row in range(len(rows)):
                if row != col and rows[row][col]:
                    multiplier = rows[row][col]
                    rows[row] = [a ^ self.multiply(multiplier, b)
                                 for a, b in zip(rows[row], rows[col])]
        if any(all(x == 0 for x in row[:-1]) and row[-1] for row in rows):
            return None
        return [rows[i][-1] for i in range(count)]

    def repair(self, damaged, parity):
        erasures = [i for i, value in enumerate(damaged) if value is None]
        intact = [i for i, value in enumerate(damaged) if value is not None]
        base = [0 if value is None else value for value in damaged]
        syndromes = self.syndromes(base, parity)
        candidates = set()
        for errors in range((parity - len(erasures)) // 2 + 1):
            for unknown in itertools.combinations(intact, errors):
                positions = erasures + list(unknown)
                magnitudes = self.solve(positions, len(base), syndromes)
                if magnitudes is None:
                    continue
                candidate = base.copy()
                for pos, value in zip(positions, magnitudes):
                    candidate[pos] ^= value
                if all(value == 0 for value in self.syndromes(candidate, parity)):
                    candidates.add(tuple(candidate))
        require(len(candidates) == 1, "unique bounded RS repair")
        return list(candidates.pop())


def current_recovery(words, state, selected):
    detected = []
    for count in WORD_COUNTS[:-1]:
        entropy_bytes = count * HALF_FIELD_BITS * 32 // 33 // 8
        entropy, tail = state[:entropy_bytes], state[entropy_bytes:]
        if hashlib.sha256(entropy).digest()[:len(tail)] == tail:
            detected.append({"words": count, "verified": True, "phrase": words.phrase(entropy)})
    full = {"words": 24, "verified": False, "phrase": words.phrase(state)}
    if selected == 24:
        return detected + [full]
    if selected in [reading["words"] for reading in detected]:
        return [reading for reading in detected if reading["words"] == selected]
    if selected and not detected:
        return []
    return detected if len(detected) == 1 else detected + [full]


def recovery_expectations(inputs, words):
    readme = inputs.read(ROOT / "vectors/suite3/README.md").decode()
    zero = inputs.json(ROOT / "vectors/suite3/zero-12.json")
    cases = inputs.json(ROOT / "vectors/suite3/negative-cases.json")
    selected = next(case for case in cases if case["name"] == "selected-24-words")
    state = bytes.fromhex(zero["decryption"]["output_state_hex"])
    require(selected["container"] == zero["container"], "selected-24 container basis")
    require(selected["password"] == zero["inputs"]["password"], "selected-24 password basis")
    current = current_recovery(words, state, 24)
    require([reading["words"] for reading in current] == [12, 24], "current selected-24 reading order")
    require(current[1] == selected["recovery"][0], "historical 24-word reading retained")
    stated = next((case for case in cases if case["name"] == "stated-24-words"), None)
    if stated is not None:
        for field in ("container", "password", "password_nfkd_utf8_hex", "pim", "memory_level", "words"):
            require(stated[field] == selected[field], "current and historical recovery input " + field)
        require(stated["recovery"] == current and stated["error_code"] is None,
                "current stated-24 fixture reproduces the complete recovery expectation")
    for order, reading in enumerate(current, 1):
        rows = [line.split("|") for line in readme.splitlines() if reading["phrase"] in line]
        require(any(row[1].strip() == str(order) and row[2].strip() == str(reading["words"])
                    for row in rows), "current recovery expectation table matches decoded state")
    prefixes = {}
    for case in cases:
        for reading in case["recovery"]:
            if reading["words"] == 24:
                words.entropy(reading["phrase"])
                prefix = words.source_check(reading["phrase"])[:8]
                require(prefix in readme, "current negative source-check digest prefix")
                prefixes[case["name"]] = prefix
    expected_names = {"wrong-password-detect", "wrong-pim", "wrong-memory-level",
                      "wrong-password-24-words", "selected-24-words"}
    if stated is not None:
        expected_names.add("stated-24-words")
    require(set(prefixes) == expected_names, "Suite 3 current source-check case names")
    qualified = (("not the complete" in readme and "historical recovery rules" in readme)
                 or ("historical single reading" in readme and "current\nconformance case" in readme))
    require(qualified, "historical recovery array must be explicitly qualified")
    return {"selected24CurrentReadings": current, "historicalArrayQualified": qualified,
            "sourceCheckPrefixes": prefixes, "sourceCheckRecords": len(prefixes),
            "distinctSourceCheckPrefixes": len(set(prefixes.values())),
            "currentFixtureChecked": stated is not None,
            "limitation": "Uses recorded decrypted state and recovered phrases; no new Argon2 replay."}


def repair_examples(inputs, words):
    profile_text = inputs.read(ROOT / "vectors/profiles/README.md").decode()
    source = inputs.json(ROOT / "vectors/suite3/zero-12.json")["container"]
    phrase_symbols = words.symbols(source)
    card = words.symbols("shaft pupil patient jewel")
    require("shaft pupil patient jewel" in profile_text, "published four-word card")
    pristine = phrase_symbols + card
    decoder = RepairDecoder()
    require(decoder.syndromes(pristine, len(card)) == [0] * len(card), "published card codeword roots")
    examples = (
        ("two erasures", {3: None, 17: None}),
        ("one error and one erasure", {10: words.symbols("zoo")[0], 5: None}),
        ("two errors at the bound", {3: words.symbols("zoo")[0], 17: words.symbols("abandon")[0]}),
    )
    result = []
    for name, changes in examples:
        damaged = pristine.copy()
        for one_based, value in changes.items():
            damaged[one_based - 1] = value
        repaired = decoder.repair(damaged, len(card))
        require(repaired == pristine, name + " restores exact public codeword")
        words.entropy(source)
        result.append({"case": name, "repairedPositions": sorted(changes),
                       "restoredWords": [source.split()[i - 1] for i in sorted(changes)]})
    return result


def profile_inventory(inputs):
    text = inputs.read(ROOT / "vectors/profiles/README.md").decode()
    source_section = text.split("## Optional source check:", 1)[1].split("## Repair words:", 1)[0]
    repair_section = text.split("## Repair words:", 1)[1].split("## Password check word:", 1)[0]
    password_section = text.split("## Password check word:", 1)[1]
    source_rows = [line for line in source_section.splitlines() if re.match(r"\|\s*\d+\s*\|", line)]
    repair_rows = [line.split("|") for line in repair_section.splitlines()
                   if line.startswith("| `")]
    password_rows = [line for line in password_section.splitlines()
                     if re.match(r"\|\s*`[1-6]{5} ", line)]
    repair_cards = sum(len(re.findall(r"`[^`]+`", row[2])) for row in repair_rows)
    require(len(source_rows) == 2, "source-profile vector row inventory")
    require(len(repair_rows) == 4 and repair_cards == 16, "repair-card inventory")
    require(len(password_rows) == 4, "password-profile vector row inventory")
    require("an erased third word is recovered" in password_section, "password erasure inventory")
    return {"sourceCheckRows": len(source_rows), "repairCards": repair_cards,
            "repairExamples": 3, "passwordRows": len(password_rows), "passwordErasureExample": 1,
            "otherProfileCalculations": "Owned by coordinator's independent profiles_probe.py."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    default = ROOT.parent / "workingspace/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bip39-3.0.0/src/language/english.rs"
    parser.add_argument("--wordlist", type=Path, default=default)
    args = parser.parse_args()
    started = utc_now()
    inputs = CapturedInputs()
    words = Bip39(inputs.read(args.wordlist))
    inputs.read(ROOT / "README.md")
    inputs.read(ROOT / "vectors/suite4/README.md")
    suite = Suite4Replay(words)
    positive = {}
    for path in sorted((ROOT / "vectors/suite4").glob("*.json")):
        data = inputs.json(path)
        if isinstance(data, dict) and data.get("schema") == "mhfe-suite-4-vector-v1":
            suite.transcript(data)
            positive[path.name] = data
    require(len(positive) == 10, "Suite 4 positive transcript count")
    manifest = inputs.read(ROOT / "vectors/suite4/SHA256SUMS").decode()
    entries = [line.split() for line in manifest.splitlines()]
    require(len(entries) == 11, "Suite 4 manifest entry count")
    require({name for _, name in entries} == set(positive) | {"negative-cases.json"}, "Suite 4 manifest coverage")
    for expected, name in entries:
        require(sha256(inputs.read(ROOT / "vectors/suite4" / name)) == expected, "manifest digest " + name)
    validation = suite.validation(inputs.json(ROOT / "vectors/suite4/validation-cases.json"))
    negative = suite.negative_structure(inputs.json(ROOT / "vectors/suite4/negative-cases.json"),
                                       positive["same-length-zero-12.json"])
    # Faults stay in memory: ensure independent exact assertions can actually reject a wrong transcript.
    rejected_faults = []
    for field in ("mask_hex", "salt_input_hex"):
        mutated = json.loads(json.dumps(positive["same-length-zero-12.json"]))
        record = mutated["encryption"]["rounds"][0]
        record[field] = (bytes.fromhex(record[field])[0] ^ 1).to_bytes(1, "big").hex() + record[field][2:]
        try:
            suite.transcript(mutated)
        except AssertionError:
            rejected_faults.append(field)
        else:
            raise AssertionError("mutated transcript accepted: " + field)
    coverage = [{"file": name, "words": v["state"]["words"],
                 "pim": v["inputs"]["pim"], "memoryLevel": v["inputs"]["memory_level"],
                 "nonzeroEntropy": any(bytes.fromhex(v["state"]["state_hex"]))}
                for name, v in positive.items()]
    require({item["words"] for item in coverage} == set(WORD_COUNTS[:-1]),
            "positive Suite 4 coverage of all four widths")
    result = {"startedAt": started, "outcome": "passed",
              "reviewedCommit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().strip(),
              "suite4": {"positiveTranscripts": len(positive), "roundRecords": len(positive) * ROUND_COUNT * 2,
                         "argon2Recomputed": False, "manifestEntries": len(entries),
                         "validation": validation, "negativeCases": negative,
                         "faultsRejected": rejected_faults, "positiveCoverage": coverage},
              "suite3CurrentExpectations": recovery_expectations(inputs, words),
              "repairDecoding": repair_examples(inputs, words),
              "profileCoverage": profile_inventory(inputs),
              "python": sys.version.split()[0], "unicodeDatabase": unicodedata.unidata_version,
              "inputHashes": inputs.hashes(), "concurrentInputChanges": inputs.changed()}
    require(not result["concurrentInputChanges"], "inputs changed during verification")
    result["inputFingerprint"] = sha256("".join(name + "\0" + digest + "\n"
                                                   for name, digest in result["inputHashes"].items()).encode())
    result["endedAt"] = utc_now()
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / "vectors-result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
