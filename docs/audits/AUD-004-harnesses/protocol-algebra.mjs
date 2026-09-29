// AUD-004: specification-only analytical checks, using public synthetic inputs.
// The mock mask is intentionally NOT MHFE: no Argon2 or implementation is tested.
import assert from "node:assert/strict";
import { createHash, createHmac } from "node:crypto";

const STATE_BYTES = 32;
const HALF_BYTES = STATE_BYTES / 2;
const ROUND_COUNT = 12;
const SOURCE_BYTES = [16, 20, 24, 28, 32];
const MAX_PIM = 1023;
const MAX_MEMORY_LEVEL = 21;
const ARGON2_MAX_KIB = 2 ** 32 - 1;
const ARGON2_LANES = 4;
const FIXTURE_COUNT = 100;
const SUITE = "MHFE-BIP39-256-EXPERIMENTAL-3";
const PASSWORD = Buffer.from("AUD-004 synthetic public password", "utf8");

const sha256 = (value) => createHash("sha256").update(value).digest();
const xor = (left, right) => Buffer.from(left.map((value, i) => value ^ right[i]));
function be32(value) {
  const result = Buffer.alloc(4);
  result.writeUInt32BE(value);
  return result;
}

function pack(entropy) {
  return Buffer.concat([entropy, sha256(entropy).subarray(0, STATE_BYTES - entropy.length)]);
}

function shortMatches(state) {
  return SOURCE_BYTES.filter((length) => length < STATE_BYTES)
    .filter((length) => pack(state.subarray(0, length)).equals(state));
}

function mockMask(round, right) {
  return createHmac("sha256", PASSWORD)
    .update(Buffer.concat([be32(round), right]))
    .digest()
    .subarray(0, HALF_BYTES);
}

function forward(state, start = 0, end = ROUND_COUNT) {
  let left = state.subarray(0, HALF_BYTES);
  let right = state.subarray(HALF_BYTES);
  for (let round = start; round < end; round += 1) {
    [left, right] = [right, xor(left, mockMask(round, right))];
  }
  return Buffer.concat([left, right]);
}

function inverse(state, start = ROUND_COUNT - 1, end = 0) {
  let left = state.subarray(0, HALF_BYTES);
  let right = state.subarray(HALF_BYTES);
  for (let round = start; round >= end; round -= 1) {
    [left, right] = [xor(right, mockMask(round, left)), left];
  }
  return Buffer.concat([left, right]);
}

let roundTripCases = 0;
let knownPairPositions = 0;
for (let fixture = 0; fixture < FIXTURE_COUNT; fixture += 1) {
  const material = sha256(Buffer.from(`AUD-004 synthetic fixture ${fixture}`, "ascii"));
  for (const length of SOURCE_BYTES) {
    const entropy = material.subarray(0, length);
    const packed = pack(entropy);
    const container = forward(packed);
    assert.equal(packed.length, STATE_BYTES);
    assert.deepEqual(inverse(container), packed);
    if (length < STATE_BYTES) assert(shortMatches(packed).includes(length));
    for (let skipped = 0; skipped < ROUND_COUNT; skipped += 1) {
      const before = forward(packed, 0, skipped);
      const after = inverse(container, ROUND_COUNT - 1, skipped + 1);
      // The unused round's left output equals its right input, with 11 masks total.
      assert.deepEqual(before.subarray(HALF_BYTES), after.subarray(0, HALF_BYTES));
      assert.equal(skipped + (ROUND_COUNT - 1 - skipped), ROUND_COUNT - 1);
      knownPairPositions += 1;
    }
    roundTripCases += 1;
  }
}

const memoryKiB = Array.from({ length: MAX_MEMORY_LEVEL + 1 }, (_, level) =>
  (2 + (level % 2)) * 2 ** (20 + Math.floor(level / 2)));
for (const memory of memoryKiB) {
  assert(Number.isSafeInteger(memory));
  assert(memory <= ARGON2_MAX_KIB);
  assert.equal(memory % (4 * ARGON2_LANES), 0);
}
assert.equal(memoryKiB[0], 2 ** 21);
assert.equal(memoryKiB[MAX_MEMORY_LEVEL], 3 * 2 ** 30);
assert(2 * 2 ** 31 > ARGON2_MAX_KIB);
assert.equal(12 * (MAX_PIM + 1), 12288);

const zeroSource12 = Buffer.alloc(16);
const overlappingSource24 = pack(zeroSource12);
assert.deepEqual(pack(overlappingSource24), pack(zeroSource12));
assert.deepEqual(shortMatches(overlappingSource24), [16]);
assert.deepEqual(forward(pack(overlappingSource24)), forward(pack(zeroSource12)));

const saltFrame = Buffer.concat([
  Buffer.from(`${SUITE}/ROUND-SALT`, "ascii"), be32(0), be32(0), be32(0), Buffer.alloc(HALF_BYTES),
]);
const maskFrame = Buffer.concat([
  Buffer.from(`${SUITE}/ROUND-MASK`, "ascii"), be32(0), be32(0), be32(0), Buffer.alloc(HALF_BYTES),
]);
assert(!saltFrame.equals(maskFrame));
assert.equal(saltFrame.length, 68);
assert.equal(maskFrame.length, 68);

const newlineLikeCodePoints = [0x85, 0x2028, 0x2029];
for (const codePoint of newlineLikeCodePoints) {
  const scalar = String.fromCodePoint(codePoint);
  assert.equal(scalar.normalize("NFKD"), scalar);
  assert(!/[\n\r]/u.test(scalar));
}

console.log(JSON.stringify({
  scope: "Specification algebra only; no MHFE implementation or actual Argon2 invocation",
  runtime: { node: process.version, unicode: process.versions.unicode },
  roundTripCases,
  knownPairPositions,
  allMemoryLevelsChecked: memoryKiB.length,
  memoryGiB: memoryKiB.map((value) => value / 2 ** 20),
  maximumPassesPerRound: 12 * (MAX_PIM + 1),
  domainFrameBytes: saltFrame.length,
  overlap: {
    source12Entropy: zeroSource12.toString("hex"),
    source24Entropy: overlappingSource24.toString("hex"),
    autoDetectedWords: 12,
    interpretation: "Known design overlap: manual 24-word selection preserves a genuine 24-word source",
  },
  acceptedNewlineLikeCodePoints: newlineLikeCodePoints.map((value) => `U+${value.toString(16).toUpperCase()}`),
  result: "passed",
}, null, 2));
