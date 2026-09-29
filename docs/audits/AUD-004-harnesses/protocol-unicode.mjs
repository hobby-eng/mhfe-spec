// AUD-004: inspect the specification's Unicode rules with the named Node runtime.
// This does not inspect or exercise the MHFE utilities or their input handling.
import assert from "node:assert/strict";

const UNICODE_MAX = 0x10ffff;
const SURROGATE_FIRST = 0xd800;
const SURROGATE_LAST = 0xdfff;
const PASSWORD_LIMIT_BYTES = 1024;
const unassigned = /\p{General_Category=Unassigned}/u;
const utf8Length = (value) => Buffer.byteLength(value, "utf8");
assert.equal(process.versions.unicode, "17.0");

let scalarCount = 0;
let assignedCount = 0;
const lfCrImages = [];
for (let codePoint = 0; codePoint <= UNICODE_MAX; codePoint += 1) {
  if (codePoint >= SURROGATE_FIRST && codePoint <= SURROGATE_LAST) continue;
  scalarCount += 1;
  const scalar = String.fromCodePoint(codePoint);
  if (unassigned.test(scalar)) continue;
  assignedCount += 1;
  const normalized = scalar.normalize("NFKD");
  assert(normalized.length > 0);
  if (/[\r\n]/u.test(normalized)) lfCrImages.push(codePoint);
}
assert.deepEqual(lfCrImages, [0x0a, 0x0d]);
assert(unassigned.test("\ufdd0"));
assert(unassigned.test("\u0378"));
assert(!unassigned.test("\ue000"));
assert.equal("\u0000".normalize("NFKD"), "\u0000");

// U+FF21 contracts from three UTF-8 bytes to one ASCII byte under NFKD.
const contraction = "\uff21".repeat(PASSWORD_LIMIT_BYTES);
assert.equal(utf8Length(contraction), 3 * PASSWORD_LIMIT_BYTES);
assert.equal(utf8Length(contraction.normalize("NFKD")), PASSWORD_LIMIT_BYTES);

// U+00E9 expands from two UTF-8 bytes to three after decomposition.
const expansion = "\u00e9".repeat(342);
assert.equal(utf8Length(expansion), 684);
assert.equal(utf8Length(expansion.normalize("NFKD")), 1026);
assert.equal("\u00e9".normalize("NFKD"), "e\u0301".normalize("NFKD"));

console.log(JSON.stringify({
  scope: "Specification Unicode analysis only; no MHFE utilities or Argon2",
  runtime: { node: process.version, unicode: process.versions.unicode },
  scalarCount,
  assignedCount,
  lfCrImages: lfCrImages.map((value) => `U+${value.toString(16).toUpperCase()}`),
  noncharacterRejectedByCategory: true,
  unassignedRejectedByCategory: true,
  privateUseAcceptedByCategory: true,
  embeddedNulSurvivesNormalization: true,
  contraction: {
    rawUtf8Bytes: utf8Length(contraction),
    normalizedUtf8Bytes: utf8Length(contraction.normalize("NFKD")),
    expected: "accepted at the normalized 1024-byte boundary",
  },
  expansion: {
    rawUtf8Bytes: utf8Length(expansion),
    normalizedUtf8Bytes: utf8Length(expansion.normalize("NFKD")),
    expected: "rejected after normalization",
  },
  result: "passed",
}, null, 2));
