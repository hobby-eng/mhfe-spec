// Independent, audit-only mathematical checks; no implementation imports or Argon2 calls.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';

const secondsPerDay = 86400;
const secondsPerYear = 365.25 * secondsPerDay;
const wordListSize = 7776;
const bip39Rate = 1_500_000;
console.log('Arithmetic uses declared hypothetical rates, not measured attack performance.');
for (const words of [2, 3, 4, 5]) {
  const space = wordListSize ** words;
  console.log(JSON.stringify({words, bits: Math.log2(space), mhfeOneCardDays: space / 2 / secondsPerDay,
    mhfeOneCardYears: space / 2 / secondsPerYear, mhfeThousandCardsYears: space / 2000 / secondsPerYear,
    bip39Seconds: space / 2 / bip39Rate, farmYears: space / 180 / secondsPerYear,
    botnetYears: space / 16000 / secondsPerYear}));
}
for (const bits of [30, 40]) {
  const space = 2 ** bits;
  console.log(JSON.stringify({bits, mhfeYears: space / 2 / secondsPerYear,
    thousandCardsDays: space / 2000 / secondsPerDay, bip39Minutes: space / 2 / bip39Rate / 60,
    farmDays: space / 180 / secondsPerDay, botnetHours: space / 16000 / 3600}));
}
console.log(JSON.stringify({costUpliftBits: Math.log2(bip39Rate),
  falseMatches21WordsFourDice: wordListSize ** 4 / 2 / 2 ** 32,
  falsePassphraseWorkToMhfeWork: wordListSize ** 5 / bip39Rate / 2 ** 32,
  independent30BitPairYears: (2 ** 30 / 2 + 2 ** 60 / 2 / bip39Rate) / secondsPerYear}));

// Independently sum all candidate completion costs for a small uniform search space.
for (const passwordCount of [1, 2, 7, 31]) {
  for (const pimCount of [1, 2, 4, 10]) {
    let hiddenTotal = 0;
    let knownTotal = 0;
    for (let pim = 0; pim < pimCount; pim++) {
      const hiddenSamples = [];
      const knownSamples = [];
      for (let rank = 1; rank <= passwordCount; rank++) {
        let hiddenWork = rank * (pim + 1);
        for (let earlier = 0; earlier < pim; earlier++) hiddenWork += passwordCount * (earlier + 1);
        hiddenSamples.push(hiddenWork);
        knownSamples.push(rank * (pim + 1));
      }
      const hiddenMean = hiddenSamples.reduce((a, b) => a + b, 0) / passwordCount;
      const knownMean = knownSamples.reduce((a, b) => a + b, 0) / passwordCount;
      assert.equal(hiddenMean, (passwordCount * (pim + 1) ** 2 + pim + 1) / 2);
      assert.equal(knownMean, (passwordCount + 1) * (pim + 1) / 2);
      hiddenTotal += hiddenMean;
      knownTotal += knownMean;
    }
    const ratio = (passwordCount * (2 * pimCount + 1) + 3) / (3 * (passwordCount + 1));
    assert.ok(Math.abs(hiddenTotal / knownTotal - ratio) < 1e-12);
  }
}
console.log('PASS: conditional and averaged hidden-PIM cost formulas by exhaustive finite sums.');

// Toy Feistel checks establish algebra only, never the security of a production cipher.
const rounds = 12;
const branchMask = 255;
function roundMask(password, index, right) {
  return createHash('sha256').update(`public audit toy:${password}:${index}:${right}`).digest()[0];
}
function forward(state, password, first = 0, end = rounds) {
  let [left, right] = state;
  for (let index = first; index < end; index++) [left, right] = [right, left ^ roundMask(password, index, right)];
  return [left, right];
}
function inverse(state, password, last = rounds - 1, first = 0) {
  let [left, right] = state;
  for (let index = last; index >= first; index--) [left, right] = [right ^ roundMask(password, index, left), left];
  return [left, right];
}
let correctFilters = 0;
let wrongFiltersPassed = 0;
for (let sample = 0; sample < 1000; sample++) {
  const source = [sample & branchMask, (sample >>> 8) & branchMask];
  const encrypted = forward(source, 'public correct key');
  assert.deepEqual(inverse(encrypted, 'public correct key'), source);
  for (let omitted = 0; omitted < rounds; omitted++) {
    const prefix = forward(source, 'public correct key', 0, omitted);
    const suffix = inverse(encrypted, 'public correct key', rounds - 1, omitted + 1);
    assert.equal(prefix[1], suffix[0]);
    assert.equal(omitted + (rounds - 1 - omitted), 11);
    correctFilters++;
    const wrongPrefix = forward(source, `public wrong key ${sample}`, 0, omitted);
    const wrongSuffix = inverse(encrypted, `public wrong key ${sample}`, rounds - 1, omitted + 1);
    wrongFiltersPassed += Number(wrongPrefix[1] === wrongSuffix[0]);
  }
}
console.log(JSON.stringify({toyBranchBits: 8, correctFilters, wrongFiltersPassed,
  interpretation: 'Algebraic validation only; toy false-match counts are not MHFE security evidence.'}));

const matchProbability = 1 / 2048;
const quantile = (probability) => Math.ceil(Math.log1p(-probability) / Math.log1p(-matchProbability));
console.log(JSON.stringify({cycleMedian: quantile(0.5), cycle95: quantile(0.95), cycle99: quantile(0.99),
  meanCycleLength: 1 / matchProbability, independentTimingEquality: matchProbability / (2 - matchProbability),
  meanMinTiming: 1 / (1 - (1 - matchProbability) ** 2)}));
assert.equal(quantile(0.5), 1420);
assert.equal(quantile(0.95), 6134);
assert.equal(quantile(0.99), 9430);
assert.equal(matchProbability / (2 - matchProbability), 1 / 4095);

// Standard cycle walking on this subset returns a fixed point. The documented rejection
// rule returns failure, so the wrapper is partial on the full subset.
const toyPermutation = [1, 0, 3, 2];
const toySubset = new Set([0, 2]);
const toyOutcomes = [];
for (const start of toySubset) {
  let current = toyPermutation[start];
  let steps = 1;
  while (!toySubset.has(current)) { current = toyPermutation[current]; steps++; }
  toyOutcomes.push({start, standardCycleWalking: current, documentedWrapper: current === start ? 'failure' : current, steps});
  assert.equal(current, start);
}
console.log(JSON.stringify({cycleWalkingRejectionCounterexample: toyOutcomes}));

const memoryKiB = (level) => (2 + level % 2) * 2 ** (20 + Math.floor(level / 2));
for (let level = 0; level <= 21; level++) {
  const memory = memoryKiB(level);
  assert.equal(memory % 16, 0);
  assert.ok(memory <= 2 ** 32 - 1);
}
assert.equal(memoryKiB(21), 3 * 2 ** 30);
assert.equal(memoryKiB(22), 2 ** 32);
console.log('PASS: all 22 memory levels fit RFC 9106 bounds and four-lane block alignment; next level exceeds the bound.');
console.log('PASS: appendix arithmetic and structural model checks completed.');
