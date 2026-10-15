// Validate the audit envelope and report pairing; this is not a proof checker.
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "../../..");
const evidence = resolve(root, "docs/audits/AUD-009-evidence");
const schema = JSON.parse(readFileSync(resolve(root, "../multi-chain-wallet-tools/docs/audit-report.schema.json")));
const file = resolve(root, "docs/audits/AUD-009-2026-10-15.json");
const data = JSON.parse(readFileSync(file, "utf8"));
const markdown = readFileSync(file.replace(/\.json$/, ".md"), "utf8");
const remediation = process.argv.slice(2);
assert(remediation.length === 0 || (remediation.length === 1 && remediation[0] === "--remediation"),
  "Usage: node validate.mjs [--remediation]");

function validate(value, rule, path = "root") {
  if (rule.$ref) {
    const target = rule.$ref.split("/").slice(1).reduce((node, key) => node[key], schema);
    validate(value, target, path);
  }
  for (const item of rule.allOf ?? []) validate(value, item, path);
  if ("const" in rule) assert.deepEqual(value, rule.const, path);
  if (rule.enum) assert(rule.enum.some((item) => JSON.stringify(item) === JSON.stringify(value)), path);
  if (rule.type) {
    const kinds = Array.isArray(rule.type) ? rule.type : [rule.type];
    const actual = value === null ? "null" : Array.isArray(value) ? "array" : typeof value;
    assert(kinds.includes(actual) || (kinds.includes("integer") && Number.isInteger(value)), path);
  }
  if (typeof value === "string") {
    if (rule.pattern) assert(new RegExp(rule.pattern).test(value), path);
    if (rule.minLength) assert(value.length >= rule.minLength, path);
  }
  if (typeof value === "number" && rule.minimum !== undefined) assert(value >= rule.minimum, path);
  if (Array.isArray(value) && rule.items) value.forEach((item, i) => validate(item, rule.items, `${path}.${i}`));
  if (value !== null && typeof value === "object" && !Array.isArray(value)) {
    for (const key of rule.required ?? []) assert(Object.hasOwn(value, key), `${path}.${key}`);
    for (const [key, child] of Object.entries(rule.properties ?? {})) {
      if (Object.hasOwn(value, key)) validate(value[key], child, `${path}.${key}`);
    }
  }
}

validate(data, schema);
const findings = [...data.findings, ...data.observations];
assert.equal(new Set(findings.map((item) => item.id)).size, findings.length);
for (const item of findings) assert(markdown.includes(item.id), item.id);
assert.equal(data.checks.coverage.length, 32);
for (const item of data.checks.coverage) assert(markdown.includes(item.checkId), item.checkId);
assert(!/\/home\/(?!user\/)[^/\s]+\//.test(JSON.stringify(data) + markdown), "Report privacy");
let checkedLinks = 0;
for (const target of [file.replace(/\.json$/, ".md"), resolve(root, "docs/audits/README.md"),
  resolve(root, "docs/audits/AUD-009-harnesses/README.md")]) {
  const source = readFileSync(target, "utf8").replace(/```[\s\S]*?```/g, "");
  for (const match of source.matchAll(/\]\(([^\s)]+)\)/g)) {
    if (/^[a-z]+:/i.test(match[1])) continue;
    assert(existsSync(resolve(dirname(target), match[1].split("#")[0])), match[1]);
    checkedLinks++;
  }
}
const initial = JSON.parse(readFileSync(resolve(evidence, "snapshot.json"), "utf8"));
const changed = initial.files.filter((item) => {
  // The index is audit-owned report publication, outside the reviewed baseline assessment.
  if (item.path === "docs/audits/README.md") return false;
  return createHash("sha256").update(readFileSync(resolve(root, item.path))).digest("hex") !== item.sha256;
});
if (!remediation.length) {
  assert.deepEqual(changed, [], "Reviewed source changed during audit; use --remediation for an authorized follow-up");
} else {
  const followup = data.remediationVerification;
  assert(followup && Object.keys(followup.fileHashes).length, "Missing follow-up identities");
  for (const [path, expected] of Object.entries(followup.fileHashes)) {
    assert.equal(createHash("sha256").update(readFileSync(resolve(root, path))).digest("hex"), expected, path);
  }
  assert.deepEqual(changed.filter((item) => !Object.hasOwn(followup.fileHashes, item.path)), [],
    "Unrecorded changes to the baseline");
  assert.equal(data.remediation.length, data.findings.length);
  assert.deepEqual(data.remediation.map((item) => item.id).sort(),
    data.findings.map((item) => item.id).sort(), "Remediation must cover every finding exactly once");
  for (const item of data.remediation) {
    assert(data.findings.some((finding) => finding.id === item.id), item.id);
    assert.equal(item.status, "verified", item.id);
  }
}
const result = { status: "passed", schema: "audit-report.schema.json", coverageItems: 32,
  localFileLinksChecked: checkedLinks,
  findingIds: data.findings.map((item) => item.id), changedBaselineFiles: changed,
  mode: remediation.length ? "remediation" : "baseline",
  limitation: "Checks the keywords used by this pinned schema and source identity, not mathematical correctness." };
writeFileSync(resolve(evidence, "report-validation.json"), `${JSON.stringify(result, null, 2)}\n`);
console.log(JSON.stringify(result));
