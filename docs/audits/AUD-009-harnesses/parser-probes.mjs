// Independent expectations for the public Markdown-to-mathematics entry point.
import { MarkdownDocument } from "../../../scripts/pdf/markdown.mjs";
import { PdfRuntime } from "../../../scripts/pdf/runtime.mjs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "../../..");
const runtime = new PdfRuntime();
const results = [];

function convert(source) {
  const document = new MarkdownDocument(runtime, { root, path: "README.md", commit: "audit" });
  const output = document.render(`\`ascii:${source}\``);
  return output;
}

function mathml(source) {
  const output = convert(source);
  return output.html.match(/<math[\s\S]*?<\/math>/)?.[0]
    .replace(/<annotation[\s\S]*?<\/annotation>/g, "");
}

function check(name, test) {
  try {
    const detail = test();
    results.push({ name, passed: true, detail });
  } catch (error) {
    results.push({ name, passed: false, error: error.message });
  }
}

function requireCondition(condition, message) {
  if (!condition) throw new Error(message);
}

check("grouped multiplication keeps its operator", () => {
  const output = convert("g(x) = (x + alpha^1)*(x + alpha^k)");
  const latex = output.math[0].source;
  requireCondition(latex.includes("\\cdot") && !latex.includes("^{*}"), latex);
  return latex;
});
check("quoted tilde remains distinct from quoted space", () => {
  const tilde = mathml('"a~b"');
  const space = mathml('"a b"');
  requireCondition(tilde !== space, `Identical rendered MathML: ${tilde}`);
});
check("unmatched closing delimiter cannot be a script argument", () => {
  const accepted = [];
  for (const source of ["x^)", "x_]"]) {
    try { convert(source); accepted.push(source); } catch { /* Expected refusal. */ }
  }
  requireCondition(accepted.length === 0, `Accepted malformed expressions: ${accepted.join(", ")}`);
});
check("ambiguity validation is independent of script order", () => {
  let refused = false;
  try { convert("R^(1)_0"); } catch { refused = true; }
  requireCondition(refused, "R^(1)_0 was accepted although R_0^(1) is refused as ambiguous");
});
check("algorithm-name hyphen is literal", () => {
  const output = mathml("SHA-256(E)");
  requireCondition(!output.includes("<mo>−</mo>"), output);
});
check("spaced multiplication and explicit labelled powers work", () => {
  const product = convert("(x + 1) * (x - 1)").math[0].source;
  requireCondition(product.includes("\\cdot"), product);
  convert("R_0^{(1)}");
});
check("unclosed groups still fail", () => {
  let refused = false;
  try { convert("x^(n-1"); } catch { refused = true; }
  requireCondition(refused, "Unclosed group accepted");
});

console.log(JSON.stringify({ dependencies: runtime.versions(), results }, null, 2));
process.exitCode = results.some((item) => !item.passed) ? 1 : 0;
