import assert from "node:assert/strict";
import { resolve } from "node:path";
import { MarkdownDocument } from "./markdown.mjs";

/** Reproduce GitHub's rejected macro and Markdown damage without contacting GitHub. */
export class GitHubMathTests {
  run(runtime, root) {
    const parse = (text) =>
      new MarkdownDocument(runtime, {
        root,
        path: resolve(root, "README.md"),
        commit: "main",
      }).render(text);
    const cases = [];
    // KaTeX accepts this command, but GitHub's math-renderer rejects it before MathJax runs.
    assert.throws(() => parse("```math\n\\operatorname{top}(x)\n```"), /GitHub.*operatorname/);
    cases.push("GitHub-rejected operatorname is caught before PDF rendering");
    assert.throws(() => parse("```math\n\\Pr[A_{<t}]\n```"), /GitHub.*less-than/);
    const comparison = String.raw`\Pr[A_{\lt t}]`;
    assert.equal(parse("```math\n" + comparison + "\n```").math[0].source, comparison);
    cases.push("a less-than subscript uses a GitHub-safe LaTeX command");
    const latex = String.raw`\mathop{\mathrm{top}}\nolimits\!\left(\{x_1,x_2\}\right)`;
    for (const [name, text] of [
      ["protected inline", "$`" + latex + "`$"],
      ["math fence", "```math\n" + latex + "\n```"],
    ]) {
      const document = parse(text);
      assert.equal(document.math.length, 1, name);
      assert.equal(document.math[0].source, latex, name);
      assert.match(document.html, /class="mop"/);
      assert.ok(!document.html.includes("katex-error"));
      cases.push(`${name} preserves function spacing, braces and indices`);
    }
    assert.throws(() => parse("$`x_1$"), /Unclosed protected inline math/);
    cases.push("an unclosed protected math delimiter is rejected");
    for (const text of ["$" + latex + "$", "$$\n" + latex + "\n$$"]) {
      assert.throws(() => parse(text), /GitHub.*delimiter/);
    }
    cases.push("Markdown-sensitive LaTeX requires a protected delimiter");
    const literal = parse("`literal:\\operatorname{top}`\n\n```text\n\\operatorname{top}\n```");
    assert.equal(literal.math.length, 0);
    cases.push("a literal macro example remains code");
    return cases;
  }
}
