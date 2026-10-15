import assert from "node:assert/strict";
import { AsciiMath } from "./ascii-math.mjs";
import { Notation } from "./notation.mjs";

/** Fixed expected notation and malformed inputs exercise the translator independently of PDF layout. */
export class NotationTests {
  run(runtime) {
    const cases = [];
    const katex = runtime.load("katex");
    for (const [source, expected] of [
      ['"mnemonic"', String.raw`\texttt{"mnemonic"}`],
      ["2^-128", String.raw`{2}^{- 128}`],
      ["x^(n-1)", String.raw`{x}^{n - 1}`],
      ["d_(n-1)", String.raw`{d}_{n - 1}`],
      ["alpha^k", String.raw`{\alpha}^{k}`],
      ["2e + s <= k", String.raw`2 e + s \le k`],
      ["5*d_2", String.raw`5 \cdot {d}_{2}`],
      ["p* = P", String.raw`{p}^{*} = P`],
      ["seed* ← {0,1}^512", String.raw`{\mathrm{seed}}^{*} \leftarrow {\{ 0 , 1 \}}^{512}`],
      ["R_0^{(1)}", String.raw`{R}_{0}^{( 1 )}`],
      ["N^A_P", String.raw`{N}_{P}^{A}`],
      ["Γ0", String.raw`\Gamma_{0}`],
      ["Pr_Γ0[win]", String.raw`{\operatorname{Pr}}_{\Gamma_{0}} [ \mathrm{win} ]`],
      ["X'", String.raw`{X}^{\prime}`],
      ["Θ0''", String.raw`{\Theta_{0}}^{\prime \prime}`],
      ["{0,1}^ENT", String.raw`{\{ 0 , 1 \}}^{\mathrm{ENT}}`],
      ["a/(b+c)", String.raw`a \mathbin{/} ( b + c )`],
    ]) {
      const actual = new AsciiMath(source).convert();
      assert.equal(actual.latex, expected, source);
      const html = katex.renderToString(actual.latex, { throwOnError: true, strict: "error" });
      assert.ok(html.includes('encoding="application/x-tex"'));
      cases.push(`notation: ${source}`);
    }
    for (const source of [
      "x^",
      "x_",
      "x^(n-1",
      "x_{i]",
      "x_i_j",
      "x^^2",
      "x_{}",
      "R_0^(1)",
      '"\\alpha"',
      "x+\\unknown",
      "x🙂y",
      "",
      "x".repeat(12001),
    ]) {
      assert.throws(() => new AsciiMath(source).convert(), undefined, source);
      cases.push(`refuses malformed notation: ${source.slice(0, 30)}`);
    }
    const n = new Notation();
    for (const literal of [
      "MHFE-REPAIR-1",
      "DS_SALT",
      "scripts/build-argon2-wasm.sh",
      "encrypt_key",
      "0x13",
      "literal:x^2",
    ])
      assert.ok(!n.inline(literal)?.latex, literal);
    assert.throws(() => n.inline("account_index"), /Ambiguous identifier/);
    assert.equal(n.inline("A, B, H").latex, "A , B , H");
    assert.equal(n.inline("Exp[·]").latex, String.raw`\operatorname{Exp} [ \cdot ]`);
    assert.equal(n.inline("f … 11").latex, String.raw`f \ldots 11`);
    assert.equal(n.inline("ascii:x^(n-1)").latex, String.raw`{x}^{n - 1}`);
    assert.equal(n.isMathBlock('SUITE_ID = ASCII("MHFE")'), false);
    assert.equal(n.isMathBlock("m(x) = d_0*x^(n-1) + d_1"), true);
    assert.throws(() => n.block("x = 2\ny = x^("), /Unclosed/);
    cases.push("literal identifiers, explicit notation and whole-block rejection");
    // Check semantics in the compiler's independent MathML tree, not just its LaTeX annotation.
    const inverse = katex.renderToString(new AsciiMath("2^-128").convert().latex);
    assert.match(inverse, /<msup><mn>2<\/mn><mrow><mo>−<\/mo><mn>128<\/mn><\/mrow><\/msup>/);
    const index = katex.renderToString(new AsciiMath("d_(n-1)").convert().latex);
    assert.match(index, /<msub>.*<mi>d<\/mi>.*<mi>n<\/mi><mo>−<\/mo><mn>1<\/mn>.*<\/msub>/);
    cases.push("MathML keeps a negative exponent and a compound subscript");
    return cases;
  }
}
