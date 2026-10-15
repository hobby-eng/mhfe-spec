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
      ["2*(x+1)", String.raw`2 \cdot ( x + 1 )`],
      ["(x+1)*(x-1)", String.raw`( x + 1 ) \cdot ( x - 1 )`],
      ["p* = P", String.raw`{p}^{*} = P`],
      ["e*(p)", String.raw`{e}^{*} ( p )`],
      ["p_i*", String.raw`{p}_{i}^{*}`],
      ["seed* ← {0,1}^512", String.raw`{\mathrm{seed}}^{*} \leftarrow {\{ 0 , 1 \}}^{512}`],
      ["R_0^{(1)}", String.raw`{R}_{0}^{( 1 )}`],
      ["R^{(1)}_0", String.raw`{R}_{0}^{( 1 )}`],
      ["R^1_0", String.raw`{R}_{0}^{1}`],
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
      "R^(1)_0",
      "x^)",
      "x_]",
      "x^}",
      "x_⌋",
      "x^+)",
      "x^-{}",
      "x^*",
      "x^/",
      '"\\alpha"',
      '"a{b}"',
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
    this.#literalMathml(katex, cases);
    return cases;
  }

  #literalMathml(katex, cases) {
    const mathml = (source) =>
      katex
        .renderToString(new AsciiMath(source).convert().latex)
        .match(/<math[\s\S]*?<\/math>/)[0]
        .replace(/<annotation[\s\S]*?<\/annotation>/g, "");
    for (const literal of ["~", "^", "%", "&", "#", "_", "$"]) {
      const source = `"a${literal}b"`;
      assert.ok(
        mathml(source)
          .replace(/<[^>]*>/g, "")
          .includes(`a${literal === "&" ? "&amp;" : literal}b`),
        source,
      );
      assert.notEqual(mathml(source), mathml('"a b"'), source);
      cases.push(`MathML keeps the quoted character ${literal}`);
    }
    for (const name of [
      "SHA-256",
      "BLAKE2b-256",
      "HMAC-SHA-256",
      "HMAC-SHA-512",
      "PBKDF2-HMAC-SHA512",
    ]) {
      assert.ok(mathml(`${name}(E)`).includes(`<mtext>${name}</mtext>`), name);
      cases.push(`MathML keeps the literal algorithm name ${name}`);
    }
    for (const source of ["(x+1)*(x-1)", "2*(x+1)", "g(x) = (x + alpha^1)*(x + alpha^k)"]) {
      assert.match(mathml(source), /<mo>⋅<\/mo>/, source);
      assert.ok(!mathml(source).includes("<mo>∗</mo>"), source);
      cases.push(`MathML keeps multiplication in ${source}`);
    }
  }
}
