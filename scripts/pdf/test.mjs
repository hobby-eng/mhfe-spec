import { NotationTests } from "./notation-test.mjs";
import { TableRegressionTests } from "./table-test.mjs";
import { ContentsRegressionTests } from "./contents-test.mjs";
import { GitHubMathTests } from "./github-math-test.mjs";
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { PdfRuntime } from "./runtime.mjs";
import { MarkdownDocument } from "./markdown.mjs";
import { BrowserLayout } from "./browser-layout.mjs";
import { PdfVerifier } from "./verify.mjs";

/** Exercise the real conversion and deliberately damage each checked stage. */
export class PdfRegressionTests {
  #runtime;
  #root;
  #directory;

  constructor(runtime, root, directory) {
    this.#runtime = runtime;
    this.#root = root;
    this.#directory = mkdtempSync(resolve(directory, "regression-"));
  }

  #parse(text) {
    return new MarkdownDocument(this.#runtime, {
      root: this.#root,
      path: resolve(this.#root, "README.md"),
      commit: "main",
    }).render(text);
  }

  #fixture() {
    return this.#parse(
      String.raw`# Math regression fixture

Inline $x_1+2^{-128}$ and $\Gamma_0$. The minus sign and indices must survive.

$$\Pr[X=x]=\frac{1}{2^{128}}$$

~~~math
2e + s \le k
~~~

- First item
- Second item

| Check | Result |
| --- | --- |
| Probability | $p_1$ |
` +
        "\n\nLegacy `d_(n-1)` and `2^-128`.\n\n```text\nm(x) = d_0*x^(n-1) + d_(n-1)\ng(x) = (x + alpha^1)*(x + alpha^k)\n```\n" +
        Array.from(
          { length: 85 },
          (_, i) =>
            `\n\n## Pagination checkpoint ${i + 1}\n\nA complete paragraph must survive each page boundary. Its words, punctuation and position are checked again in the finished PDF. This repeated fixture exercises fractional-page rounding over a longer document.\n`,
        ).join(""),
    );
  }

  async run() {
    const cases = new NotationTests().run(this.#runtime);
    cases.push(...new GitHubMathTests().run(this.#runtime, this.#root));
    for (const [name, text, expected] of [
      ["unclosed inline math", "$x_1", /Unclosed/],
      ["unclosed display math", "$$\nx+1", /Unclosed/],
      ["unclosed math fence", "~~~math\nx+1", /Unclosed math fence/],
      ["unbalanced braces", "$\\frac{1}{2$", /KaTeX parse error/],
      ["unknown command", "$\\notARealCommand{x}$", /KaTeX parse error/],
      ["empty math", "$$\n$$", /Empty math/],
      ["external math resource", "$\\href{https://example.com}{x}$", /Unsupported/],
      ["stateful macro", "$\\def\\a{1}\\a$", /Unsupported/],
      ["raw script", "<script>bad()</script>", /Unsupported/],
      ["remote image", "![image](https://example.com/test.png)", /Remote image/],
    ]) {
      assert.throws(() => this.#parse(text), expected, name);
      cases.push(name);
    }
    const literal = this.#parse("`$x$` and `\\notARealCommand`\n\n```literal\n2^-b\n```\n");
    assert.equal(literal.math.length, 0);
    const labels = this.#parse("Game Γ0, Game Δ1_j and **Bad_j**.");
    assert.deepEqual(
      labels.math.map((item) => item.source),
      [String.raw`\Gamma_{0}`, String.raw`{\Delta}_{1 , j}`, String.raw`{\mathrm{Bad}}_{j}`],
    );
    cases.push("game and event labels in prose have proper indices");
    assert.deepEqual(literal.literalCode, { spans: 2, blocks: 1 });
    cases.push("literal code remains literal");
    const document = this.#fixture();
    assert.equal(document.math.length, 8);
    const browser = new BrowserLayout(this.#runtime);
    try {
      await browser.open();
      const options = {
        directory: this.#directory,
        name: "fixture",
        identity: "PDF regression fixture",
      };
      const layout = await browser.render(document, options);
      assert.ok(
        layout.pages.length >= 8,
        "the positive fixture must exercise many page boundaries",
      );
      const verifier = await new PdfVerifier(this.#runtime).open();
      await verifier.verify(layout, this.#directory, "fixture");
      cases.push("valid math survives pagination and PDF conversion");
      await assert.rejects(
        browser.render(document, {
          ...options,
          fault: () => {
            document.querySelector(".pagedjs_page h1").remove();
          },
        }),
        /Content changed|changed order/,
      );
      cases.push("missing source block is rejected");
      await assert.rejects(
        browser.render(document, {
          ...options,
          fault: () => {
            document.querySelector(".pagedjs_page [data-math-id]").remove();
          },
        }),
        /Content changed|Math changed/,
      );
      cases.push("missing math is rejected");
      await assert.rejects(
        browser.render(document, {
          ...options,
          fault: () => {
            const headings = document.querySelectorAll(".pagedjs_page h2");
            headings[1].before(headings[0]);
            headings[0].before(headings[1]);
          },
        }),
        /changed order/,
      );
      cases.push("reordered source blocks are rejected");
      await assert.rejects(
        browser.render(document, {
          ...options,
          fault: () => {
            document.querySelector(".pagedjs_page [data-math-id]").style.transform =
              "translateX(2000px)";
          },
        }),
        /Clipped/,
      );
      cases.push("clipped math is rejected");
      await assert.rejects(
        browser.render(document, {
          ...options,
          fault: () => {
            const glyph = document.querySelector(".pagedjs_page .katex-html .mord");
            glyph.style.display = "inline-block";
            glyph.style.transform = "translateX(2000px)";
          },
        }),
        /Clipped math glyph/,
      );
      cases.push("an overflowing glyph inside a fitting formula box is rejected");
      await assert.rejects(
        browser.render(document, {
          ...options,
          fault: () => {
            document.querySelector(".pagedjs_page [data-math-id]").style.display = "none";
          },
        }),
        /Invisible math/,
      );
      cases.push("invisible math is rejected");
      assert.throws(() => verifier.compareText("x + 2", "x + 3"), /differs/);
      assert.throws(() => verifier.compareText("x", "\ufffd"), /glyph/);
      cases.push("substituted or missing PDF glyph is rejected");
      // Keep text and PDF intact: the independent image check must fail on its own.
      const { PNG } = this.#runtime.load("pngjs");
      const before = readFileSync(layout.pages[0].beforeImage);
      const changed = PNG.sync.read(before);
      changed.data.fill(255);
      writeFileSync(layout.pages[0].beforeImage, PNG.sync.write(changed));
      await assert.rejects(
        verifier.verify(layout, this.#directory, "appearance-damaged"),
        /appearance changed/,
      );
      writeFileSync(layout.pages[0].beforeImage, before);
      cases.push("appearance changes fail independently of text checks");
      const damaged = resolve(this.#directory, "damaged.pdf");
      writeFileSync(damaged, readFileSync(layout.pdfPath).subarray(0, 100));
      await assert.rejects(
        verifier.verify({ ...layout, pdfPath: damaged }, this.#directory, "damaged"),
      );
      cases.push("truncated PDF is rejected");
      cases.push(
        ...(await new TableRegressionTests((text) => this.#parse(text), this.#directory).run(
          browser,
          verifier,
        )),
      );
      cases.push(
        ...(await new ContentsRegressionTests((text) => this.#parse(text), this.#directory).run(
          browser,
          verifier,
        )),
      );
    } finally {
      await browser.close();
    }
    return { cases, directory: this.#directory };
  }
}

if (process.argv[1]?.endsWith("/pdf/test.mjs")) {
  const root = process.cwd();
  const tests = new PdfRegressionTests(new PdfRuntime(), root, resolve(root, "output"));
  console.log(await tests.run());
}
