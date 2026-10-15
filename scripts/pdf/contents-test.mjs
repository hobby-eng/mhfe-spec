import assert from "node:assert/strict";

/** Exercise contents that fit, need a fresh page, or are longer than one complete page. */
export class ContentsRegressionTests {
  #parse;
  #directory;

  constructor(parse, directory) {
    this.#parse = parse;
    this.#directory = directory;
  }

  #fixture(paragraphs, entries) {
    return this.#parse(
      "# Contents regression fixture\n\n" +
        Array.from(
          { length: paragraphs },
          (_, i) =>
            `Preface paragraph ${i + 1}. This introduction reserves space before the contents. Its text wraps over several lines, just as the specification's preamble does.\n\n`,
        ).join("") +
        "## Contents\n\n" +
        Array.from({ length: entries }, (_, i) => `- [Contents entry ${i + 1}](#body)\n`).join("") +
        "\n## Body\n\nThe body follows the complete contents.\n",
    );
  }

  #pageOf(layout, text) {
    const page = layout.pages.findIndex((page) => page.text.includes(text));
    assert.ok(page >= 0, `Missing text: ${text}`);
    return page;
  }

  async run(browser, verifier) {
    const cases = [];
    const options = { directory: this.#directory, name: "contents", identity: "Contents fixture" };
    const compact = await browser.render(this.#fixture(1, 3), options);
    assert.equal(this.#pageOf(compact, "Contents entry 1"), 0);
    assert.equal(this.#pageOf(compact, "Contents entry 3"), 0);
    await verifier.verify(compact, this.#directory, "contents-compact");
    cases.push("short contents stay on the current page when they fit");

    const document = this.#fixture(10, 18);
    const moved = await browser.render(document, options);
    const first = this.#pageOf(moved, "Contents entry 1");
    assert.ok(first > this.#pageOf(moved, "Preface paragraph 10"));
    assert.equal(first, this.#pageOf(moved, "Contents entry 18"));
    assert.match(moved.pages[first].text.trimStart(), /^\d+ \/ \d+\s+Contents\b/);
    await verifier.verify(moved, this.#directory, "contents-moved");
    cases.push("contents that do not fit the remaining space move together to a fresh page");

    const long = await browser.render(this.#fixture(1, 70), options);
    const start = this.#pageOf(long, "Contents entry 1");
    assert.ok(start > this.#pageOf(long, "Preface paragraph 1"));
    assert.ok(this.#pageOf(long, "Contents entry 70") > start);
    assert.match(long.pages[start].text.trimStart(), /^\d+ \/ \d+\s+Contents\b/);
    await verifier.verify(long, this.#directory, "contents-long");
    cases.push("contents longer than a page begin on a fresh page and preserve every entry");
    await assert.rejects(
      browser.render(document, {
        ...options,
        fault: () => {
          const contents = document.querySelector(".pagedjs_page .pdf-contents");
          contents.after(contents.cloneNode(false));
        },
      }),
      /Contents that fit a page were split/,
    );
    cases.push("the build rejects a split contents block that could fit on one page");
    await assert.rejects(
      browser.render(this.#fixture(1, 70), {
        ...options,
        fault: () => {
          const contents = document.querySelector(".pagedjs_page .pdf-contents");
          const preceding = document.createElement("p");
          preceding.dataset.proofBlock = "unexpected-preface";
          preceding.textContent = "Text must not precede oversized contents on this page.";
          contents.before(preceding);
        },
      }),
      /Oversized contents must start on a fresh page/,
    );
    cases.push("the build rejects oversized contents starting after other page content");
    return cases;
  }
}
