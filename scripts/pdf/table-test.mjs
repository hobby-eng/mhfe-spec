import assert from "node:assert/strict";

/** Reproduce unequal-width mathematical columns and check the same tables after pagination. */
export class TableRegressionTests {
  #parse;
  #directory;

  constructor(parse, directory) {
    this.#parse = parse;
    this.#directory = directory;
  }

  #fixture() {
    const preface = Array.from(
      { length: 12 },
      (_, i) =>
        `Paragraph ${i + 1} before the tables. Repeated prose puts the table after page breaks, so its measurement must use one page's content area rather than the wider intermediate flow of overflow columns.\n\n`,
    ).join("");
    return this.#parse(
      `# Table regression fixture\n\n${preface}` +
        String.raw`

| Source words | ENT | $r$ | Packed state $X$ | Verifier acceptance |
| ---: | ---: | ---: | --- | ---: |
| 12 | 128 | 128 | $E_{128}\parallel\mathrm{Trunc}_{128}(\mathrm{SHA-256}(E_{128}))$ | $2^{-128}$ |
| 15 | 160 | 96 | $E_{160}\parallel\mathrm{Trunc}_{96}(\mathrm{SHA-256}(E_{160}))$ | $2^{-96}$ |
| 24 | 256 | 0 | $E_{256}$ | No internal verifier |

| Case | Bound | Conditions |
| --- | --- | --- |
| Short source | $2^{-128}$ | A longer explanation must wrap normally and have more space than the two short columns beside it. |

| Index | $p_i$ | Explanation |
| --- | --- | --- |
` +
        Array.from(
          { length: 48 },
          (_, i) =>
            `| ${i + 1} | $2^{-128}$ | This longer table repeats its mathematical heading on later pages, preserves every row, and keeps its columns aligned. |\n`,
        ).join(""),
    );
  }

  async run(browser, verifier) {
    const document = this.#fixture();
    const options = {
      directory: this.#directory,
      name: "tables",
      identity: "Table regression fixture",
    };
    const layout = await browser.render(document, options);
    const [packed, prose] = layout.tables;
    assert.equal(packed.columnWidths.length, 5);
    assert.ok(
      packed.columnWidths.slice(0, 3).every((width) => width < packed.columnWidths[3]),
      "each numeric column must be narrower than the packed-state formula column",
    );
    assert.ok(
      prose.columnWidths[2] > prose.columnWidths[0] + prose.columnWidths[1],
      "the prose column must receive the spare width",
    );
    assert.ok(layout.tables.length > 3, "the long table must span pages and repeat its heading");
    const parts = layout.tables.slice(2);
    for (const part of parts) {
      assert.match(part.heading, /Index/);
      part.columnWidths.forEach((width, index) =>
        assert.ok(
          Math.abs(width - parts[0].columnWidths[index]) < 1,
          "a table keeps column widths across page breaks",
        ),
      );
    }
    await verifier.verify(layout, this.#directory, "tables");
    const cases = [
      "unequal numeric, formula and prose columns fit their contents",
      "multi-page tables preserve column widths, mathematical headings and PDF text",
    ];
    for (const [name, fault, expected] of [
      [
        "equal-width columns that overflow are rejected",
        () => {
          const table = document.querySelector(".pagedjs_page table");
          table.querySelector("colgroup")?.remove();
          table.style.tableLayout = "fixed";
          for (const cell of table.querySelectorAll("th,td")) cell.style.width = "20%";
        },
        /Table cell overflow/,
      ],
      [
        "a formula crossing only a cell boundary is rejected",
        () => {
          const math = document.querySelector(
            ".pagedjs_page tbody td:nth-child(4) .math-expression",
          );
          const shift =
            math.closest("td").getBoundingClientRect().right -
            math.getBoundingClientRect().right +
            5;
          math.style.transform = `translateX(${shift}px)`;
        },
        /Table cell overflow/,
      ],
      [
        "ordinary text crossing only a cell boundary is rejected",
        () => {
          const cell = document.querySelector(".pagedjs_page tbody td");
          const text = document.createElement("span");
          text.textContent = cell.textContent;
          text.style.display = "inline-block";
          text.style.transform = `translateX(${cell.getBoundingClientRect().width}px)`;
          cell.replaceChildren(text);
        },
        /Table cell overflow/,
      ],
      [
        "duplicating a mathematical header on the same page is rejected",
        () => {
          const header = document.querySelector(".pagedjs_page thead .math-expression");
          header.after(header.cloneNode(true));
        },
        /Content changed|Math changed/,
      ],
    ]) {
      await assert.rejects(browser.render(document, { ...options, fault }), expected, name);
      cases.push(name);
    }
    return cases;
  }
}
