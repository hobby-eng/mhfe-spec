/** Check cell boundaries separately from page boundaries: a formula can cross only a column. */
export class TableLayout {
  async install(page) {
    await page.evaluate(() => {
      class TablePagination extends window.Paged.Handler {
        #sources = new Map();
        #widths = new Map();

        afterParsed(source) {
          [...source.querySelectorAll("table")].forEach((table, index) => {
            table.dataset.pdfTable = String(index + 1);
            this.#sources.set(table.dataset.pdfTable, table);
          });
        }

        #measure(source, wrapper) {
          const area = wrapper.closest(".pagedjs_page").querySelector(".pagedjs_page_content");
          const probe = document.createElement("div");
          Object.assign(probe.style, {
            position: "absolute",
            visibility: "hidden",
            // The flowing wrapper can span several overflow columns before Paged.js cuts it.
            // Its bounding width is not the width available on one printed page.
            width: `${area.getBoundingClientRect().width}px`,
          });
          const table = source.cloneNode(true);
          probe.append(table);
          // Paged.js scopes print styles to its page containers. A probe in document.body
          // would measure with different fonts and table rules than the printed table.
          wrapper.append(probe);
          try {
            // Measure the complete table at the actual page width, not a partial page's rows.
            return [...table.rows[0].cells].map((cell) => cell.getBoundingClientRect().width);
          } finally {
            probe.remove();
          }
        }

        layout(wrapper) {
          for (const table of wrapper.querySelectorAll("table[data-pdf-table]")) {
            const key = table.dataset.pdfTable;
            const source = this.#sources.get(key);
            if (!this.#widths.has(key)) this.#widths.set(key, this.#measure(source, wrapper));
            table.style.tableLayout = "fixed";
            // Paged.js splits tables into DOM fragments. Insert headings before its overflow
            // calculation so their height participates in pagination, not after the page is full.
            if (table.dataset.splitFrom && !table.tHead && source.tHead)
              table.prepend(source.tHead.cloneNode(true));
            // Keep the source DOM's structure: inserting a new colgroup can become a page-break
            // target with no source counterpart, causing Paged.js to lose the remaining document.
            for (const row of table.rows)
              [...row.cells].forEach((cell, index) => {
                cell.style.width = `${this.#widths.get(key)[index]}px`;
              });
          }
        }
      }
      window.Paged.registerHandlers(TablePagination);
    });
  }

  async inspect(page) {
    return page.evaluate(() => {
      // One CSS pixel covers border collapse and fractional glyph-position rounding.
      const tolerance = 1;
      const failures = [];
      const tables = [...document.querySelectorAll(".pagedjs_page table")].map((table) => {
        const pageNumber = Number(table.closest(".pagedjs_page").dataset.pageNumber);
        const rows = [...table.rows];
        for (const [rowIndex, row] of rows.entries()) {
          for (const [columnIndex, cell] of [...row.cells].entries()) {
            const box = cell.getBoundingClientRect();
            const style = getComputedStyle(cell);
            const bounds = {
              left: box.left + parseFloat(style.borderLeftWidth) + parseFloat(style.paddingLeft),
              right:
                box.right - parseFloat(style.borderRightWidth) - parseFloat(style.paddingRight),
              top: box.top + parseFloat(style.borderTopWidth),
              bottom: box.bottom - parseFloat(style.borderBottomWidth),
            };
            const check = (rect, text) => {
              if (!rect.width || !rect.height) return;
              if (
                rect.left < bounds.left - tolerance ||
                rect.right > bounds.right + tolerance ||
                rect.top < bounds.top - tolerance ||
                rect.bottom > bounds.bottom + tolerance
              )
                failures.push(
                  `Table cell overflow on page ${pageNumber}, row ${rowIndex + 1}, column ${columnIndex + 1}: ${text.slice(0, 100)}`,
                );
            };
            const walker = document.createTreeWalker(cell, NodeFilter.SHOW_TEXT);
            let node;
            while ((node = walker.nextNode())) {
              if (node.parentElement.closest(".katex-mathml")) continue;
              const text = node.textContent;
              const start = text.search(/[^\s\u200b-\u200d\ufeff]/u);
              if (start < 0) continue;
              const range = document.createRange();
              range.setStart(node, start);
              range.setEnd(node, text.trimEnd().length);
              for (const rect of range.getClientRects()) check(rect, text);
            }
            // Covers non-text parts too, such as fraction bars, roots and images.
            for (const element of cell.querySelectorAll(".math-expression, .katex-html, img, pre"))
              for (const rect of element.getClientRects()) check(rect, element.textContent);
          }
        }
        return {
          id: table.dataset.pdfTable,
          page: pageNumber,
          heading: table.tHead?.innerText || rows[0]?.innerText || "",
          rows: rows.length,
          cells: rows.reduce((total, row) => total + row.cells.length, 0),
          columnWidths: [...(rows[0]?.cells || [])].map(
            (cell) => cell.getBoundingClientRect().width,
          ),
        };
      });
      if (failures.length) throw new Error([...new Set(failures)].slice(0, 20).join("\n"));
      return tables;
    });
  }
}
