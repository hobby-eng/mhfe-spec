/** Keep a contents heading and its list together, or start an oversized list on a fresh page. */
export class ContentsLayout {
  async install(page) {
    await page.evaluate(() => {
      // Add the wrapper before Paged.js assigns node identities for fragmentation.
      const heading = document.querySelector("#source h2#contents");
      const list = heading?.nextElementSibling;
      if (list?.matches("ul,ol")) {
        const contents = document.createElement("nav");
        contents.className = "pdf-contents";
        contents.setAttribute("aria-labelledby", heading.id);
        heading.before(contents);
        contents.append(heading, list);
      }
      class ContentsPagination extends window.Paged.Handler {
        #source;
        #measurement;

        afterParsed(source) {
          this.#source = source.querySelector(".pdf-contents");
        }

        #measure(area) {
          const probe = document.createElement("div");
          Object.assign(probe.style, {
            position: "absolute",
            visibility: "hidden",
            width: `${area.getBoundingClientRect().width}px`,
          });
          const contents = this.#source.cloneNode(true);
          probe.append(contents);
          area.append(probe);
          try {
            return {
              height: contents.getBoundingClientRect().height,
              pageHeight: area.getBoundingClientRect().height,
            };
          } finally {
            probe.remove();
          }
        }

        beforePageLayout(page) {
          if (!this.#source || this.#measurement) return;
          this.#measurement = this.#measure(page.area);
          const { height, pageHeight } = this.#measurement;
          this.#source.dataset.contentsHeight = String(height);
          this.#source.dataset.contentsPageHeight = String(pageHeight);
          if (height > pageHeight) {
            this.#source.dataset.contentsOversized = "true";
            // Paged.js converts CSS break-before into this marker before page geometry exists.
            // Set it after measuring, but before any source node is placed on the first page.
            this.#source.dataset.breakBefore = "page";
          }
        }
      }
      window.Paged.registerHandlers(ContentsPagination);
    });
  }

  async inspect(page) {
    return page.evaluate(() => {
      const fragments = [...document.querySelectorAll(".pagedjs_page .pdf-contents")];
      if (!fragments.length) return null;
      const first = fragments[0];
      const oversized = first.dataset.contentsOversized === "true";
      const pages = fragments.map((node) =>
        Number(node.closest(".pagedjs_page").dataset.pageNumber),
      );
      if (!oversized && fragments.length !== 1)
        throw new Error("Contents that fit a page were split across pages");
      const firstPage = first.closest(".pagedjs_page");
      if (oversized && firstPage.querySelector("[data-proof-block]") !== first.querySelector("h2"))
        throw new Error("Oversized contents must start on a fresh page");
      return {
        pages,
        oversized,
        height: Number(first.dataset.contentsHeight),
        pageHeight: Number(first.dataset.contentsPageHeight),
      };
    });
  }
}
