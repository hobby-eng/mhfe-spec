import { readFileSync, writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { TableLayout } from "./table-layout.mjs";

/** Paginate offline, check source coverage and geometry, and retain the pre-PDF pages as evidence. */
export class BrowserLayout {
  #runtime;
  #browser;
  #page;
  #errors = [];
  #requests = [];

  constructor(runtime) {
    this.#runtime = runtime;
  }

  async open() {
    this.#browser = await this.#runtime.load("playwright").chromium.launch({
      headless: true,
      executablePath: process.env.MHFE_PDF_CHROMIUM || undefined,
    });
    const context = await this.#browser.newContext({
      viewport: { width: 1200, height: 1500 },
      deviceScaleFactor: 1,
      offline: true,
    });
    await context.route(/https?:\/\//, (route) => {
      this.#requests.push(route.request().url());
      return route.abort();
    });
    this.#page = await context.newPage();
    // Paged.js has already imposed page geometry. Keep that layout when Chromium prints;
    // its legacy print-media height:100% rules otherwise truncate the content in Chromium.
    await this.#page.emulateMedia({ media: "screen" });
    this.#page.on("pageerror", (error) => this.#errors.push(error.message));
    this.#page.on("console", (message) => {
      if (message.type() === "error") this.#errors.push(message.text());
    });
    return this;
  }

  #styles() {
    const directory = dirname(this.#runtime.path("katex/dist/katex.min.css"));
    const katex = readFileSync(resolve(directory, "katex.min.css"), "utf8").replace(
      /url\(([^)]+)\)/g,
      (_, name) => {
        const file = name.replace(/["']/g, "");
        return `url(data:font/${file.split(".").at(-1)};base64,${readFileSync(resolve(directory, file)).toString("base64")})`;
      },
    );
    return `${katex}\n${readFileSync(new URL("print.css", import.meta.url), "utf8")}`;
  }

  async render(document, { directory, name, identity, fault }) {
    this.#errors = [];
    this.#requests = [];
    const escape = (s) =>
      s.replace(
        /[&<>"']/g,
        (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[c],
      );
    const html = `<!doctype html><html lang="en"><head><meta charset="utf-8">
      <meta http-equiv="Content-Security-Policy" content="default-src 'none'; img-src data:; font-src data:; style-src 'unsafe-inline'; script-src 'unsafe-inline'">
      <title>${escape(name)}</title><style>${this.#styles()}</style></head><body>
      <main id="source"><p class="build-identity">${escape(identity)}</p>${document.html}</main>
      <div id="pages"></div></body></html>`;
    writeFileSync(resolve(directory, `${name}.html`), html);
    await this.#page.setContent(html, { waitUntil: "load" });
    const before = await this.#page.evaluate(() => {
      for (const list of document.querySelectorAll("ul,ol")) {
        let i = Number(list.getAttribute("start") || 1);
        for (const child of list.children) {
          if (child.tagName !== "LI") continue;
          const marker = document.createElement("span");
          marker.className = "list-marker";
          marker.textContent = list.tagName === "OL" ? `${i++}. ` : "• ";
          child.prepend(marker);
        }
      }
      const root = document.querySelector("#source");
      let i = 0;
      for (const node of root.querySelectorAll("p,h1,h2,h3,h4,h5,h6,pre,th,td,li"))
        node.dataset.proofBlock = `block-${++i}`;
      const missing = [...root.querySelectorAll('a[href^="#"]')]
        .map((a) => a.getAttribute("href").slice(1))
        .filter((id) => !document.getElementById(id));
      if (missing.length) throw new Error(`Unresolved internal anchors: ${missing.join(", ")}`);
      // Own text excludes nested blocks and the accessibility copy of mathematical notation.
      window.pdfOwnText = (block) => {
        const walker = document.createTreeWalker(block, NodeFilter.SHOW_TEXT);
        let node;
        let value = "";
        while ((node = walker.nextNode())) {
          if (node.parentElement.closest(".katex-mathml")) continue;
          if (node.parentElement.closest("[data-proof-block]") === block) value += node.textContent;
        }
        return value.normalize("NFKC").replace(/\s|[\u200b-\u200d\ufeff]/gu, "");
      };
      return [...root.querySelectorAll("[data-proof-block]")].map((node) => ({
        id: node.dataset.proofBlock,
        text: window.pdfOwnText(node),
        repeatable: Boolean(node.closest("thead")),
      }));
    });
    await this.#page.evaluate(() => {
      window.PagedConfig = { auto: false };
    });
    await this.#page.addScriptTag({
      content: readFileSync(this.#runtime.path("pagedjs/dist/paged.polyfill.js"), "utf8"),
    });
    await new TableLayout().install(this.#page);
    await this.#page.evaluate(async () => {
      await document.fonts.ready;
      // Bound malformed-layout work independently of CI's overall time limit.
      let timer;
      try {
        await Promise.race([
          new window.Paged.Previewer().preview(
            document.querySelector("#source").innerHTML,
            undefined,
            document.querySelector("#pages"),
          ),
          new Promise((_, reject) => {
            timer = setTimeout(
              () => reject(new Error("Pagination exceeded five minutes")),
              300_000,
            );
          }),
        ]);
      } finally {
        clearTimeout(timer);
      }
      document.querySelector("#source")?.remove();
      const pages = [...document.querySelectorAll(".pagedjs_page")];
      if (pages.length > 300) throw new Error("Document exceeds the 300-page build limit");
      pages.forEach((page, i) => {
        const footer = page.querySelector(".pagedjs_margin-bottom-center .pagedjs_margin-content");
        if (!footer) throw new Error("Page footer is missing");
        footer.textContent = `${i + 1} / ${pages.length}`;
      });
      await document.fonts.ready;
    });
    // Fault injection is passed only by the negative regression tests, never the build CLI.
    if (fault) await this.#page.evaluate(fault);
    const tables = await new TableLayout().inspect(this.#page);
    const layout = await this.#inspect(before, document.math);
    layout.tables = tables;
    if (this.#errors.length || this.#requests.length)
      throw new Error(
        `Browser errors before printing: ${JSON.stringify({ errors: this.#errors, requests: this.#requests })}`,
      );
    const pdfPath = resolve(directory, `${name}.pdf`);
    for (let i = 0; i < layout.pages.length; i++) {
      const file = resolve(directory, `${name}-before-${i + 1}.png`);
      await this.#page
        .locator(".pagedjs_page")
        .nth(i)
        .screenshot({ path: file, animations: "disabled" });
      layout.pages[i].beforeImage = file;
    }
    await this.#page.pdf({
      path: pdfPath,
      printBackground: true,
      preferCSSPageSize: true,
      tagged: true,
      outline: true,
    });
    if (this.#errors.length || this.#requests.length)
      throw new Error(
        `Browser errors or network requests: ${JSON.stringify({ errors: this.#errors, requests: this.#requests })}`,
      );
    writeFileSync(
      resolve(directory, `${name}-layout.json`),
      JSON.stringify(layout, null, 2) + "\n",
    );
    return { pdfPath, ...layout, browserVersion: this.#browser.version() };
  }

  async #inspect(before, math) {
    return this.#page.evaluate(
      ({ before, math }) => {
        const pages = [...document.querySelectorAll(".pagedjs_page")];
        if (!pages.length) throw new Error("Pagination produced no pages");
        const failures = [];
        const expectedOrder = before.filter((block) => block.text).map((block) => block.id);
        const expectedIds = new Set(expectedOrder);
        const actualOrder = [
          ...new Set(
            [...document.querySelectorAll(".pagedjs_page [data-proof-block]")]
              .map((node) => node.dataset.proofBlock)
              .filter((id) => expectedIds.has(id)),
          ),
        ];
        if (JSON.stringify(actualOrder) !== JSON.stringify(expectedOrder))
          failures.push("Source blocks changed order during pagination");
        for (const block of before) {
          const nodes = [
            ...document.querySelectorAll(`.pagedjs_page [data-proof-block="${block.id}"]`),
          ];
          const chunks = nodes.map(window.pdfOwnText);
          if (block.repeatable && chunks.every((text) => text === block.text) && chunks.length)
            continue;
          if (chunks.join("") !== block.text)
            failures.push(
              `Content changed: ${block.id}: ${block.text.slice(0, 80)} => ${chunks.join("").slice(0, 80)}`,
            );
        }
        const expressions = [...document.querySelectorAll(".pagedjs_page [data-math-id]")];
        for (const item of math) {
          const matches = expressions.filter((node) => node.dataset.mathId === item.id);
          const repeatedHeader =
            matches.length > 1 &&
            matches.every((node) => node.closest("thead")) &&
            new Set(matches.map((node) => node.closest(".pagedjs_page"))).size === matches.length;
          if (
            (!repeatedHeader && matches.length !== 1) ||
            matches.some(
              (node) =>
                node.querySelector('annotation[encoding="application/x-tex"]')?.textContent !==
                item.source,
            )
          )
            failures.push(`Math changed or duplicated: ${item.id}`);
        }
        const result = pages.map((page) => {
          const rect = page.getBoundingClientRect();
          const content = page.querySelector(".pagedjs_page_content").getBoundingClientRect();
          const mathBoxes = [];
          for (const node of page.querySelectorAll(".math-expression, pre, table, img")) {
            const r = node.getBoundingClientRect();
            if (
              r.width &&
              (r.left < content.left - 1 ||
                r.right > content.right + 1 ||
                r.top < content.top - 1 ||
                r.bottom > content.bottom + 1)
            )
              failures.push(
                `Clipped ${node.tagName} on page ${page.dataset.pageNumber}: ${node.textContent.slice(0, 80)}`,
              );
            if (
              node.dataset.mathId &&
              (!r.width || !r.height || getComputedStyle(node).visibility === "hidden")
            )
              failures.push(`Invisible math: ${node.dataset.mathId}`);
            if (node.dataset.mathId) {
              // The outer inline/block box may fit while a KaTeX child overflows it.
              const walker = document.createTreeWalker(
                node.querySelector(".katex-html"),
                NodeFilter.SHOW_TEXT,
              );
              let textNode;
              while ((textNode = walker.nextNode())) {
                if (!textNode.textContent.replace(/[\s\u200b-\u200d\ufeff]/gu, "")) continue;
                const range = document.createRange();
                range.selectNodeContents(textNode);
                for (const glyph of range.getClientRects()) {
                  if (
                    glyph.left < content.left - 1 ||
                    glyph.right > content.right + 1 ||
                    glyph.top < content.top - 1 ||
                    glyph.bottom > content.bottom + 1
                  )
                    failures.push(
                      `Clipped math glyph: ${node.dataset.mathId} on page ${page.dataset.pageNumber}, ${JSON.stringify(textNode.textContent)}, overflow ${[content.left - glyph.left, glyph.right - content.right, content.top - glyph.top, glyph.bottom - content.bottom].map((x) => x.toFixed(2)).join(",")}`,
                    );
                }
              }
            }
            if (node.dataset.mathId)
              mathBoxes.push({
                id: node.dataset.mathId,
                x: r.left - rect.left,
                y: r.top - rect.top,
                width: r.width,
                height: r.height,
              });
          }
          return { width: rect.width, height: rect.height, text: page.innerText, mathBoxes };
        });
        if (failures.length) throw new Error(failures.slice(0, 20).join("\n"));
        return { pages: result, sourceBlocks: before.length, expressions: math.length };
      },
      { before, math },
    );
  }

  async close() {
    await this.#browser?.close();
  }
}
