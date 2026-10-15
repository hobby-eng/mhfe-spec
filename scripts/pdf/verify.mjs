import { readFileSync, writeFileSync } from "node:fs";
import { dirname, resolve } from "node:path";

/** Independently reopen each finished PDF and compare text, pages and rasterized output. */
export class PdfVerifier {
  #runtime;
  #pdfjs;
  #canvas;
  #png;
  #pixelmatch;

  constructor(runtime) {
    this.#runtime = runtime;
  }

  async open() {
    this.#canvas = this.#runtime.load("@napi-rs/canvas");
    this.#pdfjs = await this.#runtime.import("pdfjs-dist/legacy/build/pdf.mjs");
    this.#png = this.#runtime.load("pngjs").PNG;
    this.#pixelmatch = (await this.#runtime.import("pixelmatch")).default;
    return this;
  }

  #characters(value) {
    const normalized = value.normalize("NFKC").replace(/\s|[\u200b-\u200d\ufeff]/gu, "");
    const counts = new Map();
    for (const char of normalized) counts.set(char, (counts.get(char) ?? 0) + 1);
    return counts;
  }

  compareText(expected, actual) {
    if (/[\ufffd\u0000]/u.test(actual)) throw new Error("PDF contains a missing or invalid glyph");
    const wanted = this.#characters(expected);
    const found = this.#characters(actual);
    const differences = [];
    for (const char of new Set([...wanted.keys(), ...found.keys()])) {
      if ((wanted.get(char) ?? 0) !== (found.get(char) ?? 0))
        differences.push(
          `${JSON.stringify(char)}: ${wanted.get(char) ?? 0} -> ${found.get(char) ?? 0}`,
        );
    }
    if (differences.length)
      throw new Error(
        `PDF text differs from the laid-out page: ${differences.slice(0, 30).join(", ")}`,
      );
  }

  async verify(layout, directory, name) {
    const pdfRoot = dirname(this.#runtime.path("pdfjs-dist/package.json"));
    const pdf = await this.#pdfjs.getDocument({
      data: new Uint8Array(readFileSync(layout.pdfPath)),
      standardFontDataUrl: `${pdfRoot}/standard_fonts/`,
      cMapUrl: `${pdfRoot}/cmaps/`,
      cMapPacked: true,
      useSystemFonts: false,
      isEvalSupported: false,
    }).promise;
    try {
      if (pdf.numPages !== layout.pages.length)
        throw new Error(`PDF page count changed: ${layout.pages.length} -> ${pdf.numPages}`);
      const results = [];
      for (let i = 0; i < pdf.numPages; i++) {
        const page = await pdf.getPage(i + 1);
        const expected = layout.pages[i];
        const text = await page.getTextContent({ disableNormalization: true });
        this.compareText(expected.text, text.items.map((item) => item.str ?? "").join(""));
        const original = this.#png.sync.read(readFileSync(expected.beforeImage));
        const viewport = page.getViewport({
          scale: original.width / page.getViewport({ scale: 1 }).width,
        });
        if (Math.abs(viewport.height - original.height) > 2)
          throw new Error(`PDF page dimensions changed on page ${i + 1}`);
        const canvas = this.#canvas.createCanvas(original.width, original.height);
        await page.render({ canvas, canvasContext: canvas.getContext("2d"), viewport }).promise;
        const output = canvas.toBuffer("image/png");
        writeFileSync(resolve(directory, `${name}-after-${i + 1}.png`), output);
        const actual = this.#png.sync.read(output);
        const diff = new this.#png({ width: original.width, height: original.height });
        // A one-pixel box filter removes RGB subpixel antialiasing differences between
        // Chromium and PDF.js. Compare each mathematical region separately too: a local
        // error must not disappear into the much larger white area of a page.
        const filteredBefore = { ...original, data: this.#filtered(original) };
        const filteredAfter = { ...actual, data: this.#filtered(actual) };
        const changed = this.#pixelmatch(
          filteredBefore.data,
          filteredAfter.data,
          diff.data,
          original.width,
          original.height,
          { threshold: 0.25, includeAA: false },
        );
        const ratio = changed / (original.width * original.height);
        writeFileSync(resolve(directory, `${name}-diff-${i + 1}.png`), this.#png.sync.write(diff));
        // Independent rasterizers antialias differently; text equality catches even one missing symbol.
        if (ratio > 0.015)
          throw new Error(
            `PDF appearance changed on page ${i + 1}: ${(ratio * 100).toFixed(3)}% differing pixels`,
          );
        for (const box of expected.mathBoxes)
          this.#checkMathPixels(filteredBefore, filteredAfter, box);
        results.push({
          page: i + 1,
          text: "pass",
          rasterDifference: ratio,
          mathExpressions: expected.mathBoxes.length,
        });
        page.cleanup();
      }
      return results;
    } finally {
      await pdf.destroy();
    }
  }

  #filtered(image) {
    const output = Buffer.alloc(image.data.length);
    for (let y = 0; y < image.height; y++) {
      for (let x = 0; x < image.width; x++) {
        const sums = [0, 0, 0];
        let count = 0;
        for (let dy = -1; dy <= 1; dy++)
          for (let dx = -1; dx <= 1; dx++) {
            const px = x + dx,
              py = y + dy;
            if (px < 0 || py < 0 || px >= image.width || py >= image.height) continue;
            const offset = (py * image.width + px) * 4;
            for (let c = 0; c < 3; c++) sums[c] += image.data[offset + c];
            count++;
          }
        const offset = (y * image.width + x) * 4;
        for (let c = 0; c < 3; c++) output[offset + c] = Math.round(sums[c] / count);
        output[offset + 3] = 255;
      }
    }
    return output;
  }

  #checkMathPixels(before, after, box) {
    const left = Math.max(0, Math.floor(box.x));
    const top = Math.max(0, Math.floor(box.y));
    const width = Math.min(before.width - left, Math.ceil(box.width) + 1);
    const height = Math.min(before.height - top, Math.ceil(box.height) + 1);
    const a = Buffer.alloc(width * height * 4);
    const b = Buffer.alloc(a.length);
    for (let y = 0; y < height; y++) {
      const offset = ((top + y) * before.width + left) * 4;
      before.data.copy(a, y * width * 4, offset, offset + width * 4);
      after.data.copy(b, y * width * 4, offset, offset + width * 4);
    }
    const changed = this.#pixelmatch(a, b, null, width, height, {
      threshold: 0.25,
      includeAA: false,
    });
    if (changed / (width * height) > 0.12)
      throw new Error(`PDF math appearance changed: ${box.id}`);
  }
}
