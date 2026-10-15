import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import {
  copyFileSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  writeFileSync,
} from "node:fs";
import { relative, resolve } from "node:path";
import { PdfRuntime } from "./runtime.mjs";
import { MarkdownDocument } from "./markdown.mjs";
import { BrowserLayout } from "./browser-layout.mjs";
import { PdfVerifier } from "./verify.mjs";
import { PdfRegressionTests } from "./test.mjs";

/** Build both documents from one checkout, exposing results only after every check succeeds. */
export class PdfBuild {
  #root;
  #output;
  #runtime;

  constructor(root) {
    this.#root = root;
    this.#output = resolve(root, "output/documents");
    this.#runtime = new PdfRuntime();
  }

  #hash(file) {
    return createHash("sha256")
      .update(readFileSync(resolve(this.#root, file)))
      .digest("hex");
  }

  #inputs() {
    const files = ["README.md", "docs/DESIGN-NOTES.md", "scripts/build-pdfs.mjs"];
    for (const directory of ["scripts/pdf", "tooling/pdf", "assets"]) {
      for (const entry of readdirSync(resolve(this.#root, directory), { withFileTypes: true })) {
        if (entry.isFile()) files.push(`${directory}/${entry.name}`);
      }
    }
    return Object.fromEntries(files.sort().map((file) => [file, this.#hash(file)]));
  }

  async run() {
    mkdirSync(this.#output, { recursive: true });
    const directory = mkdtempSync(resolve(this.#output, "build-"));
    const inputs = this.#inputs();
    const commit = execFileSync("git", ["rev-parse", "HEAD"], {
      cwd: this.#root,
      encoding: "utf8",
    }).trim();
    const report = {
      status: "running",
      commit,
      inputs,
      node: process.version,
      dependencies: this.#runtime.versions(),
      notes: [
        "Source SHA-256 values bind this build even when the checkout is uncommitted.",
        "Mathematical notation is transcribed to LaTeX; literal code and protocol strings are preserved.",
        "Automated checks do not prove mathematical meaning or replace visual review.",
      ],
      documents: [],
    };
    const browser = new BrowserLayout(this.#runtime);
    try {
      console.log("MHFE PDF · checking the converter with negative fixtures");
      const tests = await new PdfRegressionTests(this.#runtime, this.#root, directory).run();
      report.regressionTests = tests.cases;
      await browser.open();
      const verifier = await new PdfVerifier(this.#runtime).open();
      for (const [file, name] of [
        ["README.md", "mhfe-specification"],
        ["docs/DESIGN-NOTES.md", "mhfe-supplement"],
      ]) {
        console.log(`MHFE PDF · typesetting ${file}`);
        const source = readFileSync(resolve(this.#root, file), "utf8");
        const document = new MarkdownDocument(this.#runtime, {
          root: this.#root,
          path: resolve(this.#root, file),
          commit,
        }).render(source);
        const identity = `Source: ${file} · revision ${commit.slice(0, 12)} · SHA-256 ${document.sourceSha256}`;
        const layout = await browser.render(document, { directory, name, identity });
        console.log(`MHFE PDF · checking ${layout.pages.length} finished pages of ${name}`);
        const pages = await verifier.verify(layout, directory, name);
        report.documents.push({
          source: file,
          file: `${name}.pdf`,
          sha256: this.#hash(layout.pdfPath),
          browser: layout.browserVersion,
          sourceBlocks: layout.sourceBlocks,
          math: document.math,
          literalCode: document.literalCode,
          tables: layout.tables,
          contents: layout.contents,
          pages,
        });
      }
      if (JSON.stringify(inputs) !== JSON.stringify(this.#inputs()))
        throw new Error("Build inputs changed during conversion; rebuild from a stable checkout");
      report.status = "pass";
      for (const document of report.documents)
        copyFileSync(resolve(directory, document.file), resolve(this.#output, document.file));
      const checksums =
        report.documents.map((document) => `${document.sha256}  ${document.file}`).join("\n") +
        "\n";
      writeFileSync(resolve(this.#output, "SHA256SUMS"), checksums);
      writeFileSync(
        resolve(this.#output, "verification.json"),
        JSON.stringify(report, null, 2) + "\n",
      );
      console.log(`MHFE PDF · passed; output in ${relative(this.#root, this.#output)}`);
    } catch (error) {
      report.status = "fail";
      report.error = error.message;
      throw error;
    } finally {
      writeFileSync(
        resolve(directory, "verification.json"),
        JSON.stringify(report, null, 2) + "\n",
      );
      await browser.close();
    }
    return report;
  }
}
