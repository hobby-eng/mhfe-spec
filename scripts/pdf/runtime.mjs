import { createRequire } from "node:module";
import { readFileSync, existsSync, realpathSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

/** Resolve the isolated, version-checked PDF toolchain without global Node packages. */
export class PdfRuntime {
  #require;
  #versions;
  #home;

  constructor() {
    const manifest = resolve(
      dirname(fileURLToPath(import.meta.url)),
      "../../tooling/pdf/package.json",
    );
    this.#home = process.env.MHFE_PDF_DEPENDENCIES || dirname(manifest);
    this.#require = createRequire(resolve(this.#home, "package.json"));
    this.#versions = JSON.parse(readFileSync(manifest, "utf8")).dependencies;
    for (const [name, version] of Object.entries(this.#versions)) {
      const actual = JSON.parse(readFileSync(this.path(`${name}/package.json`), "utf8")).version;
      if (actual !== version) throw new Error(`${name}: expected ${version}, found ${actual}`);
    }
  }

  path(name) {
    const file = resolve(this.#home, "node_modules", name);
    if (existsSync(file) && /\.[a-z]+$/.test(name)) return realpathSync(file);
    return this.#require.resolve(name);
  }

  load(name) {
    return this.#require(name);
  }

  async import(name) {
    return import(pathToFileURL(this.path(name)).href);
  }

  versions() {
    return { ...this.#versions };
  }
}
