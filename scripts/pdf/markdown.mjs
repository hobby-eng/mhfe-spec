import { Notation } from "./notation.mjs";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { dirname, extname, relative, resolve } from "node:path";

/** Compile explicit math only; invalid or unsupported LaTeX never falls back to visible source. */
export class MathCompiler {
  #katex;
  #expressions = [];

  constructor(runtime) {
    this.#katex = runtime.load("katex");
  }

  render(source, display, conversion = null, { protectedMarkdown = true } = {}) {
    if (!source.trim()) throw new Error("Empty math expression");
    // GitHub rejects this otherwise valid KaTeX command. Generated notation is local to the PDF;
    // only explicit source math is also interpreted by GitHub's renderer.
    if (!conversion && /\\operatorname\b/.test(source))
      throw new Error("GitHub rejects operatorname; use \\mathop{\\mathrm{name}}\\nolimits");
    // GitHub treats a raw less-than followed by a letter as markup, even inside a math fence.
    if (!conversion && source.includes("<"))
      throw new Error("GitHub can misread a literal less-than sign; use \\lt instead");
    // Dollar delimiters alone let Markdown consume escapes or split multiline expressions.
    if (!protectedMarkdown && /[\r\n]|\\[^A-Za-z]/.test(source))
      throw new Error("GitHub needs a protected delimiter: use $`...`$ or a math fence");
    // No document state, external resources or HTML can be introduced by an expression.
    if (
      /\\(?:href|url|includegraphics|html\w*|def|gdef|edef|xdef|let|global|newcommand|renewcommand)\b/.test(
        source,
      )
    ) {
      throw new Error(`Unsupported stateful or resource command in math: ${source}`);
    }
    const id = `math-${this.#expressions.length + 1}`;
    const rendered = this.#katex.renderToString(source, {
      displayMode: display,
      throwOnError: true,
      strict: "error",
      trust: false,
      output: "htmlAndMathml",
      maxExpand: 1000,
    });
    if (rendered.includes("katex-error")) throw new Error(`Math rendering failed: ${source}`);
    this.#expressions.push({
      id,
      source,
      display,
      conversion,
      sha256: createHash("sha256").update(source).digest("hex"),
    });
    return `<${display ? "div" : "span"} class="math-expression" data-math-id="${id}">${rendered}</${display ? "div" : "span"}>`;
  }

  inventory() {
    return [...this.#expressions];
  }
}

/** Parse Markdown, retain literal code, resolve links and embed local images for an offline build. */
export class MarkdownDocument {
  #parser;
  #math;
  #root;
  #path;
  #commit;
  #slugs = new Map();
  #codeSpans = 0;
  #codeBlocks = 0;
  #notation = new Notation();

  constructor(runtime, { root, path, commit }) {
    this.#root = root;
    this.#path = path;
    this.#commit = commit;
    this.#math = new MathCompiler(runtime);
    this.#parser = runtime.load("markdown-it")({ html: true, typographer: false, linkify: false });
    this.#rules();
  }

  #rules() {
    const parser = this.#parser;
    parser.core.ruler.after("inline", "notation_locations", (state) => {
      let line = 1;
      for (const token of state.tokens) {
        if (token.map) line = token.map[0] + 1;
        for (const child of token.children ?? []) child.meta = { ...child.meta, line };
      }
    });
    const text = parser.renderer.rules.text.bind(parser.renderer);
    parser.renderer.rules.text = (tokens, index, ...args) => {
      // Game labels in running prose also use subscripts; prose and URLs are otherwise literal.
      const content = tokens[index].content;
      const pattern = /(?<![\p{L}\p{N}])([ΓΔΘ]\d+(?:_j)?|(?:Bad|Early)_[A-Za-z])(?![\p{L}\p{N}])/gu;
      let end = 0,
        html = "";
      for (const match of content.matchAll(pattern)) {
        html += parser.utils.escapeHtml(content.slice(end, match.index));
        const game = match[0].match(/^([ΓΔΘ])(\d+)_j$/);
        const converted = this.#notation.convert(game ? `${game[1]}_{${game[2]},j}` : match[0]);
        html += this.#math.render(converted.latex, false, converted);
        end = match.index + match[0].length;
      }
      return end
        ? html + parser.utils.escapeHtml(content.slice(end))
        : text(tokens, index, ...args);
    };
    parser.inline.ruler.before("escape", "checked_math", (state, silent) => {
      if (state.src[state.pos] !== "$") return false;
      const start = state.pos;
      if (state.src[start + 1] === "$") throw new Error("Display math must be in its own block");
      if (state.src[start + 1] === "`") {
        const end = state.src.indexOf("`$", start + 2);
        if (end < 0) throw new Error("Unclosed protected inline math delimiter");
        if (!silent) {
          const token = state.push("checked_math", "", 0);
          token.content = state.src.slice(start + 2, end);
          token.meta = { protectedMath: true };
        }
        state.pos = end + 2;
        return true;
      }
      let end = start + 1;
      while (end < state.src.length) {
        if (state.src[end] === "\\") {
          end += 2;
          continue;
        }
        if (state.src[end] === "$") break;
        end++;
      }
      if (end >= state.src.length)
        throw new Error(`Unclosed inline math near: ${state.src.slice(start, start + 80)}`);
      if (!silent) {
        const token = state.push("checked_math", "", 0);
        token.content = state.src.slice(start + 1, end);
      }
      state.pos = end + 1;
      return true;
    });
    parser.renderer.rules.checked_math = (tokens, index) =>
      this.#math.render(tokens[index].content, false, null, {
        protectedMarkdown: tokens[index].meta?.protectedMath ?? false,
      });
    parser.block.ruler.before("fence", "checked_display_math", (state, start, end, silent) => {
      const first = state.src.slice(state.bMarks[start] + state.tShift[start], state.eMarks[start]);
      if (!first.startsWith("$$")) return false;
      if (silent) return true;
      let content = first.slice(2);
      let last = start;
      if (!content.trimEnd().endsWith("$$")) {
        for (last = start + 1; last < end; last++) {
          const line = state.src.slice(state.bMarks[last], state.eMarks[last]);
          content += `\n${line}`;
          if (line.trimEnd().endsWith("$$")) break;
        }
        if (last === end) throw new Error(`Unclosed display math at line ${start + 1}`);
      }
      const token = state.push("checked_display_math", "", 0);
      token.content = content.trimEnd().slice(0, -2).trim();
      token.map = [start, last + 1];
      state.line = last + 1;
      return true;
    });
    parser.renderer.rules.checked_display_math = (tokens, index) =>
      this.#math.render(tokens[index].content, true, null, { protectedMarkdown: false });
    const fence = parser.renderer.rules.fence.bind(parser.renderer);
    parser.renderer.rules.fence = (tokens, index, options, env, renderer) => {
      const info = tokens[index].info.trim();
      const automatic =
        ["", "text"].includes(info) && this.#notation.isMathBlock(tokens[index].content);
      if (["math", "ascii-math"].includes(info) || automatic) {
        const token = tokens[index];
        const closing = env.lines[token.map[1] - 1]?.trim() || "";
        if (
          closing.length < token.markup.length ||
          [...closing].some((char) => char !== token.markup[0])
        )
          throw new Error(`Unclosed math fence at line ${token.map[0] + 1}`);
        if (info === "ascii-math" || automatic) {
          const converted = this.#notation.block(token.content);
          return this.#math.render(converted.latex, true, converted);
        }
        return this.#math.render(token.content.trim(), true);
      }
      this.#codeBlocks++;
      return fence(tokens, index, options, env, renderer);
    };
    const code = parser.renderer.rules.code_inline.bind(parser.renderer);
    parser.renderer.rules.code_inline = (tokens, index, ...args) => {
      const token = tokens[index];
      let converted;
      try {
        converted = this.#notation.inline(token.content);
      } catch (error) {
        throw new Error(`line ${token.meta?.line}: ${token.content}: ${error.message}`);
      }
      if (converted?.latex) return this.#math.render(converted.latex, false, converted);
      this.#codeSpans++;
      if (converted?.literal !== undefined) token.content = converted.literal;
      return code(tokens, index, ...args);
    };
    parser.renderer.rules.image = (tokens, index) =>
      this.#image(tokens[index].attrGet("src"), tokens[index].content);
    for (const kind of ["html_block", "html_inline"]) {
      parser.renderer.rules[kind] = (tokens, index) => this.#html(tokens[index].content);
    }
    parser.renderer.rules.link_open = (tokens, index, options, env, renderer) => {
      const token = tokens[index];
      token.attrSet("href", this.#link(token.attrGet("href")));
      return renderer.renderToken(tokens, index, options);
    };
    parser.renderer.rules.heading_open = (tokens, index, options, env, renderer) => {
      const plain = tokens[index + 1].content.replace(/[`*_]/g, "");
      const base = plain
        .toLowerCase()
        .replace(/[^\p{L}\p{N}_\- ]/gu, "")
        .replace(/ /g, "-");
      const count = this.#slugs.get(base) ?? 0;
      this.#slugs.set(base, count + 1);
      tokens[index].attrSet("id", count ? `${base}-${count}` : base);
      return renderer.renderToken(tokens, index, options);
    };
  }

  #link(href) {
    if (href.startsWith("#")) return href;
    if (/^(https?:|mailto:)/.test(href)) return href;
    if (/^[a-z][a-z\d+.-]*:/i.test(href) || href.startsWith("//"))
      throw new Error(`Unsupported link: ${href}`);
    const [path, fragment] = href.split("#");
    const target = resolve(dirname(this.#path), decodeURIComponent(path));
    const rel = relative(this.#root, target);
    if (rel.startsWith("..")) throw new Error(`Link outside repository: ${href}`);
    return `https://github.com/hobby-eng/mhfe-spec/blob/${this.#commit}/${rel}${fragment ? `#${fragment}` : ""}`;
  }

  #image(src, alt) {
    const escape = this.#parser.utils.escapeHtml;
    // Badges retain their readable labels and links, without network requests.
    if (/^https:\/\/(img\.shields\.io|zenodo\.org)\//.test(src))
      return `<span class="badge-label">${escape(alt)}</span>`;
    if (/^[a-z]+:|^\/\//i.test(src)) throw new Error(`Remote image is not allowed: ${src}`);
    const path = resolve(dirname(this.#path), src);
    if (relative(this.#root, path).startsWith(".."))
      throw new Error(`Image outside repository: ${src}`);
    const types = { ".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg" };
    const type = types[extname(path).toLowerCase()];
    if (!type) throw new Error(`Unsupported local image: ${src}`);
    return `<img src="data:${type};base64,${readFileSync(path).toString("base64")}" alt="${escape(alt)}">`;
  }

  #html(html) {
    const cleaned = html.replace(/<!--[\s\S]*?-->/g, "").replace(/<img\b[^>]*>/gi, (tag) => {
      const src = tag.match(/\bsrc="([^"]+)"/i)?.[1];
      if (!src) throw new Error("An HTML image needs a quoted source");
      return this.#image(src, tag.match(/\balt="([^"]*)"/i)?.[1] ?? "");
    });
    for (const tag of cleaned.matchAll(/<\/?([a-z][a-z\d]*)\b([^>]*)>/gi)) {
      if (!new Set(["p", "sub", "sup", "br", "img"]).has(tag[1].toLowerCase()))
        throw new Error(`Unsupported raw HTML: ${tag[0]}`);
      if (tag[1].toLowerCase() !== "img" && tag[2].trim() && !/^\s+align="center"\s*$/.test(tag[2]))
        throw new Error(`Unsupported HTML attributes: ${tag[0]}`);
    }
    return cleaned;
  }

  render(source) {
    let html;
    try {
      html = this.#parser.render(source, { lines: source.split("\n") });
    } catch (error) {
      throw new Error(`${relative(this.#root, this.#path)}: ${error.message}`, { cause: error });
    }
    return {
      html,
      math: this.#math.inventory(),
      literalCode: { spans: this.#codeSpans, blocks: this.#codeBlocks },
      sourceSha256: createHash("sha256").update(source).digest("hex"),
    };
  }
}
