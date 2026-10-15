const SYMBOLS = {
  "<=": "\\le",
  "≤": "\\le",
  ">=": "\\ge",
  "≥": "\\ge",
  "!=": "\\ne",
  "≠": "\\ne",
  "==": "=",
  "~": "\\sim",
  "≈": "\\approx",
  "->": "\\to",
  "→": "\\to",
  "←": "\\leftarrow",
  "↦": "\\mapsto",
  "||": "\\Vert",
  "‖": "\\Vert",
  "⊕": "\\oplus",
  xor: "\\oplus",
  XOR: "\\oplus",
  "*": "\\cdot",
  "·": "\\cdot",
  "×": "\\times",
  "−": "-",
  "∈": "\\in",
  "∉": "\\notin",
  "⊆": "\\subseteq",
  "∪": "\\cup",
  "∖": "\\setminus",
  "∧": "\\land",
  "∨": "\\lor",
  "¬": "\\neg",
  "≪": "\\ll",
  "∞": "\\infty",
  Σ: "\\sum",
  "...": "\\ldots",
  "…": "\\ldots",
  "..": "\\ldots",
  α: "\\alpha",
  alpha: "\\alpha",
  τ: "\\tau",
  tau: "\\tau",
  ε: "\\varepsilon",
  δ: "\\delta",
  λ: "\\lambda",
  η: "\\eta",
  ω: "\\omega",
  σ: "\\sigma",
  π: "\\pi",
  ρ: "\\rho",
  Γ: "\\Gamma",
  Δ: "\\Delta",
  Θ: "\\Theta",
  Ω: "\\Omega",
  Π: "\\Pi",
};
const FUNCTIONS = new Set(["Pr", "Exp", "Ex", "min", "max", "log2", "floor", "sqrt", "exp", "gcd"]);
const SPECIAL_NAMES = [
  "cn_slow_hash",
  "DS_SALT",
  "DS_MASK",
  "SUITE_ID",
  "PBKDF2-HMAC-SHA512",
  "HMAC-SHA-512",
  "HMAC-SHA-256",
  "BLAKE2b-256",
  "SHA-256",
];
const OPEN = { "(": ")", "[": "]", "{": "}", "⌊": "⌋", "⌈": "⌉" };
const DELIMITERS = {
  "{": "\\{",
  "}": "\\}",
  "⌊": "\\lfloor",
  "⌋": "\\rfloor",
  "⌈": "\\lceil",
  "⌉": "\\rceil",
};
const MAX_SOURCE_LENGTH = 12000;
const MAX_DEPTH = 64;

/** Transcribe a bounded ASCII/Unicode notation without algebraic simplification or precedence guesses.
 * Scripts consume one atom or an explicitly grouped expression; division remains a slash.
 * Every non-whitespace source character belongs to a token, and every token to the syntax tree.
 */
export class AsciiMath {
  #tokens;
  #position = 0;

  constructor(source) {
    if (!source.trim() || source.length > MAX_SOURCE_LENGTH)
      throw new Error("Empty or oversized ASCII math");
    this.#tokens = this.#lex(source);
  }

  #lex(source) {
    const tokens = [];
    let offset = 0;
    const symbols = Object.keys(SYMBOLS)
      .filter((s) => !/^\w+$/.test(s))
      .sort((a, b) => b.length - a.length);
    while (offset < source.length) {
      const rest = source.slice(offset);
      const space = rest.match(/^\s+/);
      if (space) {
        offset += space[0].length;
        continue;
      }
      let value = SPECIAL_NAMES.find((s) => rest.startsWith(s));
      value ??= rest.match(/^[ΓΔΘ]\d+/)?.[0];
      value ??= symbols.find((s) => rest.startsWith(s));
      value ??= rest.match(/^(?:0x[0-9a-fA-F]+|\d+(?:\.\d+)?|[ΓΔΘ]\d+|[a-zA-Z]+\d*|[\p{L}])/u)?.[0];
      value ??= rest.match(/^"[^"\n]*"/)?.[0];
      value ??= rest.match(/^[()[\]{}⌊⌋⌈⌉_^'+\-*/=<>|,:;.]/)?.[0];
      if (!value)
        throw new Error(`Unsupported ASCII math at column ${offset + 1}: ${rest.slice(0, 40)}`);
      tokens.push({ value, offset });
      offset += value.length;
    }
    return tokens;
  }

  #sequence(stop, depth) {
    if (depth > MAX_DEPTH) throw new Error("ASCII math nesting is too deep");
    const nodes = [];
    while (this.#position < this.#tokens.length) {
      const next = this.#tokens[this.#position].value;
      if (next === stop) {
        this.#position++;
        return nodes;
      }
      if (Object.values(OPEN).includes(next))
        throw new Error(`Unexpected closing delimiter ${next}`);
      if (next === "_" || next === "^") throw new Error(`Script without a base: ${next}`);
      nodes.push(this.#atom(depth));
    }
    if (stop) throw new Error(`Unclosed ASCII math group, expected ${stop}`);
    return nodes;
  }

  #atom(depth, script = false) {
    if (depth > MAX_DEPTH) throw new Error("ASCII math nesting is too deep");
    const token = this.#tokens[this.#position++];
    if (!token) throw new Error("Missing script argument");
    if (Object.values(OPEN).includes(token.value))
      throw new Error(`Unexpected closing delimiter ${token.value}`);
    let node = OPEN[token.value]
      ? { kind: "group", open: token.value, children: this.#sequence(OPEN[token.value], depth + 1) }
      : { kind: "token", value: token.value };
    if (script) {
      if (node.kind === "group" && !node.children.length) throw new Error("Empty script argument");
      if (/^[+−-]$/.test(token.value))
        node = { kind: "sequence", children: [node, this.#atom(depth + 1, true)] };
      if (/^[_^=,;*/<>|:.]$/.test(token.value)) throw new Error("Invalid script argument");
      return node;
    }
    const scripts = {};
    let parenthesizedNumericPower = false;
    while (this.#position < this.#tokens.length) {
      const next = this.#tokens[this.#position].value;
      if (next === "_" || next === "^") {
        if (scripts[next])
          throw new Error(`Repeated ${next} script; group the expression explicitly`);
        this.#position++;
        const argument = this.#atom(depth + 1, true);
        parenthesizedNumericPower ||=
          next === "^" &&
          argument.kind === "group" &&
          argument.open === "(" &&
          argument.children.length === 1 &&
          /^\d+$/.test(argument.children[0].value ?? "");
        // Parentheses/braces here group an index or exponent; square brackets remain literal.
        scripts[next] =
          argument.kind === "group" && ["(", "{"].includes(argument.open)
            ? { kind: "sequence", children: argument.children }
            : argument;
      } else if (next === "'" || (next === "*" && this.#isSuffixStar(node))) {
        this.#position++;
        scripts.primes = (scripts.primes ?? "") + next;
      } else break;
    }
    // Check both scripts after parsing, so their order cannot change this refusal.
    // R_0^(1) needs ^1 for a power or ^{(1)} for a labelled sample.
    if (scripts._ && parenthesizedNumericPower)
      throw new Error(
        "Ambiguous parenthesized superscript: use ^1 for a power or ^{(1)} for a label",
      );
    if (Object.keys(scripts).length) node = { kind: "script", base: node, ...scripts };
    return node;
  }

  #isSuffixStar(base) {
    const before = this.#tokens[this.#position - 1];
    const current = this.#tokens[this.#position];
    const after = this.#tokens[this.#position + 1];
    // Only an identifier can carry a postfix star; groups and numbers multiply.
    // The star touches its identifier and is followed by a delimiter/operator or end.
    // An adjacent identifier/number after '*' instead means multiplication, as in 5*d_2.
    return (
      before &&
      base.kind === "token" &&
      /^\p{L}/u.test(base.value) &&
      current.offset === before.offset + before.value.length &&
      (!after ||
        /^[)\]},:;=<>!+−-]$/.test(after.value) ||
        [
          "(",
          "[",
          "∈",
          "≠",
          "‖",
          "||",
          "∨",
          "∧",
          "←",
          "→",
          "↦",
          "<=",
          ">=",
          "≤",
          "≥",
          "!=",
          "==",
          "/",
          "·",
          "×",
        ].includes(after.value))
    );
  }

  #emit(node) {
    if (node.kind === "sequence") return node.children.map((n) => this.#emit(n)).join(" ");
    if (node.kind === "group")
      return `${DELIMITERS[node.open] ?? node.open} ${node.children.map((n) => this.#emit(n)).join(" ")} ${DELIMITERS[OPEN[node.open]] ?? OPEN[node.open]}`;
    if (node.kind === "script") {
      const sub = node._ ? `_{${this.#emit(node._)}}` : "";
      const superparts = [
        node["^"] ? this.#emit(node["^"]) : "",
        ...[...(node.primes ?? "")].map((p) => (p === "\'" ? "\\prime" : "*")),
      ].filter(Boolean);
      return `{${this.#emit(node.base)}}${sub}${superparts.length ? `^{${superparts.join(" ")}}` : ""}`;
    }
    const s = node.value;
    if (SYMBOLS[s]) return SYMBOLS[s];
    if (s.startsWith('"') && /[\\{}]/.test(s))
      throw new Error("Quoted ASCII math text cannot contain LaTeX commands or braces");
    if (s.startsWith('"'))
      return `\\texttt{${s.replace(/[%&#_$~^]/g, (c) =>
        c === "~" ? "\\textasciitilde{}" : c === "^" ? "\\textasciicircum{}" : `\\${c}`,
      )}}`;
    if (s === "in") return "\\in";
    if (s === "mod") return "\\bmod";
    if (s === "|") return "\\vert";
    if (s === "/") return "\\mathbin{/}";
    if (s === "log2") return "\\log_{2}";
    if (FUNCTIONS.has(s)) return `\\operatorname{${s}}`;
    if (/^[ΓΔΘ]\d+$/.test(s)) return `${SYMBOLS[s[0]]}_{${s.slice(1)}}`;
    if (/^[NC]\d+$/.test(s)) return `${s[0]}_{${s.slice(1)}}`;
    if (SPECIAL_NAMES.includes(s) && s.includes("-")) return `\\text{${s}}`;
    if (/^[a-zA-Z][a-zA-Z\d_-]+$/.test(s)) return `\\mathrm{${s.replaceAll("_", "\\_")}}`;
    if (/^0x/.test(s)) return `\\mathtt{${s}}`;
    return s;
  }

  convert() {
    const tree = { kind: "sequence", children: this.#sequence(null, 0) };
    if (this.#position !== this.#tokens.length) throw new Error("Unconsumed ASCII math tokens");
    return { latex: this.#emit(tree), tokens: this.#tokens.map(({ value }) => value), tree };
  }
}
