import { AsciiMath } from "./ascii-math.mjs";

const LITERALS = new Set([
  "mhfe",
  "cn_slow_hash(passphrase)",
  "act",
  "?",
  "||",
  "General_Category=Unassigned",
  "Cn",
  "General_Category=Cc",
  "SUITE_ID",
  "DS_SALT",
  "DS_MASK",
  "0x13",
  "00 00 01 00",
  "1/8",
  "8/8",
  "<dice><TAB><word>",
  "11111",
  "66666",
  "drop-down",
  "felt-tip",
  "t-shirt",
  "yo-yo",
  "yoyo",
  "LICENSE",
  "encrypt_key",
  "decrypt_key",
  "polyseed_crypt",
  "stated-24-words",
  "selected-24-words",
  "mnemonic-encryption",
  "Seedshift",
  "bip39_obfuscator",
  "BIP39Colors",
  "MnemonicCrypt",
  "Mnemonikey",
  "pktseed",
  "seed-otp",
  "NOT_ENOUGH_MEMORY",
  "MEMORY_ALLOCATION_FAILED",
  "12:<secret>",
  "15:<secret>",
  "18:<secret>",
  "21:<secret>",
  "24:<secret>",
  "1:",
  "5:",
]);

/** Decide notation only at Markdown code boundaries; never scan prose, URLs or actual program fences. */
export class Notation {
  inline(source) {
    if (source.startsWith("literal:")) return { literal: source.slice(8) };
    if (source.startsWith("ascii:")) return this.convert(source.slice(6).trim());
    if (
      LITERALS.has(source) ||
      /^(?:MHFE-|CC-BY-|v\d+\.\d+|[a-f\d]{32,}$)/.test(source) ||
      /(?:\.md|\.txt|\.sh)$|^(?:vectors\/|docs\/|scripts\/|hobby-eng\/)/.test(source)
    )
      return null;
    const namedIndex = source.match(/^([a-zA-Z]{2,})_/);
    if (
      namedIndex &&
      !new Set(["Pr", "Exp", "Perm", "Inv", "Trunc", "Packed", "Early", "Bad", "Coll"]).has(
        namedIndex[1],
      )
    )
      throw new Error("Ambiguous identifier: use ascii: for mathematics or literal: for code");
    // A formula is explicit ($...$ / ascii:) or a mathematical code span in the existing sources.
    // Unrecognised prose identifiers remain code; operators, indices and powers must parse or fail.
    if (
      /^[\p{L}]$/u.test(source) ||
      /[_^=<>+*∈≠≤≥‖⊕∧∨¬Σ⌊⌈]/u.test(source) ||
      /^(?:\d|-[\d]|[NC]\d|[ΓΔΘ]\d|Pw$|Qw$|ENT$|PIM$|MEM$|Perm$|seed$|Ex$|Cross$|CS$|tau|RoundMask$|xor$|XOR$|[A-Za-z]+\()/.test(
        source,
      ) ||
      /[()[\]{}…]|(?:[A-Z], ){1,}[A-Z]|[\p{L}0-9]\/|[\p{L}]'|\s[-−/|·]\s/u.test(source)
    )
      return this.convert(source);
    return null;
  }

  convert(source) {
    const result = new AsciiMath(source).convert();
    return { ...result, original: source };
  }

  isMathBlock(source) {
    // Literal protocol constants and document metadata are not mathematical equations.
    if (/^\s*(?:SUITE_ID\s*=|BIP:)/.test(source)) return false;
    return /[_^]|(?:<=|>=|=|≤|≥|⊕|∈)/.test(source);
  }

  block(source) {
    const lines = source
      .trim()
      .split(/\n/)
      .filter((line) => line.trim());
    const converted = lines.map((line) => {
      const label = line.match(/^([a-z]+(?:[ ,]+[a-z]+)+):\s*(.+)$/);
      if (!label) return this.convert(line.trim());
      const body = this.convert(label[2]);
      return {
        ...body,
        latex: `\\text{${label[1]}: } ${body.latex}`,
        tokens: [label[1] + ":", ...body.tokens],
      };
    });
    return {
      original: source,
      latex: `\\begin{gathered}\n${converted.map((line) => line.latex).join(" \\\\\n")}\n\\end{gathered}`,
      tokens: converted.map((line) => line.tokens),
    };
  }
}
