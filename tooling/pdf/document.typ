// Body faces are pinned separately; mathematical and code fonts are bundled with Typst.
#set page(paper: "a4", margin: (top: 18mm, bottom: 20mm, left: 20mm, right: 20mm),
  footer: context {
    metadata((kind: "footer-start", pos: here().position()))
    align(center, text(size: 8pt, counter(page).display("1 / 1", both: true)))
    metadata((kind: "footer-end", pos: here().position()))
  })
#set text(font: "Times New Roman", size: 12pt, lang: "en")
#set par(leading: 10pt, spacing: 18pt, justify: true)
#show heading: set par(justify: false)
#show heading: set block(above: 0pt, below: 0pt)
#show raw.where(block: true): set par(justify: false)
#show math.equation: set text(font: "New Computer Modern Math")
#set heading(numbering: none)
#show heading.where(level: 1): set text(size: 20pt)
#show heading.where(level: 2): set text(size: 16pt)
#show heading.where(level: 3): set text(size: 14pt)
#show heading.where(level: 4): set text(size: 12pt)
#set math.equation(numbering: none)
#show math.equation.where(block: true): set block(above: 0.8em, below: 0.8em)
#set table(inset: 5pt, stroke: 0.35pt + luma(120))
#set table.cell(breakable: false)
#show figure.where(kind: table): set block(breakable: false)
#show raw: set text(font: "DejaVu Sans Mono", size: 10pt)
// The game identifier is a lower-right script, consistently in inline and display math.
#let Pr = math.op("Pr", limits: false)

// Every marker has its own context: sharing the body's context would give its end
// marker the start position and conceal page splits.
#let mhfe-mark(value) = context metadata(value + (pos: here().position(),))
#let mhfe-width = 170mm
#let mhfe-block(id, body) = [
  #mhfe-mark((kind: "block-start", id: id))#body(mhfe-width)#mhfe-mark((kind: "block-end", id: id))
]
// Only indented text, cells and explicit containers need a dynamic width query.
#let mhfe-narrow-block(id, body) = layout(available => [
  #mhfe-mark((kind: "block-start", id: id))#body(available.width)#mhfe-mark((kind: "block-end", id: id))
])
#let mhfe-heading(id, body) = block(above: 24pt, below: 18pt, sticky: true)[
  #mhfe-mark((kind: "heading-start", id: id))
  #mhfe-narrow-block(id, body)
  #mhfe-mark((kind: "heading-end", id: id))
]
#let mhfe-code(id, body) = block(breakable: false, above: 10pt, below: 12pt)[
  #mhfe-mark((kind: "code-start", id: id))
  #mhfe-narrow-block(id, body)
  #mhfe-mark((kind: "code-end", id: id))
]
// Preserve array columns, their individual alignment and explicit separator rules.
#let mhfe-array(alignments, vrules, hrules, rows) = context {
  let widths = range(alignments.len()).map(column => calc.max(..rows.map(row =>
    measure(math.equation(row.at(column))).width)))
  let padded = rows.map(row => row.enumerate().map(((column, cell)) => {
    let extra = widths.at(column) - measure(math.equation(cell)).width
    let before = if alignments.at(column) == "r" { extra } else if alignments.at(column) == "c" { extra / 2 } else { 0pt }
    let after = extra - before
    [#h(before)#cell#h(after)]
  }))
  math.equation(block: true, math.mat(delim: none, align: left,
    column-gap: 1em, row-gap: 0.5em,
    augment: (vline: vrules, hline: hrules, stroke: 0.4pt), ..padded))
}

// An inline equation may wrap only after a relation or binary operator outside all
// fences, norms and absolute-value bars, as TeX allows. The parts between those points
// are unbreakable boxes, joined by Typst's spacing after the operator: thick after a
// relation and medium after a binary operator. That spacing is weak, so it disappears
// at a line end. An equation with its sentence punctuation narrower than an eighth of
// its line stays one box; moving it to the next line costs little.
// The regression suite sets this flag to require that the parts and their spacing
// reproduce the width of each whole equation. Measuring every part of a full document
// would exceed the memory limit of the rendering container.
#let mhfe-check-parts = false
#let mhfe-relations = ("=", "≠", "≤", "≥", "<", ">", "≈", "∼", "≡", "∈", "∉", "⊆", "⊂", "→", "←", "↦")
#let mhfe-binaries = ("+", "−", "-", "·", "⋅", "×", "⊕", "∧", "∨", "∪", "∩", "∖")
// Pandoc puts explicitly sized fences inside scale(equation(symbol)). Inspect only
// those wrappers; a binary concatenation symbol must not become a fence.
#let mhfe-scaled-fence(atom) = {
  if atom.func() == scale { atom = atom.body }
  if atom.func() == math.equation { atom = atom.body }
  atom.fields().at("text", default: none)
}
// Different fence types may nest. A single toggle would close an outer modulus at
// the opening of an inner norm, allowing a line break inside both.
#let mhfe-bar-stack(bars, text, role: none) = {
  if text == "∥" { text = "‖" }
  if role == "opening" {
    bars.push(text)
  } else if role == "closing" {
    if bars.len() > 0 { let _ = bars.pop() }
  } else if bars.len() > 0 and bars.last() == text {
    let _ = bars.pop()
  } else {
    bars.push(text)
  }
  bars
}
// The complete equation is recorded once; its parts do not add native math records.
#let mhfe-part(body) = [#math.equation(body)<mhfe-part>]
#let mhfe-wrap-inline(id, body, tail, natural, width) = {
  if natural < width / 8 {
    return box(body + tail)
  }
  // Plain loops only: Typst memoizes every call of a user-defined function.
  let parts = body.body.fields().at("children", default: (body.body,))
  let texts = ()
  let operators = ()
  for (index, part) in parts.enumerate() {
    if part == [ ] { continue }
    let attached = part.func() == math.attach
    let atom = if attached { part.base } else { part }
    // Deliberate copy with the wide-equation pass: inline field reads avoid a
    // memoized helper call per atom; the norm regressions exercise both paths.
    let role = atom.fields().at("class", default: none)
    if ("opening", "closing").contains(role) { atom = atom.body }
    texts.push(if atom.func() == scale { mhfe-scaled-fence(atom) } else { atom.fields().at("text", default: none) })
    operators.push((index, if attached { none } else { part.fields().at("text", default: none) }, role))
  }
  let opening = ("(", "[", "{", "⌊", "⌈", "⟨")
  let closing = (")", "]", "}", "⌋", "⌉", "⟩")
  let depth = 0
  let bars = ()
  let cuts = (:)
  for (position, (index, own, role)) in operators.enumerate() {
    let text = texts.at(position)
    if opening.contains(text) { depth += 1 }
    if closing.contains(text) { depth -= 1 }
    if ("‖", "∥", "|").contains(text) { bars = mhfe-bar-stack(bars, text, role: role) }
    let relation = mhfe-relations.contains(own)
    if depth != 0 or bars.len() > 0 or not (relation or mhfe-binaries.contains(own)) or position == 0 or position == texts.len() - 1 {
      continue
    }
    // A break needs an operand before the operator and no relation, closing fence
    // or punctuation after it.
    let before = texts.at(position - 1)
    let after = texts.at(position + 1)
    if mhfe-relations.contains(before) or mhfe-binaries.contains(before) or opening.contains(before) or (",", ";", ":").contains(before) {
      continue
    }
    if mhfe-relations.contains(after) or closing.contains(after) or (",", ";", ".", ":").contains(after) or (not relation and mhfe-binaries.contains(after)) {
      continue
    }
    cuts.insert(str(index), if relation { 5em / 18 } else { 4em / 18 })
  }
  if cuts.len() == 0 {
    return box(body + tail)
  }
  let pieces = ()
  let current = []
  for (index, part) in parts.enumerate() {
    current += part
    if str(index) in cuts {
      pieces.push((current, cuts.at(str(index)).to-absolute()))
      current = []
    }
  }
  pieces.push((current, 0pt))
  if mhfe-check-parts {
    let total = 0pt
    for (piece, gap) in pieces {
      total += measure(math.equation(piece)).width + gap
    }
    assert(calc.abs((total - measure(body).width).pt()) < 0.01,
      message: "Inline equation parts change its spacing: " + id)
  }
  mhfe-mark((kind: "math-parts", id: id, parts: pieces.len()))
  mhfe-mark((kind: "native-math", body: body.body, block: false))
  for (index, (piece, gap)) in pieces.enumerate() {
    if index == pieces.len() - 1 {
      box(mhfe-part(piece) + tail)
    } else {
      box(mhfe-part(piece))
      h(gap, weak: true)
    }
  }
}

// Break wide inline equations at a relation outside all fences. Function calls
// without an outer relation may break at their outer argument separators only.
#let mhfe-fit-inline(body, tail: [], id: "unknown", width: 170mm) = context {
  let natural = if body.func() == math.equation { measure(body + tail).width } else { 0pt }
  if natural > width {
    let parts = body.body.fields().at("children", default: (body.body,))
    let depth = 0
    let bars = ()
    let breaks = ()
    let commas = ()
    for (index, part) in parts.enumerate() {
      let atom = if part.func() == math.attach { part.base } else { part }
      let role = atom.fields().at("class", default: none)
      if ("opening", "closing").contains(role) { atom = atom.body }
      let text = if atom.func() == scale { mhfe-scaled-fence(atom) } else { atom.fields().at("text", default: none) }
      if ("(", "[", "{", "⌊", "⌈", "⟨").contains(text) { depth += 1 }
      if (")", "]", "}", "⌋", "⌉", "⟩").contains(text) { depth -= 1 }
      if ("‖", "∥", "|").contains(text) { bars = mhfe-bar-stack(bars, text, role: role) }
      if depth == 0 and bars.len() == 0 and ("=", "≤", "≥", "·", "⋅", "+").contains(text) { breaks.push(index) }
      // The fallback applies to outer function arguments, never probability brackets.
      if depth == 1 and bars.len() == 0 and text == "," and parts.any(it => it.fields().at("text", default: none) == "(") and not parts.any(it => it.fields().at("text", default: none) == "[") {
        commas.push(index + 1)
      }
    }
    let candidates = if breaks.len() > 0 { breaks } else { commas }
    assert(candidates.len() > 0, message: "Wide equation has no safe outer break: " + id)
    let chunks = ()
    let chunk = []
    for (index, part) in parts.enumerate() {
      if candidates.contains(index) {
        chunks.push(chunk)
        chunk = []
      }
      chunk += part
    }
    chunks.push(chunk + tail)
    let lines = ()
    let line = []
    for (index, chunk) in chunks.enumerate() {
      assert(measure(math.equation(chunk)).width <= width, message: "An indivisible equation segment exceeds its container: " + id)
      if index == 1 or measure(math.equation(line + chunk)).width > width {
        lines.push(line)
        line = []
      }
      line += chunk
    }
    lines.push(line)
    // Set the rows like TeX's multline: the first flush left, the last flush right
    // and any others centred, 10 pt from the container edges when they fit.
    let widths = lines.map(line => measure(math.equation(block: true, line)).width)
    for row in widths {
      assert(row <= width, message: "Equation row exceeds its container: " + id)
    }
    let span = calc.max(..widths, width - 20pt)
    let result = []
    for (index, line) in lines.enumerate() {
      let extra = span - widths.at(index)
      if index > 0 { result += linebreak() }
      if index == 0 {
        result += line + h(extra)
      } else if index == lines.len() - 1 {
        result += h(extra) + line
      } else {
        result += h(extra / 2) + line + h(extra / 2)
      }
    }
    mhfe-mark((kind: "math-promoted", tail: tail, width: width, row-widths: widths))
    math.equation(block: true, result)
  } else if body.func() == math.equation {
    mhfe-wrap-inline(id, body, tail, natural, width)
  } else {
    box(body + tail)
  }
}

#let mhfe-math(id, display: false, tag: none, tail: [], width: 170mm, body) = {
  let rendered = if tag == none { body } else {
    set math.equation(numbering: n => tag)
    body
  }
  mhfe-mark((kind: "math-start", id: id, display: display, tag: tag, tail: tail))
  if display { rendered; tail } else { mhfe-fit-inline(rendered, tail: tail, id: id, width: width) }
}
#let mhfe-math-end(id) = mhfe-mark((kind: "math-end", id: id))

// Native text and math trees are the reference for the independent PDF text check.
// The checker ignores text hooks between each math start/end pair, because those
// characters are already represented in the complete mathematical content tree.
#show text: it => [#mhfe-mark((kind: "native-text", text: it.text))#it]
#show math.equation: it => {
  if it.at("label", default: none) != <mhfe-part> {
    mhfe-mark((kind: "native-math", body: it.body, block: it.block))
  }
  it
}

#let mhfe-table(id, body) = {
  set text(size: 11pt)
  set par(leading: 5pt, spacing: 8pt, justify: false)
  show table.cell: it => layout(available => context {
    let measured = measure(it, width: available.width)
    mhfe-mark((kind: "cell", id: id, column: it.x, row: it.y,
      width: available.width, height: measured.height))
    it
    mhfe-mark((kind: "cell-end", id: id, column: it.x, row: it.y))
  })
  block(breakable: false, above: 10pt, below: 12pt)[
    #mhfe-mark((kind: "table-start", id: id))
    #mhfe-narrow-block(id, body)
    #mhfe-mark((kind: "table-end", id: id))
  ]
}

#let mhfe-contents(body) = context {
  let compact = [
    #set par(leading: 4pt, spacing: 5pt, justify: false)
    #set list(spacing: 5pt)
    #body
  ]
  let size = measure(compact, width: 170mm)
  let oversized = size.height > 259mm
  let content = [#mhfe-mark((kind: "contents-start", oversized: oversized, height: size.height))#compact#mhfe-mark((kind: "contents-end"))]
  if oversized {
    pagebreak(weak: true)
    content
  } else {
    // Typst moves this complete block if it does not fit the remaining space.
    block(breakable: false, content)
  }
  pagebreak(weak: true)
  mhfe-mark((kind: "contents-body-start"))
}
