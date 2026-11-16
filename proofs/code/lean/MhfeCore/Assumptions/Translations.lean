-- Line-by-line translations of the five functions of mhfe_core that Aeneas build-2b9e3ea cannot
-- translate, with the helpers they use. This file is not a module of its own: tools/splice.py
-- places each of its blocks into MhfeCore/Code.lean, after the extracted definitions it uses and
-- before those that use it (README.md, "The trusted base").

/-- `<[T]>::split_first_chunk_mut::<N>` followed by `.expect(..)`: the first `N` elements as an
array and the rest, or a panic when fewer than `N` are left. The backward function puts both
parts back in place. -/
def MhfeTranslation.splitFirstChunkMutExpect {T : Type} (N : Std.Usize) (s : Slice T) :
    RustM (((Array T N) × (Slice T)) × (((Array T N) × (Slice T)) → Slice T)) :=
  if h : N.val ≤ s.val.length then
    have hs := s.property
    have hf : (s.val.take N.val).length = N.val := by simp; omega
    have hr : (s.val.drop N.val).length ≤ Usize.max := by simp; omega
    let back := fun (p : (Array T N) × (Slice T)) =>
      if hp : p.2.val.length = (s.val.drop N.val).length then
        Slice.from (p.1.val ++ p.2.val) (by
          have h1 := p.1.property
          simp only [List.length_append, List.length_drop] at *
          omega)
      else s
    ok ((Array.from (s.val.take N.val) hf, Slice.from (s.val.drop N.val) hr), back)
  else fail panic

/-- `<[u8]>::swap_with_slice`: panics unless both have the same length, then swaps them. -/
def MhfeTranslation.swapWithSlice (a b : Slice Std.U8) : RustM ((Slice Std.U8) × (Slice Std.U8)) :=
  if a.length = b.length then ok (b, a) else fail panic

/-- `for (byte, mask_byte) in target.iter_mut().zip(mask.iter()) { *byte ^= mask_byte; }`:
the zip stops at the shorter one, so bytes of `target` past the end of `mask` keep their value. -/
def MhfeTranslation.xorZip (target mask : Slice Std.U8) : Slice Std.U8 :=
  Slice.from (List.zipWith (· ^^^ ·) target.val mask.val ++ target.val.drop mask.val.length) (by
    have := target.property
    simp only [List.length_append, List.length_zipWith, List.length_drop]
    omega)

/-- [mhfe_core::feistel::{mhfe_core::feistel::Workspace}::parts]: Source: 'src/feistel.rs',
lines 205:4-220:5.

```rust
fn parts(&mut self) -> Parts<'_> {
    let half = self.geometry.half_bytes;
    let (left, rest) = self.secret.as_mut_bytes().split_at_mut(half);
    let (right, rest) = rest.split_at_mut(half);
    let (message, rest) = rest.split_at_mut(self.geometry.message_bytes());
    let (salt, rest) = rest.split_first_chunk_mut().expect("room for the salt");
    let (key, mask) = rest.split_first_chunk_mut().expect("room for the key");
    Parts { left, right, message, salt, key, mask }
}
``` -/
def feistel.Workspace.parts (self : feistel.Workspace) :
    RustM (feistel.Parts × (feistel.Parts → feistel.Workspace)) := do
  let half := self.geometry.half_bytes
  let (s, as_mut_bytes_back) ← protect.Secret.as_mut_bytes self.secret
  let ((left, rest), back1) ← core.slice.Slice.split_at_mut s half
  let ((right, rest1), back2) ← core.slice.Slice.split_at_mut rest half
  let i ← feistel.Geometry.message_bytes self.geometry
  let ((message, rest2), back3) ← core.slice.Slice.split_at_mut rest1 i
  let ((salt, rest3), back4) ← MhfeTranslation.splitFirstChunkMutExpect 16#usize rest2
  let ((key, mask), back5) ← MhfeTranslation.splitFirstChunkMutExpect 32#usize rest3
  let back := fun (p : feistel.Parts) =>
    let rest3' := back5 (p.key, p.mask)
    let rest2' := back4 (p.salt, rest3')
    let rest1' := back3 (p.message, rest2')
    let rest' := back2 (p.right, rest1')
    let s' := back1 (p.left, rest')
    { self with secret := as_mut_bytes_back s' }
  ok ({ left, right, message, salt, key, mask }, back)

/-- [mhfe_core::feistel::{mhfe_core::feistel::Permutation<'_0, E>}::round]: Source:
'src/feistel.rs', lines 131:4-162:5. `stack::cleared(body)` runs `body` and then clears the stack,
which changes no value, so the body is translated directly.

```rust
fn round(&mut self, space: &mut Workspace, round: u32, masked: Side) -> Result<(), Error> {
    stack::cleared(|| {
        let geometry = space.geometry;
        let Parts { left, right, message, salt, key, mask } = space.parts();
        let (target, source) = match masked {
            Side::Left => (left, right),
            Side::Right => (right, left),
        };
        write_message(message, geometry, self.work, round, source);
        round_salt(geometry, message, salt);
        self.engine.argon2id(
            self.password.as_bytes(),
            salt,
            self.work.memory_kib(),
            self.work.passes(),
            key,
        )?;
        round_mask(geometry, key, message, mask);
        for (byte, mask_byte) in target.iter_mut().zip(mask.iter()) {
            *byte ^= mask_byte;
        }
        target.swap_with_slice(source);
        Ok(())
    })
}
```

The result has the shape of the extracted functions: the result of the round, `self` after it
(with its engine), the backward function of `self`, and `space` after it. -/
def feistel.Permutation.round {E : Type _} (engineArgon2EngineInst : engine.Argon2Engine E)
    (self : feistel.Permutation E) (space : feistel.Workspace) (round : Std.U32)
    (masked : feistel.Side) :
    RustM ((core.result.Result Unit error.Error) × (feistel.Permutation E) ×
      (feistel.Permutation E → feistel.Permutation E) × feistel.Workspace) := do
  let geometry := space.geometry
  let (p, parts_back) ← feistel.Workspace.parts space
  let sides : Slice Std.U8 × Slice Std.U8 :=
    match masked with
    | feistel.Side.Left => (p.left, p.right)
    | feistel.Side.Right => (p.right, p.left)
  let (target, source) := sides
  let message ← feistel.write_message p.message geometry self.work round source
  let salt ← feistel.round_salt geometry message p.salt
  let pw ← password.Password.as_bytes self.password
  let mem ← suite.WorkFactor.memory_kib self.work
  let passes ← suite.WorkFactor.passes self.work
  let (r, engine1, key) ←
    engineArgon2EngineInst.argon2id self.engine pw salt mem passes p.key
  let self1 := { self with engine := engine1 }
  let back := fun (self2 : feistel.Permutation E) => { self with engine := self2.engine }
  match r with
  | core.result.Result.Err e =>
    let space1 := parts_back { p with message, salt, key }
    ok (core.result.Result.Err e, self1, back, space1)
  | core.result.Result.Ok () =>
    let mask ← feistel.round_mask geometry key message p.mask
    let target1 := MhfeTranslation.xorZip target mask
    let (target2, source1) ← MhfeTranslation.swapWithSlice target1 source
    let halves : Slice Std.U8 × Slice Std.U8 :=
      match masked with
      | feistel.Side.Left => (target2, source1)
      | feistel.Side.Right => (source1, target2)
    let (left, right) := halves
    let space1 := parts_back { left, right, message, salt, key, mask }
    ok (core.result.Result.Ok (), self1, back, space1)

/-- The loop of `forward` from round `round` on, with `fuel` rounds left:

```rust
for round in 0..ROUNDS {
    if on_round(round + 1).is_break() {
        return Ok(ControlFlow::Break(()));
    }
    self.round(&mut space, round, Side::Left)?;
}
``` -/
def MhfeTranslation.forwardLoop {E : Type _} {T2 : Type _} (engineArgon2EngineInst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (self : feistel.Permutation E) (space : feistel.Workspace) (on_round : T2) (round : Std.U32) :
    (fuel : Nat) → RustM ((core.result.Result (core.ops.control_flow.ControlFlow Unit
      feistel.Workspace) error.Error) × (feistel.Permutation E) × T2)
  | 0 => ok (core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue space), self,
      on_round)
  | fuel + 1 => do
    let i ← round + 1#u32
    let (cf, on_round1) ← fnInst.call_mut on_round i
    let b ← core.ops.control_flow.ControlFlow.is_break cf
    if b then
      ok (core.result.Result.Ok (core.ops.control_flow.ControlFlow.Break ()), self, on_round1)
    else
      let (r, self1, _, space1) ←
        feistel.Permutation.round engineArgon2EngineInst self space round feistel.Side.Left
      match r with
      | core.result.Result.Err e => ok (core.result.Result.Err e, self1, on_round1)
      | core.result.Result.Ok () =>
        let next ← round + 1#u32
        MhfeTranslation.forwardLoop engineArgon2EngineInst fnInst self1 space1 on_round1 next fuel

/-- The loop of `inverse` with `fuel` rounds left; `step` counts from 1 and `round` down from 11:

```rust
for (step, round) in (1..).zip((0..ROUNDS).rev()) {
    if on_round(step).is_break() {
        return Ok(ControlFlow::Break(()));
    }
    self.round(&mut space, round, Side::Right)?;
}
``` -/
def MhfeTranslation.inverseLoop {E : Type _} {T2 : Type _} (engineArgon2EngineInst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (self : feistel.Permutation E) (space : feistel.Workspace) (on_round : T2) (step : Std.U32) :
    (fuel : Nat) → RustM ((core.result.Result (core.ops.control_flow.ControlFlow Unit
      feistel.Workspace) error.Error) × (feistel.Permutation E) × T2)
  | 0 => ok (core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue space), self,
      on_round)
  | fuel + 1 => do
    let (cf, on_round1) ← fnInst.call_mut on_round step
    let b ← core.ops.control_flow.ControlFlow.is_break cf
    if b then
      ok (core.result.Result.Ok (core.ops.control_flow.ControlFlow.Break ()), self, on_round1)
    else
      let round ← lift (UScalar.cast .U32 (⟨BitVec.ofNat _ fuel⟩ : Std.Usize))
      let (r, self1, _, space1) ←
        feistel.Permutation.round engineArgon2EngineInst self space round feistel.Side.Right
      match r with
      | core.result.Result.Err e => ok (core.result.Result.Err e, self1, on_round1)
      | core.result.Result.Ok () =>
        let next ← step + 1#u32
        MhfeTranslation.inverseLoop engineArgon2EngineInst fnInst self1 space1 on_round1 next fuel

/-- [mhfe_core::feistel::{mhfe_core::feistel::Permutation<'_0, E>}::forward]: Source:
'src/feistel.rs', lines 95:4-109:5.

```rust
pub(crate) fn forward(
    &mut self,
    x: &[u8],
    on_round: &mut impl FnMut(u32) -> ControlFlow<()>,
) -> Rounds {
    let mut space = Workspace::new(self.geometry, x);
    for round in 0..ROUNDS {
        if on_round(round + 1).is_break() {
            return Ok(ControlFlow::Break(()));
        }
        // L_{i+1} = R_i and R_{i+1} = L_i XOR M_i: the left half takes the mask.
        self.round(&mut space, round, Side::Left)?;
    }
    Ok(ControlFlow::Continue(space.into_state()))
}
```

The callers that Aeneas generates expect, after the callback's final state, the function that
gives back what the callback borrows (a closure that holds `&mut on_round`); it is the identity:
the borrowed value is the closure's state when `forward` returns. -/
def feistel.Permutation.forward {E : Type _} {T2 : Type _}
    (engineArgon2EngineInst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (self : feistel.Permutation E) (x : Slice Std.U8) (on_round : T2) :
    RustM ((core.result.Result (core.ops.control_flow.ControlFlow Unit protect.Secret)
      error.Error) × (feistel.Permutation E) × (feistel.Permutation E → feistel.Permutation E) ×
      T2 × (T2 → T2)) := do
  let space ← feistel.Workspace.new self.geometry x
  let back := fun (self2 : feistel.Permutation E) => { self with engine := self2.engine }
  let (r, self1, on_round1) ←
    MhfeTranslation.forwardLoop engineArgon2EngineInst fnInst self space on_round 0#u32 suite.ROUNDS.val
  match r with
  | core.result.Result.Err e => ok (core.result.Result.Err e, self1, back, on_round1, fun c => c)
  | core.result.Result.Ok (core.ops.control_flow.ControlFlow.Break ()) =>
    ok (core.result.Result.Ok (core.ops.control_flow.ControlFlow.Break ()), self1, back,
      on_round1, fun c => c)
  | core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue space1) =>
    let st ← feistel.Workspace.into_state space1
    ok (core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st), self1, back,
      on_round1, fun c => c)

/-- [mhfe_core::feistel::{mhfe_core::feistel::Permutation<'_0, E>}::inverse]: Source:
'src/feistel.rs', lines 112:4-127:5.

```rust
pub(crate) fn inverse(
    &mut self,
    y: &[u8],
    on_round: &mut impl FnMut(u32) -> ControlFlow<()>,
) -> Rounds {
    let mut space = Workspace::new(self.geometry, y);
    for (step, round) in (1..).zip((0..ROUNDS).rev()) {
        if on_round(step).is_break() {
            return Ok(ControlFlow::Break(()));
        }
        // R_i = L_{i+1}, so the mask comes from the left half; then L_i = R_{i+1} XOR M_i: the
        // right half takes the mask.
        self.round(&mut space, round, Side::Right)?;
    }
    Ok(ControlFlow::Continue(space.into_state()))
}
```

The result has the same shape as `forward`'s. -/
def feistel.Permutation.inverse {E : Type _} {T2 : Type _}
    (engineArgon2EngineInst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (self : feistel.Permutation E) (y : Slice Std.U8) (on_round : T2) :
    RustM ((core.result.Result (core.ops.control_flow.ControlFlow Unit protect.Secret)
      error.Error) × (feistel.Permutation E) × (feistel.Permutation E → feistel.Permutation E) ×
      T2 × (T2 → T2)) := do
  let space ← feistel.Workspace.new self.geometry y
  let back := fun (self2 : feistel.Permutation E) => { self with engine := self2.engine }
  let (r, self1, on_round1) ←
    MhfeTranslation.inverseLoop engineArgon2EngineInst fnInst self space on_round 1#u32 suite.ROUNDS.val
  match r with
  | core.result.Result.Err e => ok (core.result.Result.Err e, self1, back, on_round1, fun c => c)
  | core.result.Result.Ok (core.ops.control_flow.ControlFlow.Break ()) =>
    ok (core.result.Result.Ok (core.ops.control_flow.ControlFlow.Break ()), self1, back,
      on_round1, fun c => c)
  | core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue space1) =>
    let st ← feistel.Workspace.into_state space1
    ok (core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st), self1, back,
      on_round1, fun c => c)

/-- [mhfe_core::recovery::lengths]: Source: 'src/recovery.rs', lines 135:0-150:1. The arms are
tried in order, a guard that fails passing to the next arm.

```rust
fn lengths(stated: Option<usize>, detected: &[usize]) -> Result<Vec<usize>, Error> {
    match (stated, detected) {
        (Some(words), _) if detected.contains(&words) => Ok(vec![words]),
        (None | Some(STATE_WORDS), []) => Ok(vec![STATE_WORDS]),
        (Some(_), []) => Err(Error::VerifierMismatch),
        (None, [words]) => Ok(vec![*words]),
        (Some(stated), [words]) if stated != STATE_WORDS => Ok(vec![*words]),
        _ => Ok(detected.iter().copied().chain([STATE_WORDS]).collect()),
    }
}
``` -/
def recovery.lengths (stated : Option Std.Usize) (detected : Slice Std.Usize) :
    RustM (core.result.Result (alloc.vec.Vec Std.Usize) error.Error) := do
  let sw ← packing.STATE_WORDS
  let vec1 := fun (w : Std.Usize) => alloc.vec.Vec.from [w] (by simp; scalar_tac)
  let arm6 : RustM (core.result.Result (alloc.vec.Vec Std.Usize) error.Error) :=
    if h : (detected.val ++ [sw]).length ≤ Usize.max then
      ok (core.result.Result.Ok (alloc.vec.Vec.from (detected.val ++ [sw]) h))
    else fail panic
  match stated, detected.val with
  | some words, d =>
    if words ∈ d then ok (core.result.Result.Ok (vec1 words))
    else match d with
      | [] =>
        if words = sw then ok (core.result.Result.Ok (vec1 sw))
        else ok (core.result.Result.Err error.Error.VerifierMismatch)
      | [w] => if words ≠ sw then ok (core.result.Result.Ok (vec1 w)) else arm6
      | _ => arm6
  | none, [] => ok (core.result.Result.Ok (vec1 sw))
  | none, [w] => ok (core.result.Result.Ok (vec1 w))
  | none, _ => arm6

/-- Replaces the generated instance of the same name (MANIFEST-code.txt, "R"). Aeneas
generates the `call_once` of this closure, which captures a mutable borrow, with the closure's
state in its result, while `FnOnce.call_once` returns the output alone; the closure is consumed,
so the state is dropped.
Trait implementation: [mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>}::encrypt::{closure}::{impl core::ops::function::FnOnce<(u32,), core::ops::control_flow::ControlFlow<(), ()>> for mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>[TraitClause0]}::encrypt::{closure}::{closure#2}<'_0, E, T1, T2>}]
    Source: 'src/cipher.rs', lines 106:60-108:17 -/
@[reducible]
def
  cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple
  {E : Type _} {T1 : Type _} {T2 : Type _} (engineArgon2EngineInst :
  engine.Argon2Engine E)
  (coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst :
  core.ops.function.FnMut T1 (Std.U32 × Std.U32)
  (core.ops.control_flow.ControlFlow Unit Unit))
  (coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst :
  core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow
  Unit Unit)) : core.ops.function.FnOnce (cipher.Mhfe.encrypt.closure.closure_2
  E T1 T2) Std.U32 (core.ops.control_flow.ControlFlow Unit Unit) := {
  call_once := fun c i => do
    let (o, _) ←
      cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple.call_once
        engineArgon2EngineInst
        coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
        coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst c i
    ok o
}


/-- Replaces the generated instance of the same name (MANIFEST-code.txt, "R"). Aeneas
generates the `call_mut` of this closure, which captures a mutable borrow, with a backward function
in its result, while `FnMut.call_mut` returns the output and the closure's new state; the new state
is the backward function applied to the state after the call, as in the generated `call_once`.
Trait implementation: [mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>}::encrypt::{closure}::{impl core::ops::function::FnMut<(u32,), core::ops::control_flow::ControlFlow<(), ()>> for mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>[TraitClause0]}::encrypt::{closure}::{closure#2}<'_0, E, T1, T2>}]
    Source: 'src/cipher.rs', lines 106:60-108:17 -/
@[reducible]
def
  cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
  {E : Type _} {T1 : Type _} {T2 : Type _} (engineArgon2EngineInst :
  engine.Argon2Engine E)
  (coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst :
  core.ops.function.FnMut T1 (Std.U32 × Std.U32)
  (core.ops.control_flow.ControlFlow Unit Unit))
  (coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst :
  core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow
  Unit Unit)) : core.ops.function.FnMut (cipher.Mhfe.encrypt.closure.closure_2
  E T1 T2) Std.U32 (core.ops.control_flow.ControlFlow Unit Unit) := {
  FnOnceInst :=
    cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple
    engineArgon2EngineInst
    coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
    coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst
  call_mut := fun c i => do
    let (o, c1, back) ←
      cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut
        engineArgon2EngineInst
        coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
        coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst c i
    ok (o, back c1)
}


/-- Replaces the generated instance of the same name (MANIFEST-code.txt, "R"). Aeneas
generates the `call_once` of this closure, which captures a mutable borrow, with the closure's
state in its result, while `FnOnce.call_once` returns the output alone; the closure is consumed,
so the state is dropped.
Trait implementation: [mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>}::encrypt::{closure}::{impl core::ops::function::FnOnce<(u32,), core::ops::control_flow::ControlFlow<(), ()>> for mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>[TraitClause0]}::encrypt::{closure}::{closure}<'_0, E, T1, T2>}]
    Source: 'src/cipher.rs', lines 89:44-89:79 -/
@[reducible]
def
  cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple
  {E : Type _} {T1 : Type _} {T2 : Type _} (engineArgon2EngineInst :
  engine.Argon2Engine E)
  (coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst :
  core.ops.function.FnMut T1 (Std.U32 × Std.U32)
  (core.ops.control_flow.ControlFlow Unit Unit))
  (coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst :
  core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow
  Unit Unit)) : core.ops.function.FnOnce (cipher.Mhfe.encrypt.closure.closure E
  T1 T2) Std.U32 (core.ops.control_flow.ControlFlow Unit Unit) := {
  call_once := fun c i => do
    let (o, _) ←
      cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple.call_once
        engineArgon2EngineInst
        coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
        coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst c i
    ok o
}


/-- Replaces the generated instance of the same name (MANIFEST-code.txt, "R"). Aeneas
generates the `call_mut` of this closure, which captures a mutable borrow, with a backward function
in its result, while `FnMut.call_mut` returns the output and the closure's new state; the new state
is the backward function applied to the state after the call, as in the generated `call_once`.
Trait implementation: [mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>}::encrypt::{closure}::{impl core::ops::function::FnMut<(u32,), core::ops::control_flow::ControlFlow<(), ()>> for mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>[TraitClause0]}::encrypt::{closure}::{closure}<'_0, E, T1, T2>}]
    Source: 'src/cipher.rs', lines 89:44-89:79 -/
@[reducible]
def
  cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
  {E : Type _} {T1 : Type _} {T2 : Type _} (engineArgon2EngineInst :
  engine.Argon2Engine E)
  (coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst :
  core.ops.function.FnMut T1 (Std.U32 × Std.U32)
  (core.ops.control_flow.ControlFlow Unit Unit))
  (coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst :
  core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow
  Unit Unit)) : core.ops.function.FnMut (cipher.Mhfe.encrypt.closure.closure E
  T1 T2) Std.U32 (core.ops.control_flow.ControlFlow Unit Unit) := {
  FnOnceInst :=
    cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple
    engineArgon2EngineInst
    coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
    coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst
  call_mut := fun c i => do
    let (o, c1, back) ←
      cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut
        engineArgon2EngineInst
        coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
        coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst c i
    ok (o, back c1)
}


/-- Replaces the generated instance of the same name (MANIFEST-code.txt, "R"). Aeneas
generates the `call_once` of this closure, which captures a mutable borrow, with the closure's
state in its result, while `FnOnce.call_once` returns the output alone; the closure is consumed,
so the state is dropped.
Trait implementation: [mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>}::decrypt::{closure}::{impl core::ops::function::FnOnce<(u32,), core::ops::control_flow::ControlFlow<(), ()>> for mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>[TraitClause0]}::decrypt::{closure}::{closure#1}<'_0, E, T1>}]
    Source: 'src/cipher.rs', lines 153:62-155:17 -/
@[reducible]
def
  cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple
  {E : Type _} {T1 : Type _} (engineArgon2EngineInst : engine.Argon2Engine E)
  (coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst :
  core.ops.function.FnMut T1 (Std.U32 × Std.U32)
  (core.ops.control_flow.ControlFlow Unit Unit)) : core.ops.function.FnOnce
  (cipher.Mhfe.decrypt.closure.closure_1 E T1) Std.U32
  (core.ops.control_flow.ControlFlow Unit Unit) := {
  call_once := fun c i => do
    let (o, _) ←
      cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple.call_once
        engineArgon2EngineInst
        coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst c i
    ok o
}


/-- Replaces the generated instance of the same name (MANIFEST-code.txt, "R"). Aeneas
generates the `call_mut` of this closure, which captures a mutable borrow, with a backward function
in its result, while `FnMut.call_mut` returns the output and the closure's new state; the new state
is the backward function applied to the state after the call, as in the generated `call_once`.
Trait implementation: [mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>}::decrypt::{closure}::{impl core::ops::function::FnMut<(u32,), core::ops::control_flow::ControlFlow<(), ()>> for mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>[TraitClause0]}::decrypt::{closure}::{closure#1}<'_0, E, T1>}]
    Source: 'src/cipher.rs', lines 153:62-155:17 -/
@[reducible]
def
  cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
  {E : Type _} {T1 : Type _} (engineArgon2EngineInst : engine.Argon2Engine E)
  (coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst :
  core.ops.function.FnMut T1 (Std.U32 × Std.U32)
  (core.ops.control_flow.ControlFlow Unit Unit)) : core.ops.function.FnMut
  (cipher.Mhfe.decrypt.closure.closure_1 E T1) Std.U32
  (core.ops.control_flow.ControlFlow Unit Unit) := {
  FnOnceInst :=
    cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleU32ControlFlowTupleTuple
    engineArgon2EngineInst
    coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
  call_mut := fun c i => do
    let (o, c1, back) ←
      cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut
        engineArgon2EngineInst
        coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst c i
    ok (o, back c1)
}


/-- Replaces the generated instance of the same name (MANIFEST-code.txt, "R"). This closure,
passed to `stack::cleared`, captures mutable borrows; Aeneas generates its `call_once` with the
values it gives back (the captured state) after the result, and the code that calls
`stack::cleared` takes them apart, but declares the instance with the result alone as its output.
The instance is declared here with the output that its `call_once` and its callers use; no
function changes.
 Trait implementation: [mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>}::encrypt::{impl core::ops::function::FnOnce<(), core::result::Result<core::ops::control_flow::ControlFlow<(), mhfe_core::phrase::Phrase>, mhfe_core::error::Error>> for mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>[TraitClause0]}::encrypt::{closure}<'_0, '_1, '_2, '_3, '_4, '_5, E, T1, T2>}]
    Source: 'src/cipher.rs', lines 76:23-117:9 -/
@[reducible]
def
  cipher.Mhfe.encrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTuplePhraseError
  {E : Type _} {T1 : Type _} {T2 : Type _} (engineArgon2EngineInst :
  engine.Argon2Engine E)
  (coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst :
  core.ops.function.FnMut T1 (Std.U32 × Std.U32)
  (core.ops.control_flow.ControlFlow Unit Unit))
  (coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst :
  core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow
  Unit Unit)) : core.ops.function.FnOnce (cipher.Mhfe.encrypt.closure E T1 T2) Unit
  ((core.result.Result (core.ops.control_flow.ControlFlow Unit
    phrase.Phrase) error.Error) × (cipher.Mhfe.encrypt.closure E T1 T2) ×
    (cipher.Mhfe.encrypt.closure E T1 T2) × (cipher.Mhfe.encrypt.closure E T1
    T2)) := {
  call_once :=
    cipher.Mhfe.encrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTuplePhraseError.call_once
    engineArgon2EngineInst
    coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
    coreopsfunctionFnMutT2TupleShared0PhraseControlFlowTupleTupleInst
}


/-- Replaces the generated instance of the same name (MANIFEST-code.txt, "R"). This closure,
passed to `stack::cleared`, captures mutable borrows; Aeneas generates its `call_once` with the
values it gives back (the captured state) after the result, and the code that calls
`stack::cleared` takes them apart, but declares the instance with the result alone as its output.
The instance is declared here with the output that its `call_once` and its callers use; no
function changes.
 Trait implementation: [mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>}::decrypt::{impl core::ops::function::FnOnce<(), core::result::Result<core::ops::control_flow::ControlFlow<(), mhfe_core::recovery::Recovery>, mhfe_core::error::Error>> for mhfe_core::cipher::{mhfe_core::cipher::Mhfe<E>[TraitClause0]}::decrypt::{closure}<'_0, '_1, '_2, '_3, '_4, '_5, E, T1>}]
    Source: 'src/cipher.rs', lines 142:23-157:9 -/
@[reducible]
def
  cipher.Mhfe.decrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTupleRecoveryError
  {E : Type _} {T1 : Type _} (engineArgon2EngineInst : engine.Argon2Engine E)
  (coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst :
  core.ops.function.FnMut T1 (Std.U32 × Std.U32)
  (core.ops.control_flow.ControlFlow Unit Unit)) : core.ops.function.FnOnce (cipher.Mhfe.decrypt.closure E T1) Unit
  ((core.result.Result (core.ops.control_flow.ControlFlow Unit
    recovery.Recovery) error.Error) × (cipher.Mhfe.decrypt.closure E T1) ×
    (cipher.Mhfe.decrypt.closure E T1)) := {
  call_once :=
    cipher.Mhfe.decrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTupleRecoveryError.call_once
    engineArgon2EngineInst
    coreopsfunctionFnMutT1PairU32U32ControlFlowTupleTupleInst
}

