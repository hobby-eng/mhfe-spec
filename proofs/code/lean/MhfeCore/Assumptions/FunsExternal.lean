-- [mhfe_core]: external functions, written by hand from the template that Aeneas generates
-- (MhfeCore/Extraction/FunsExternal_Template.lean). They are models of what the proof takes as
-- given: functions of the Rust standard library that Aeneas does not model, the operating-system
-- pages, the stack clearing, the hash functions, BIP39 and NFKD. The hash functions, PBKDF2, NFKD
-- and the UTF-8 check are Lean `opaque` constants: nothing about their values is known, so every
-- theorem holds for every choice of them. README.md lists every definition. The five
-- functions of mhfe_core that Aeneas cannot translate are in Translations.lean.
module
public import Aeneas
public import MhfeCore.Extraction.Types
@[expose] public section
open Aeneas Aeneas.Std RustM ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open mhfe_core

universe u v w x y

namespace MhfeModel

instance (n : Std.Usize) : Inhabited (Array Std.U8 n) := ⟨Array.repeat n 0#u8⟩

/-- BLAKE2b with a 32-byte output (RFC 7693), as a function of its whole input. -/
opaque blake2b256 : List Std.U8 → Array Std.U8 32#usize

/-- SHA-256, as a function of its whole input. -/
opaque sha256 : List Std.U8 → Array Std.U8 32#usize

/-- HMAC-SHA-256 of a message under a 64-byte key block (the only way the code calls it: the key
zero-padded to the block of SHA-256), as a function of the block's bytes and the message. -/
opaque hmacSha256 : List Std.U8 → List Std.U8 → Array Std.U8 32#usize

/-- The BIP39 seed (PBKDF2-HMAC-SHA512, 2048 iterations) of a phrase and a normalized
passphrase. -/
opaque bip39Seed : phrase.Phrase → Str → Array Std.U8 64#usize

/-- UTF8(NFKD(text)) with the Unicode 18.0.0 tables. -/
opaque nfkd : Str → List Std.U8

/-- Whether bytes are UTF-8. -/
opaque isUtf8 : List Std.U8 → Bool

/-- `n` zero bytes as a slice. -/
def zeros (n : Std.Usize) : Slice Std.U8 :=
  Slice.from (List.replicate n.val 0#u8) (by simp; scalar_tac)

/-- The text of a phrase. The model is an injective encoding, its word count in two bytes and then
its entropy; what the proof relies on is that reading the text of a phrase gives the phrase. -/
def phraseText (p : phrase.Phrase) : List Std.U8 :=
  [⟨BitVec.ofNat 8 (p.wordCount.val / 256)⟩, ⟨BitVec.ofNat 8 p.wordCount.val⟩] ++
    p.entropyBytes.val

end MhfeModel

/-! ## The Rust standard library -/

/-- [core::array::iter::{impl IntoIterator for [T; N]}::into_iter] -/
def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter {T : Type u} {N : Std.Usize}
    (a : Array T N) : RustM (core.array.iter.IntoIter T N) :=
  ok ⟨a.val⟩

/-- [core::array::iter::{impl Iterator for IntoIter<T, N>}::next] -/
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next {T : Type u}
    {N : Std.Usize} (it : core.array.iter.IntoIter T N) :
    RustM ((Option T) × (core.array.iter.IntoIter T N)) :=
  match it.rest with
  | [] => ok (none, it)
  | x :: xs => ok (some x, ⟨xs⟩)

/-- [core::option::{impl IntoIterator for Option<T>}::into_iter] -/
def core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter {T : Type u}
    (o : Option T) : RustM (core.option.IntoIter T) :=
  ok ⟨o⟩

/-- [core::option::{impl Iterator for IntoIter<A>}::next] -/
def core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next {A : Type u}
    (it : core.option.IntoIter A) : RustM ((Option A) × (core.option.IntoIter A)) :=
  ok (it.inner, ⟨none⟩)

/-- [core::iter::traits::iterator::Iterator::flatten]: no element is taken yet. -/
def core.iter.traits.iterator.Iterator.flatten.default {Self : Type u} {Clause0_Item : Type v}
    {Clause1_Item : Type w} {Clause1_IntoIter : Type x}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
    (collectIntoIteratorInst : core.iter.traits.collect.IntoIterator Clause0_Item Clause1_Item
      Clause1_IntoIter)
    (self : Self) :
    RustM (core.iter.adapters.flatten.Flatten Self Clause0_Item Clause1_Item Clause1_IntoIter) :=
  ok ⟨self, none⟩

/-- [core::iter::adapters::flatten::{impl Iterator for Flatten}::next]: the next element of the
current inner iterator; when it has none, the next inner iterator of the outer one; when the
outer one has none, `None`. (The standard library's flatten also keeps a back iterator for
`next_back`, which is never used here.) -/
def core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next {I : Type u}
    {U : Type v} {Clause0_Item : Type w} {Clause2_Item : Type x}
    (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (traitscollectIntoIteratorInst : core.iter.traits.collect.IntoIterator Clause0_Item
      Clause2_Item U)
    (traitsiteratorIteratorInst1 : core.iter.traits.iterator.Iterator U Clause2_Item)
    (self : core.iter.adapters.flatten.Flatten I Clause0_Item Clause2_Item U) :
    RustM ((Option Clause2_Item) × (core.iter.adapters.flatten.Flatten I Clause0_Item
      Clause2_Item U)) :=
  loop (fun (st : core.iter.adapters.flatten.Flatten I Clause0_Item Clause2_Item U) => do
    match st.front with
    | some inner =>
      let (o, inner1) ← traitsiteratorIteratorInst1.next inner
      match o with
      | some y => ok (ControlFlow.done (some y, { st with front := some inner1 }))
      | none => ok (ControlFlow.cont { st with front := none })
    | none =>
      let (o, outer1) ← traitsiteratorIteratorInst.next st.outer
      match o with
      | none => ok (ControlFlow.done (none, { outer := outer1, front := none }))
      | some x =>
        let inner ← traitscollectIntoIteratorInst.into_iter x
        ok (ControlFlow.cont { outer := outer1, front := some inner })) self

/-- [core::iter::traits::iterator::Iterator::filter] -/
def core.iter.traits.iterator.Iterator.filter.default {Self : Type u} {P : Type v}
    {Clause0_Item : Type w} (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
    (opsfunctionFnMutPTupleSharedClause0_ItemBoolInst : core.ops.function.FnMut P Clause0_Item
      Bool)
    (self : Self) (predicate : P) : RustM (core.iter.adapters.filter.Filter Self P) :=
  ok ⟨self, predicate⟩

/-- [core::iter::adapters::filter::{impl Iterator for Filter}::next]: the next element for which
the predicate holds. -/
def core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next {I : Type u}
    {P : Type v} {Clause0_Item : Type w}
    (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst : core.ops.function.FnMut P Clause0_Item
      Bool)
    (self : core.iter.adapters.filter.Filter I P) :
    RustM ((Option Clause0_Item) × (core.iter.adapters.filter.Filter I P)) :=
  loop (fun (st : core.iter.adapters.filter.Filter I P) => do
    let (o, iter1) ← traitsiteratorIteratorInst.next st.iter
    match o with
    | none => ok (ControlFlow.done (none, { st with iter := iter1 }))
    | some x =>
      let (b, pred1) ← opsfunctionFnMutPTupleShared0Clause0_ItemBoolInst.call_mut st.pred x
      if b then ok (ControlFlow.done (some x, ⟨iter1, pred1⟩))
      else ok (ControlFlow.cont ⟨iter1, pred1⟩)) self

/-- [core::iter::traits::iterator::Iterator::map] -/
def core.iter.traits.iterator.Iterator.map.default {Self : Type u} {B : Type v} {F : Type w}
    {Clause0_Item : Type x} (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
    (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F Clause0_Item B)
    (self : Self) (f : F) : RustM (core.iter.adapters.map.Map Self F) :=
  ok ⟨self, f⟩

/-- [core::iter::adapters::map::{impl Iterator for Map}::next] -/
def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next {B : Type u} {I : Type v}
    {F : Type w} {Clause0_Item : Type x}
    (traitsiteratorIteratorInst : core.iter.traits.iterator.Iterator I Clause0_Item)
    (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F Clause0_Item B)
    (self : core.iter.adapters.map.Map I F) :
    RustM ((Option B) × (core.iter.adapters.map.Map I F)) := do
  let (o, iter1) ← traitsiteratorIteratorInst.next self.iter
  match o with
  | none => ok (none, { self with iter := iter1 })
  | some x =>
    let (y, f1) ← opsfunctionFnMutFTupleClause0_ItemBInst.call_mut self.f x
    ok (some y, ⟨iter1, f1⟩)

/-- [core::iter::traits::iterator::Iterator::all]: false at the first element for which `f` is
false, true when there is none. -/
def core.iter.traits.iterator.Iterator.all.default {Self : Type u} {F : Type v}
    {Clause0_Item : Type w} (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
    (opsfunctionFnMutFTupleClause0_ItemBoolInst : core.ops.function.FnMut F Clause0_Item Bool)
    (self : Self) (f : F) : RustM (Bool × Self) :=
  loop (fun (st : Self × F) => do
    let (o, it1) ← IteratorInst.next st.1
    match o with
    | none => ok (ControlFlow.done (true, it1))
    | some x =>
      let (b, f1) ← opsfunctionFnMutFTupleClause0_ItemBoolInst.call_mut st.2 x
      if b then ok (ControlFlow.cont (it1, f1)) else ok (ControlFlow.done (false, it1)))
    (self, f)

/-- [core::slice::iter::{impl Iterator for Iter<'a, T>}::all], as `Iterator::all` on the slice's
iterator. -/
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all {T : Type u}
    {F : Type v} (opsfunctionFnMutFTupleSharedATBoolInst : core.ops.function.FnMut F T Bool)
    (self : core.slice.iter.Iter T) (f : F) : RustM (Bool × (core.slice.iter.Iter T)) :=
  loop (fun (st : core.slice.iter.Iter T × F) => do
    if h : st.1.i < st.1.slice.length then
      let x := st.1.slice.val[st.1.i]
      let (b, f1) ← opsfunctionFnMutFTupleSharedATBoolInst.call_mut st.2 x
      if b then ok (ControlFlow.cont ({ st.1 with i := st.1.i + 1 }, f1))
      else ok (ControlFlow.done (false, { st.1 with i := st.1.i + 1 }))
    else ok (ControlFlow.done (true, st.1)))
    (self, f)

/-- [core::result::{impl FromIterator<Result<T, E>> for Result<V, E>}::from_iter]: the first
error, or the collection of all the values. -/
def core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult.from_iter {T : Type}
    {E : Type} {V : Type} {I : Type} {Clause1_IntoIter : Type}
    (itertraitscollectFromIteratorInst : core.iter.traits.collect.FromIterator V T)
    (itertraitscollectIntoIteratorIResultClause1_IntoIterInst :
      core.iter.traits.collect.IntoIterator I (core.result.Result T E) Clause1_IntoIter)
    (iter : I) : RustM (core.result.Result V E) := do
  let it ← itertraitscollectIntoIteratorIResultClause1_IntoIterInst.into_iter iter
  let itInst := itertraitscollectIntoIteratorIResultClause1_IntoIterInst.iteratorInst
  let r ← loop (fun (st : Clause1_IntoIter × List T) => do
    let (o, it1) ← itInst.next st.1
    match o with
    | none => ok (ControlFlow.done (core.result.Result.Ok st.2))
    | some (core.result.Result.Err e) => ok (ControlFlow.done (core.result.Result.Err e))
    | some (core.result.Result.Ok x) => ok (ControlFlow.cont (it1, st.2 ++ [x]))) (it, [])
  match r with
  | core.result.Result.Err e => ok (core.result.Result.Err e)
  | core.result.Result.Ok xs =>
    let listInst : core.iter.traits.iterator.Iterator (List T) T :=
      { next := fun l => match l with
          | [] => ok (none, [])
          | y :: ys => ok (some y, ys) }
    let v ← itertraitscollectFromIteratorInst.from_iter
      (core.iter.traits.collect.IntoIterator.Blanket listInst) xs
    ok (core.result.Result.Ok v)

/-- [core::iter::range::Step::forward]: `forward_checked(start, n).expect(..)`. -/
def core.iter.range.Step.forward.default {Self : Type u} (StepInst : core.iter.range.Step Self)
    (start : Self) (n : Std.Usize) : RustM Self := do
  let o ← StepInst.forward_checked start n
  match o with
  | some y => ok y
  | none => fail panic

/-- [core::iter::range::Step::forward_unchecked]: as `forward` (overflow is undefined behaviour). -/
def core.iter.range.Step.forward_unchecked.default {Self : Type u}
    (StepInst : core.iter.range.Step Self) (start : Self) (n : Std.Usize) : RustM Self :=
  core.iter.range.Step.forward.default StepInst start n

/-- [core::iter::range::Step::backward]: `backward_checked(start, n).expect(..)`. -/
def core.iter.range.Step.backward.default {Self : Type u} (StepInst : core.iter.range.Step Self)
    (start : Self) (n : Std.Usize) : RustM Self := do
  let o ← StepInst.backward_checked start n
  match o with
  | some y => ok y
  | none => fail panic

/-- [core::iter::range::Step::backward_unchecked]: as `backward`. -/
def core.iter.range.Step.backward_unchecked.default {Self : Type u}
    (StepInst : core.iter.range.Step Self) (start : Self) (n : Std.Usize) : RustM Self :=
  core.iter.range.Step.backward.default StepInst start n

/-- [core::ops::control_flow::ControlFlow::is_break] -/
def core.ops.control_flow.ControlFlow.is_break {B : Type u} {C : Type v}
    (cf : core.ops.control_flow.ControlFlow B C) : RustM Bool :=
  match cf with
  | core.ops.control_flow.ControlFlow.Break _ => ok true
  | core.ops.control_flow.ControlFlow.Continue _ => ok false

/-- [core::ops::control_flow::ControlFlow::map_continue] -/
def core.ops.control_flow.ControlFlow.map_continue {B : Type u} {C : Type v} {T : Type w}
    {F : Type x} (functionFnOnceFTupleCTInst : core.ops.function.FnOnce F C T)
    (cf : core.ops.control_flow.ControlFlow B C) (f : F) :
    RustM (core.ops.control_flow.ControlFlow B T) :=
  match cf with
  | core.ops.control_flow.ControlFlow.Break b => ok (core.ops.control_flow.ControlFlow.Break b)
  | core.ops.control_flow.ControlFlow.Continue c => do
    let t ← functionFnOnceFTupleCTInst.call_once f c
    ok (core.ops.control_flow.ControlFlow.Continue t)

/-- [core::ops::range::RangeBounds::contains] -/
def core.ops.range.RangeBounds.contains.default {Self : Type u} {T : Type v} {U : Type w}
    (RangeBoundsInst : core.ops.range.RangeBounds Self T)
    (cmpPartialOrdInst : core.cmp.PartialOrd T U) (cmpPartialOrdInst1 : core.cmp.PartialOrd U T)
    (self : Self) (item : U) : RustM Bool := do
  let s ← RangeBoundsInst.start_bound self
  let lo ← match s with
    | core.ops.range.Bound.Included start => cmpPartialOrdInst.le start item
    | core.ops.range.Bound.Excluded start => cmpPartialOrdInst.lt start item
    | core.ops.range.Bound.Unbounded => ok true
  if lo then
    let e ← RangeBoundsInst.end_bound self
    match e with
    | core.ops.range.Bound.Included last => cmpPartialOrdInst1.le item last
    | core.ops.range.Bound.Excluded last => cmpPartialOrdInst1.lt item last
    | core.ops.range.Bound.Unbounded => ok true
  else ok false

/-- [core::option::Option::filter] -/
def core.option.Option.filter {T : Type u} {P : Type v}
    (opsfunctionFnOncePTupleSharedTBoolInst : core.ops.function.FnOnce P T Bool)
    (o : Option T) (predicate : P) : RustM (Option T) :=
  match o with
  | none => ok none
  | some x => do
    let b ← opsfunctionFnOncePTupleSharedTBoolInst.call_once predicate x
    if b then ok (some x) else ok none

/-- [core::option::{impl PartialEq for Option<T>}::eq] -/
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type u}
    (cmpPartialEqInst : core.cmp.PartialEq T T) (a b : Option T) : RustM Bool :=
  match a, b with
  | none, none => ok true
  | some x, some y => cmpPartialEqInst.eq x y
  | _, _ => ok false

/-- [core::result::Result::ok] -/
def core.result.Result.ok {T : Type u} {E : Type v} (r : core.result.Result T E) :
    RustM (Option T) :=
  match r with
  | core.result.Result.Ok x => RustM.ok (some x)
  | core.result.Result.Err _ => RustM.ok none

/-- [core::convert::{impl AsRef<U> for &T}::as_ref] -/
def Shared0T.Insts.CoreConvertAsRef.as_ref {T : Type u} {U : Type v}
    (AsRefInst : core.convert.AsRef T U) (x : T) : RustM U :=
  AsRefInst.as_ref x

/-- [core::convert::{impl AsRef<[T]> for [T]}::as_ref] -/
def Slice.Insts.CoreConvertAsRefSlice.as_ref {T : Type u} (s : Slice T) : RustM (Slice T) := ok s

/-- [core::str::converts::from_utf8]: the bytes as text when they are UTF-8. -/
def core.str.converts.from_utf8 (s : Slice Std.U8) :
    RustM (core.result.Result Str core.str.error.Utf8Error) :=
  if MhfeModel.isUtf8 s.val then ok (core.result.Result.Ok s)
  else ok (core.result.Result.Err ⟨⟩)

/-! ## Operating system and stack (`src/os.rs`, `src/stack.rs`) -/

/-- [mhfe_core::stack::overwrite]: overwrites 128 KiB of the stack; no value changes. -/
def stack.overwrite : RustM Unit := ok ()

/-- [mhfe_core::os::unix::{mhfe_core::os::Pages}::new]: pages of `bytes` zero bytes. -/
def os.unix.Pages.new (bytes : Std.Usize) : RustM os.Pages := ok ⟨MhfeModel.zeros bytes⟩

/-- [mhfe_core::os::{mhfe_core::os::Pages}::as_slice] -/
def os.Pages.as_slice (p : os.Pages) : RustM (Slice Std.U8) := ok p.bytes

/-- [mhfe_core::os::{mhfe_core::os::Pages}::as_mut_slice]: the bytes, to change in place; a slice
given back has the same length. -/
def os.Pages.as_mut_slice (p : os.Pages) :
    RustM ((Slice Std.U8) × (Slice Std.U8 → os.Pages)) :=
  ok (p.bytes, fun s => if s.length = p.bytes.length then ⟨s⟩ else p)

/-! ## The native engine (not used by any theorem, which hold for every engine) -/

def engine.native.NativeArgon2.new (memory_kib : Std.U32) :
    RustM (core.result.Result engine.native.NativeArgon2 error.Error) :=
  ok (core.result.Result.Err error.Error.OutOfMemory)

def engine.native.NativeArgon2.Insts.Mhfe_coreEngineArgon2Engine.argon2id
    (self : engine.native.NativeArgon2) (password : Slice Std.U8) (salt : Array Std.U8 16#usize)
    (memory_kib passes : Std.U32) (key : Array Std.U8 32#usize) :
    RustM ((core.result.Result Unit error.Error) × engine.native.NativeArgon2 ×
      (Array Std.U8 32#usize)) :=
  ok (core.result.Result.Err error.Error.OutOfMemory, self, key)

/-! ## Hash crates (shims of the harness) -/

/-- [blake2::Blake2b::new] -/
def blake2_1.Blake2b.new (N : Type u) : RustM (blake2_1.Blake2b N) := ok ⟨[]⟩

/-- [blake2::Blake2b::chain_update] -/
def blake2_1.Blake2b.chain_update {N : Type u} {T : Type v}
    (coreconvertAsRefTSliceU8Inst : core.convert.AsRef T (Slice Std.U8))
    (self : blake2_1.Blake2b N) (data : T) : RustM (blake2_1.Blake2b N) := do
  let s ← coreconvertAsRefTSliceU8Inst.as_ref data
  ok ⟨self.input ++ s.val⟩

/-- [blake2::Blake2b::finalize] -/
def blake2_1.Blake2b.finalize {N : Type u} (self : blake2_1.Blake2b N) :
    RustM (Array Std.U8 32#usize) :=
  ok (MhfeModel.blake2b256 self.input)

/-- [hmac::CtOutput::into_bytes] -/
def hmac.CtOutput.into_bytes (c : hmac.CtOutput) : RustM (Array Std.U8 32#usize) := ok c.tag

/-- [hmac::{impl KeyInit for Hmac<D>}::new]: keyed with a key block of 64 bytes. -/
def hmac.Hmac.Insts.HmacKeyInit.new (D : Type u) (key : Array Std.U8 64#usize) :
    RustM (hmac.Hmac D) :=
  ok ⟨key, []⟩

/-- [hmac::Hmac::update] -/
def hmac.Hmac.update {D : Type u} (self : hmac.Hmac D) (data : Slice Std.U8) :
    RustM (hmac.Hmac D) :=
  ok ⟨self.key, self.input ++ data.val⟩

/-- [hmac::Hmac::finalize] -/
def hmac.Hmac.finalize {D : Type u} (self : hmac.Hmac D) : RustM hmac.CtOutput :=
  ok ⟨MhfeModel.hmacSha256 self.key.val self.input⟩

/-- [sha2::Sha256::new] -/
def sha2.Sha256.new : RustM sha2.Sha256 := ok ⟨[]⟩

/-- [sha2::Sha256::chain_update] -/
def sha2.Sha256.chain_update {T : Type u}
    (coreconvertAsRefTSliceU8Inst : core.convert.AsRef T (Slice Std.U8)) (self : sha2.Sha256)
    (data : T) : RustM sha2.Sha256 := do
  let s ← coreconvertAsRefTSliceU8Inst.as_ref data
  ok ⟨self.input ++ s.val⟩

/-- [sha2::Sha256::finalize] -/
def sha2.Sha256.finalize (self : sha2.Sha256) : RustM (Array Std.U8 32#usize) :=
  ok (MhfeModel.sha256 self.input)

/-- [sha2::Sha256::digest] -/
def sha2.Sha256.digest {T : Type u}
    (coreconvertAsRefTSliceU8Inst : core.convert.AsRef T (Slice Std.U8)) (data : T) :
    RustM (Array Std.U8 32#usize) := do
  let s ← coreconvertAsRefTSliceU8Inst.as_ref data
  ok (MhfeModel.sha256 s.val)

/-! ## zeroize: a wiped value is the type's zero (`Default`) -/

/-- [zeroize::{impl<Z: DefaultIsZeroes> Zeroize for Z}::zeroize] -/
def zeroize.Zeroize.Blanket.zeroize {Z : Type u} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z)
    (z : Z) : RustM Z :=
  DefaultIsZeroesInst.coredefaultDefaultInst.default

/-- [zeroize::{impl<Z: Zeroize, const N: usize> Zeroize for [Z; N]}::zeroize] -/
def Array.Insts.ZeroizeZeroize.zeroize {Z : Type u} {N : Std.Usize} (ZeroizeInst : zeroize.Zeroize Z)
    (a : Array Z N) : RustM (Array Z N) := do
  let l ← a.val.mapM ZeroizeInst.zeroize
  if h : l.length = N.val then ok (Array.from l h) else fail panic

/-- [zeroize::{impl<Z: DefaultIsZeroes> Zeroize for [Z]}::zeroize] -/
def Slice.Insts.ZeroizeZeroize.zeroize {Z : Type u} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z)
    (s : Slice Z) : RustM (Slice Z) := do
  let z ← DefaultIsZeroesInst.coredefaultDefaultInst.default
  ok (Slice.from (List.replicate s.length z) (by simp))

/-! ## BIP39 and NFKD (`src/phrase.rs`, `src/nfkd.rs`) -/

/-- [mhfe_core::phrase::WORD_COUNTS] -/
def phrase.WORD_COUNTS : RustM (Array Std.Usize 5#usize) :=
  ok (Array.make 5#usize [12#usize, 15#usize, 18#usize, 21#usize, 24#usize])

/-- [mhfe_core::phrase::{mhfe_core::phrase::Phrase}::words] -/
def phrase.Phrase.words (p : phrase.Phrase) : RustM Std.Usize := ok p.wordCount

/-- [mhfe_core::phrase::{mhfe_core::phrase::Phrase}::entropy]: the entropy in a secret of its
own length. -/
def phrase.Phrase.entropy (p : phrase.Phrase) : RustM protect.Secret :=
  ok ⟨⟨p.entropyBytes⟩, ⟨BitVec.ofNat _ p.entropyBytes.length⟩,
    ⟨BitVec.ofNat _ p.entropyBytes.length⟩⟩

/-- [mhfe_core::phrase::{mhfe_core::phrase::Phrase}::encode]: `bip39::Mnemonic::from_entropy_in`
accepts 16 to 32 bytes in steps of 4 and gives three words for every four bytes. -/
def phrase.Phrase.encode (entropy : Slice Std.U8) :
    RustM (core.result.Result phrase.Phrase error.Error) :=
  if entropy.length ∈ [16, 20, 24, 28, 32] then
    ok (core.result.Result.Ok ⟨⟨BitVec.ofNat _ (entropy.length / 4 * 3)⟩, entropy⟩)
  else
    ok (core.result.Result.Err (error.Error.InvalidEntropyLength
      ⟨BitVec.ofNat _ entropy.length⟩))

/-- [mhfe_core::phrase::{mhfe_core::phrase::Phrase}::as_str] -/
def phrase.Phrase.as_str (p : phrase.Phrase) : RustM Str :=
  if h : (MhfeModel.phraseText p).length ≤ Usize.max then
    ok (Slice.from (MhfeModel.phraseText p) h)
  else fail panic

/-- [mhfe_core::phrase::{mhfe_core::phrase::Phrase}::read_text]: the inverse of the text model
`MhfeModel.phraseText`. On every text of at least two bytes it returns `Ok` with the phrase those
bytes encode, without checking the word count or the length; on a shorter text it reports an
invalid word count. The proof uses it only on the output of `as_str`, where it gives the phrase
back: the decoding of the words in the creation check therefore always succeeds in the model, and
that check's test of the words' encoding is assumed, not proved. -/
def phrase.Phrase.read_text (text : Str) : RustM (core.result.Result phrase.Phrase error.Error) :=
  match text.val with
  | hi :: lo :: rest =>
    if h : rest.length ≤ Usize.max then
      ok (core.result.Result.Ok
        ⟨⟨BitVec.ofNat _ (hi.val * 256 + lo.val)⟩, Slice.from rest h⟩)
    else ok (core.result.Result.Err (error.Error.InvalidWordCount 0#usize))
  | _ => ok (core.result.Result.Err (error.Error.InvalidWordCount 0#usize))

/-- [mhfe_core::phrase::{mhfe_core::phrase::Phrase}::mnemonic] -/
def phrase.Phrase.mnemonic (p : phrase.Phrase) : RustM bip39.Mnemonic := ok ⟨p⟩

/-- [bip39::Mnemonic::to_seed_normalized] -/
def bip39.Mnemonic.to_seed_normalized (m : bip39.Mnemonic) (passphrase : Str) :
    RustM (Array Std.U8 64#usize) :=
  ok (MhfeModel.bip39Seed m.phrase passphrase)

/-- [mhfe_core::nfkd::{mhfe_core::nfkd::Nfkd<'a>}::of] -/
def nfkd.Nfkd.of (text : Str) : RustM nfkd.Nfkd := ok ⟨text⟩

/-- [mhfe_core::nfkd::{mhfe_core::nfkd::Nfkd<'a>}::write]: UTF8(NFKD(text)) in a secret. -/
def nfkd.Nfkd.write (n : nfkd.Nfkd) : RustM protect.Secret :=
  let b := MhfeModel.nfkd n.text
  if h : b.length ≤ Usize.max then
    ok ⟨⟨Slice.from b h⟩, ⟨BitVec.ofNat _ b.length⟩, ⟨BitVec.ofNat _ b.length⟩⟩
  else fail panic

/-! ## Formatting (never part of a computed value) -/

def feistel.Geometry.Insts.CoreFmtDebug.fmt (g : feistel.Geometry) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

def recovery.Recovery.Insts.CoreFmtDebug.fmt (r : recovery.Recovery) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

def recovery.Reading.Insts.CoreFmtDebug.fmt (r : recovery.Reading) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

def suite.Suite.Insts.CoreFmtDebug.fmt (s : suite.Suite) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

def suite.WorkFactor.Insts.CoreFmtDebug.fmt (w : suite.WorkFactor) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)

def wallet_check.Seed.Insts.CoreFmtDebug.fmt (s : wallet_check.Seed) (f : core.fmt.Formatter) :
    RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (core.result.Result.Ok (), f)
