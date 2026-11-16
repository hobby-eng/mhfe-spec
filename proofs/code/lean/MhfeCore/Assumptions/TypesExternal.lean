-- [mhfe_core]: external types, written by hand from the template that Aeneas generates
-- (MhfeCore/Extraction/TypesExternal_Template.lean). Each is the model of a type that the
-- extraction keeps opaque; README.md lists them with their reasons.
module
public import Aeneas
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

universe u v w x

/-! ## Types of the Rust standard library that Aeneas does not model -/

/-- [core::array::iter::IntoIter]: the elements not yet returned. -/
structure core.array.iter.IntoIter (T : Type u) (N : Std.Usize) where
  rest : List T

/-- [core::iter::adapters::flatten::Flatten]: the outer iterator and the current inner one. -/
structure core.iter.adapters.flatten.Flatten (I : Type u) (Clause0_Item : Type v)
    (Clause1_Item : Type w) (Clause1_IntoIter : Type x) where
  outer : I
  front : Option Clause1_IntoIter

/-- [core::iter::adapters::filter::Filter]: the iterator and the predicate. -/
structure core.iter.adapters.filter.Filter (I : Type u) (P : Type v) where
  iter : I
  pred : P

/-- [core::mem::maybe_uninit::MaybeUninit]: a value that may be missing (not used by any theorem). -/
structure core.mem.maybe_uninit.MaybeUninit (T : Type u) where
  value : Option T

/-- [core::option::IntoIter]: the element not yet returned. -/
structure core.option.IntoIter (A : Type u) where
  inner : Option A

/-- [core::str::error::Utf8Error] -/
structure core.str.error.Utf8Error where

/-! ## Types of mhfe_core kept opaque -/

/-- [mhfe_core::os::Pages] (unsafe code, `src/os.rs`): the bytes of the pages. The model keeps
their contents only; locking, dump exclusion and wiping are not values. -/
structure os.Pages where
  bytes : Slice Std.U8

/-- [mhfe_core::engine::native::NativeArgon2] (`src/engine/native.rs`): the native engine. No theorem
uses it: every theorem holds for every engine. -/
structure engine.native.NativeArgon2 where

/-- [mhfe_core::phrase::Phrase] (`src/phrase.rs`, on the `bip39` crate): a BIP39 phrase, as its
word count and its entropy. -/
structure phrase.Phrase where
  wordCount : Std.Usize
  entropyBytes : Slice Std.U8

/-- [mhfe_core::nfkd::Nfkd] (`src/nfkd.rs`, on the Unicode tables): the text to normalize. -/
structure nfkd.Nfkd where
  text : Str

/-! ## Types of the crates outside the proof

The hash crates are the shims of the extraction harness (`harness/shims`), which have the API of
`blake2`, `hmac` and `sha2` that the crate calls. Each hasher is modelled as the bytes it has been
given so far. -/

/-- [bip39::Mnemonic]: the phrase it was parsed from. -/
structure bip39.Mnemonic where
  phrase : phrase.Phrase

/-- [blake2::digest::consts::U32]: the output length of 32 bytes. -/
structure blake2_1.digest.consts.U32 where

/-- [blake2::Blake2b<N>]: the bytes given so far. -/
structure blake2_1.Blake2b (N : Type u) where
  input : List Std.U8

/-- [hmac::Hmac<D>]: the key block and the bytes given so far. -/
structure hmac.Hmac (D : Type u) where
  key : Array Std.U8 64#usize
  input : List Std.U8

/-- [hmac::CtOutput]: the tag. -/
structure hmac.CtOutput where
  tag : Array Std.U8 32#usize

/-- [sha2::Sha256]: the bytes given so far. -/
structure sha2.Sha256 where
  input : List Std.U8
