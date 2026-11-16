import MhfeCore.Code

/-!
# Facts about the models of the opaque items

Wiping a buffer never fails and keeps its length; these lemmas let the proofs step over the wiping
of secrets, which changes no computed value.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

@[step] theorem zeroize_slice_u8_spec (s : Slice Std.U8) :
    Slice.Insts.ZeroizeZeroize.zeroize U8.Insts.ZeroizeDefaultIsZeroes s ⦃ r =>
      r.length = s.length ⦄ := by
  simp [Slice.Insts.ZeroizeZeroize.zeroize]

theorem mapM_ok {α β : Type} (f : α → RustM β) (hf : ∀ x, ∃ y, f x = ok y) (l : List α) :
    ∃ z, l.mapM f = ok z ∧ z.length = l.length := by
  induction l with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨z, hz, hl⟩ := ih
    obtain ⟨y, hy⟩ := hf x
    exact ⟨y :: z, by simp only [List.mapM_cons, hy, hz, bind_tc_ok]; rfl, by simp [hl]⟩

@[step] theorem zeroize_array_u8_spec {N : Std.Usize} (a : Array Std.U8 N) :
    Array.Insts.ZeroizeZeroize.zeroize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a
      ⦃ _ => True ⦄ := by
  obtain ⟨z, hz, hl⟩ := mapM_ok (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes).zeroize
    (fun x => ⟨_, by simp [zeroize.Zeroize.Blanket, zeroize.Zeroize.Blanket.zeroize,
      U8.Insts.ZeroizeDefaultIsZeroes]; rfl⟩) a.val
  have hN : z.length = N.val := by simp [hl, Array.property]
  simp [Array.Insts.ZeroizeZeroize.zeroize, hz, hN]

end MhfeProofs
