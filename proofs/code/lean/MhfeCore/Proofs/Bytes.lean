import MhfeCore.Code
import MhfeCore.Spec.Spec

/-!
# Big-endian bytes
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

theorem toLEBytes_succ {w : Nat} (b : BitVec (w + 8)) :
    b.toLEBytes = b.setWidth 8 :: ((b >>> 8).setWidth w).toLEBytes := by
  conv_lhs => rw [BitVec.toLEBytes]
  simp only [gt_iff_lt]
  rfl

theorem toLEBytes_zero (b : BitVec 0) : b.toLEBytes = [] := by
  rw [BitVec.toLEBytes]; simp

/-- `u32::to_be_bytes` is `BE32` of the specification. -/
theorem to_be_bytes_be32 (x : Std.U32) :
    x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8) = MhfeSpec.be32 x.val := by
  have e : x.bv.toLEBytes = [x.bv.setWidth 8, ((x.bv >>> 8).setWidth 24).setWidth 8,
      ((((x.bv >>> 8).setWidth 24) >>> 8).setWidth 16).setWidth 8,
      ((((((x.bv >>> 8).setWidth 24) >>> 8).setWidth 16) >>> 8).setWidth 8).setWidth 8] := by
    rw [toLEBytes_succ (w := 24) x.bv, toLEBytes_succ (w := 16), toLEBytes_succ (w := 8),
      toLEBytes_succ (w := 0), toLEBytes_zero]
  have hx : x.bv.toNat < 4294967296 := by
    have := x.bv.isLt; simpa [UScalarTy.numBits] using this
  simp only [BitVec.toBEBytes, e, MhfeSpec.be32, MhfeSpec.byte, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, List.map_nil]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩ <;>
  congr 1 <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, UScalar.val] <;> try omega
  all_goals (generalize x.bv.toNat = n at *; omega)

end MhfeProofs
