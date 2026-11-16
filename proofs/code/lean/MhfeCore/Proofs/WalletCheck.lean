import MhfeCore.Proofs.Packing
import MhfeCore.Proofs.Bytes

/-!
# The wallet check (MHFE-WALLET-CHECK-SEED-1)

`seed_passes` is true exactly when the first 16 bits of
`SHA-256(ASCII("MHFE-WALLET-CHECK-SEED-1") || BE32(256) || seed)` are zero: the specification's
`walletCheckPasses`.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

theorem domain_val :
    wallet_check.DOMAIN.val = MhfeSpec.ascii "MHFE-WALLET-CHECK-SEED-1" := by
  unfold wallet_check.DOMAIN; decide +kernel

theorem entropy_bits_spec : wallet_check.ENTROPY_BITS ⦃ v => v.val = 256 ⦄ := by
  unfold wallet_check.ENTROPY_BITS
  simp only [packing.STATE_BYTES]
  step*

/-- `digest` is the SHA-256 of the domain, `BE32(256)` and the seed. -/
theorem digest_spec (seed : Slice Std.U8) :
    wallet_check.digest seed ⦃ d => d.val =
      shaF (MhfeSpec.ascii "MHFE-WALLET-CHECK-SEED-1" ++ MhfeSpec.be32 256 ++ seed.val) ⦄ := by
  unfold wallet_check.digest
  simp only [sha2.Sha256.new, sha2.Sha256.chain_update, sha2.Sha256.finalize,
    Shared0T.Insts.CoreConvertAsRef.as_ref, Slice.Insts.CoreConvertAsRefSlice.as_ref, bind_tc_ok]
  let* ⟨ i, hi ⟩ ← entropy_bits_spec
  step*
  rw [x_post, a_post, to_be_bytes_be32, hi, domain_val]
  simp [shaF]

/-- `Iterator::all` over a byte slice with the closure `|&b| b == 0`, from index `i` on. -/
theorem all_zero_spec (s : Slice Std.U8) :
    ∀ (n i : Nat), s.val.length - i = n →
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
        wallet_check.seed_passes.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool ⟨s, i⟩ ()
        ⦃ r => r.1 = (s.val.drop i).all (· == 0#u8) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i hi
    unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
    rw [loop.eq_1]
    have : ¬ i < s.length := by simp only [Slice.length]; omega
    simp [this, List.drop_eq_nil_of_le (show s.val.length ≤ i by omega)]
  | succ n ih =>
    intro i hi
    have hlt : i < s.length := by simp only [Slice.length]; omega
    have ih' := ih (i + 1) (by omega)
    unfold core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all at ih' ⊢
    rw [loop.eq_1]
    simp only [dif_pos hlt, wallet_check.seed_passes.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool,
      wallet_check.seed_passes.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut,
      bind_tc_ok]
    have hlt' : i < s.val.length := by simp only [Slice.length] at hlt; exact hlt
    by_cases h0 : s.val[i] = 0#u8
    · rw [List.drop_eq_getElem_cons hlt']
      simpa [h0, wallet_check.seed_passes.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool,
        wallet_check.seed_passes.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut]
        using ih'
    · simp [h0, wallet_check.seed_passes.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool,
        wallet_check.seed_passes.closure.Insts.CoreOpsFunctionFnMutTupleShared0U8Bool.call_mut]
      refine ⟨s.val[i], ?_, fun h => h0 (UScalar.eq_of_val_eq (by simpa using h))⟩
      rw [List.drop_eq_getElem_cons hlt']
      exact List.mem_cons_self

/-- `seed_passes` is the specification's wallet check. -/
theorem seed_passes_spec (seed : Slice Std.U8) :
    wallet_check.seed_passes seed ⦃ b => (b = true ↔ MhfeSpec.walletCheckPasses shaF seed.val) ⦄ := by
  unfold wallet_check.seed_passes
  let* ⟨ d, hd ⟩ ← digest_spec
  simp only [wallet_check.CHECK_BITS]
  step*
  simp only [core.slice.Slice.iter, bind_tc_ok]
  let* ⟨ passes, it, hr ⟩ ← all_zero_spec s 2 0 (by simp only [Slice.length] at s_post1; omega)
  step*
  simp only [MhfeSpec.walletCheckPasses]
  have hL := shaF_length (MhfeSpec.ascii "MHFE-WALLET-CHECK-SEED-1" ++ MhfeSpec.be32 256 ++ seed.val)
  generalize shaF (MhfeSpec.ascii "MHFE-WALLET-CHECK-SEED-1" ++ MhfeSpec.be32 256 ++ seed.val) = L
    at hL hd ⊢
  match L, hL with
  | a :: b :: rest, _ =>
    have hsv : s.val = [a, b] := by
      rw [s_post, i_post]; simp [List.slice, hd]
    rw [hr, hsv]
    simp only [List.drop_zero, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      beq_iff_eq, List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rw [h1]; rfl, by rw [h2]; rfl⟩

end MhfeProofs
