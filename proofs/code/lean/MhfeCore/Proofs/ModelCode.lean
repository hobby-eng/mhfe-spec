import MhfeCore.Proofs.Geometry
import MhfeCore.Spec.ModelLink

/-!
# The permutation of the code is the cipher of the Lean models

`forward_spec` and `inverse_spec` say that the code computes `Perm` and `Perm^-1` of the byte
specification; `MhfeModelLink` says that these are the cipher of `DeniabilityModel` and, for suite
3, `KnownPairModel.cipher` and the recovery program `Gamma2Model.finalize` of the guessing
theorems. Together: the code computes the cipher of the Lean models, with the model's tables
instantiated by the code's primitives. The security theorems of the models assume uniformly random
tables; that reading of the primitives is their assumption, not a theorem here.
-/

open Aeneas Aeneas.Std RustM mhfe_core MhfeSpec MhfeBits MhfeBridge MhfeLean MhfeModelLink

namespace MhfeProofs

variable {E T2 : Type} (inst : engine.Argon2Engine E)
  (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize)
  (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))

/-- `forward` of the code is the cipher of the deniability model, in both suites. -/
theorem forward_eq_deniabilityCipher (hA : EngineComputes inst A) (hcb : CallbackTotal fnInst)
    (self : feistel.Permutation E) (c : Setting) (hc : Matches self c)
    (v : Lemma1.State (8 * c.half)) (x : Slice Std.U8)
    (hx : x.val = toBytes c.half v.1 ++ toBytes c.half v.2) (cb : T2) :
    feistel.Permutation.forward inst fnInst self x cb ⦃ res _self1 _back _cb1 _cbBack =>
      ∀ st, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st) →
        secretBytes st =
          let w := DeniabilityModel.cipher c.password (tableA (modelPrims A) c)
            (tableB (modelPrims A) c c.half) (tableH (modelPrims A) c c.half) v
          toBytes c.half w.1 ++ toBytes c.half w.2 ⦄ := by
  have hh : c.half ≤ 32 := by have := hc.geo.2; rw [hc.half] at this; omega
  have hlen : x.val.length = 2 * c.half := by rw [hx]; simp [toBytes_length]; omega
  apply WP.spec_mono (forward_spec inst A hA fnInst hcb self c hc x hlen cb)
  rintro ⟨res, self1, back, cb1, cbBack⟩ ⟨_, hpost⟩ st hst
  rw [(hpost st hst).1, hx, perm_eq_deniabilityCipher _ c (modelPrims_wellFormed A) hh v]

/-- `inverse` of the code is the inverse of the cipher of the deniability model. -/
theorem inverse_eq_deniabilityCipher (hA : EngineComputes inst A) (hcb : CallbackTotal fnInst)
    (self : feistel.Permutation E) (c : Setting) (hc : Matches self c)
    (v : Lemma1.State (8 * c.half)) (y : Slice Std.U8)
    (hy : y.val = toBytes c.half v.1 ++ toBytes c.half v.2) (cb : T2) :
    feistel.Permutation.inverse inst fnInst self y cb ⦃ res _self1 _back _cb1 _cbBack =>
      ∀ st, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st) →
        secretBytes st =
          let w := (DeniabilityModel.cipher c.password (tableA (modelPrims A) c)
            (tableB (modelPrims A) c c.half) (tableH (modelPrims A) c c.half)).symm v
          toBytes c.half w.1 ++ toBytes c.half w.2 ⦄ := by
  have hh : c.half ≤ 32 := by have := hc.geo.2; rw [hc.half] at this; omega
  have hlen : y.val.length = 2 * c.half := by rw [hy]; simp [toBytes_length]; omega
  apply WP.spec_mono (inverse_spec inst A hA fnInst hcb self c hc y hlen cb)
  rintro ⟨res, self1, back, cb1, cbBack⟩ ⟨_, hpost⟩ st hst
  rw [(hpost st hst).1, hy, permInv_eq_deniabilityCipher _ c (modelPrims_wellFormed A) hh v]

/-- In suite 3, `inverse` of the code is the recovery program `Gamma2Model.finalize` of the
guessing theorems, run on the tables of the code's primitives. -/
theorem inverse_eq_finalize (hA : EngineComputes inst A) (hcb : CallbackTotal fnInst)
    (self : feistel.Permutation E) (words pim mem : Nat) (password : Bytes)
    (hc : Matches self ⟨.three, words, pim, mem, password⟩)
    {Entropy : Type} (g : Entropy → Gamma2Model.Hash) (v : Gamma2Model.State) (y : Slice Std.U8)
    (hy : y.val = toBytes 16 v.1 ++ toBytes 16 v.2) (cb : T2) :
    feistel.Permutation.inverse inst fnInst self y cb ⦃ res _self1 _back _cb1 _cbBack =>
      ∀ st, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st) →
        let c : Setting := ⟨.three, words, pim, mem, password⟩
        let T : Gamma2Model.Tables Bytes Entropy :=
          ⟨tableA (modelPrims A) c, tableB (modelPrims A) c 16, tableH (modelPrims A) c 16, g⟩
        secretBytes st =
          let w := (Gamma2Model.execute T (Gamma2Model.finalize password 12 v le_rfl)).1.1
          toBytes 16 w.1 ++ toBytes 16 w.2 ⦄ := by
  have hlen : y.val.length = 2 * (⟨.three, words, pim, mem, password⟩ : Setting).half := by
    rw [hy]; simp [toBytes_length, Setting.half, Suite.halfBytes]
  apply WP.spec_mono (inverse_spec inst A hA fnInst hcb self _ hc y hlen cb)
  rintro ⟨res, self1, back, cb1, cbBack⟩ ⟨_, hpost⟩ st hst
  simp only
  rw [(hpost st hst).1, hy]
  exact permInv_eq_finalize _ (modelPrims_wellFormed A) words pim mem password g v

end MhfeProofs
