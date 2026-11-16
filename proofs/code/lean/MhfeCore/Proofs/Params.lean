import Mathlib.Tactic.IntervalCases
import MhfeCore.Code
import MhfeCore.Spec.Spec

/-!
# Suite parameters and the work factor in the code
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- `WorkFactor::memory_kib` computes `m(MEM)` without overflow for every accepted level. -/
theorem memory_kib_spec (w : suite.WorkFactor) (h : w.memory_level.val ≤ 21) :
    suite.WorkFactor.memory_kib w ⦃ r => r.val = MhfeSpec.memoryKiB w.memory_level.val ⦄ := by
  unfold suite.WorkFactor.memory_kib
  step*
  rw [r_post, i1_post, i3_post, i2_post, i_post, Nat.shiftLeft_eq]
  simp only [MhfeSpec.memoryKiB, U32.size]
  generalize w.memory_level.val = m at *
  interval_cases m <;> norm_num [U32.numBits, UScalarTy.numBits]

/-- `WorkFactor::passes` computes `t(PIM) = 12 (PIM + 1)` without overflow for every accepted PIM. -/
theorem passes_spec (w : suite.WorkFactor) (h : w.pim.val ≤ 1023) :
    suite.WorkFactor.passes w ⦃ r => r.val = MhfeSpec.passes w.pim.val ⦄ := by
  unfold suite.WorkFactor.passes suite.BASE_PASSES
  step*
  simp [MhfeSpec.passes, *]

/-- `WorkFactor::new` accepts exactly the PIM values up to 1023 and the memory levels up to 21
(WF-2), checking the PIM first. -/
theorem new_spec (pim mem : Std.U32) :
    suite.WorkFactor.new pim mem ⦃ r =>
      (pim.val ≤ MhfeSpec.maxPim ∧ mem.val ≤ MhfeSpec.maxMemoryLevel →
        r = core.result.Result.Ok { pim, memory_level := mem }) ∧
      (MhfeSpec.maxPim < pim.val → r = core.result.Result.Err (error.Error.InvalidPim pim)) ∧
      (pim.val ≤ MhfeSpec.maxPim → MhfeSpec.maxMemoryLevel < mem.val →
        r = core.result.Result.Err (error.Error.InvalidMemoryLevel mem)) ⦄ := by
  unfold suite.WorkFactor.new suite.WorkFactor.MAX_PIM suite.WorkFactor.MAX_MEMORY_LEVEL
  simp only [MhfeSpec.maxPim, MhfeSpec.maxMemoryLevel]
  split_ifs with h1 h2 <;> simp_all

end MhfeProofs
