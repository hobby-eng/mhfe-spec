/-
The uniform probability mass functions of Mathlib before 2026-10-04 and two lemmas about them from
VCVio's former `ToMathlib.General`, kept here because the current Mathlib makes the uniform
distributions measures and VCVio removed that file. The definitions and proofs are those of
Mathlib's `Mathlib/Probability/Distributions/Uniform.lean` at revision 8f9d9cff (Copyright (c) 2024
Josha Dekker; authors Josha Dekker, Devon Tuma, Kexing Ying) and of VCVio's
`ToMathlib/General.lean` at revision e7f4c8d0 (Copyright (c) 2024 Devon Tuma), both released under
the Apache 2.0 license; only the namespace and the qualification of Mathlib names changed.
Inside `namespace MhfeLean`, `PMF.uniformOfFintype` and the other names below resolve to these
declarations, so the chapters keep their text.
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace MhfeLean
namespace PMF

variable {α : Type*}

open scoped NNReal ENNReal

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
noncomputable def uniformOfFinset (s : Finset α) (hs : s.Nonempty) : _root_.PMF α := by
  classical
  refine _root_.PMF.ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, if_false]

variable {s : Finset α} (hs : s.Nonempty) {a : α}

open scoped Classical in
@[simp]
theorem uniformOfFinset_apply (a : α) :
    uniformOfFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  rfl

theorem uniformOfFinset_apply_of_mem (ha : a ∈ s) : uniformOfFinset s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  simp [ha]

theorem uniformOfFinset_apply_of_notMem (ha : a ∉ s) : uniformOfFinset s hs a = 0 := by simp [ha]

@[simp]
theorem support_uniformOfFinset : (uniformOfFinset s hs).support = s := by
  classical
  ext x
  rw [_root_.PMF.mem_support_iff, uniformOfFinset_apply]
  by_cases h : x ∈ s <;> simp [h, ENNReal.natCast_ne_top]

theorem mem_support_uniformOfFinset_iff (a : α) : a ∈ (uniformOfFinset s hs).support ↔ a ∈ s := by
  simp

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_uniformOfFinset_apply :
    (uniformOfFinset s hs).toOuterMeasure t = (s.filter (· ∈ t)).card / s.card :=
  calc
    (uniformOfFinset s hs).toOuterMeasure t = ∑' x, if x ∈ t then uniformOfFinset s hs x else 0 :=
      _root_.PMF.toOuterMeasure_apply (uniformOfFinset s hs) t
    _ = ∑' x, if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [uniformOfFinset_apply, ← ite_and, and_comm]
    _ = ∑ x ∈ s.filter (· ∈ t), if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0∞)⁻¹ else 0 :=
      tsum_eq_sum fun _ hx => if_neg fun h => hx (Finset.mem_filter.2 h)
    _ = ∑ x ∈ s.filter (· ∈ t), (s.card : ℝ≥0∞)⁻¹ :=
      Finset.sum_congr rfl fun x hx => by
        have this : x ∈ s ∧ x ∈ t := by simpa using hx
        simp only [this, and_self_iff, if_true]
    _ = (s.filter (· ∈ t)).card / s.card := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
@[simp]
theorem toMeasure_uniformOfFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformOfFinset s hs).toMeasure t = (s.filter (· ∈ t)).card / s.card :=
  (_root_.PMF.toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans
    (toOuterMeasure_uniformOfFinset_apply hs t)

end Measure

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
noncomputable def uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] : _root_.PMF α :=
  uniformOfFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniformOfFintype_apply (a : α) : uniformOfFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformOfFintype, Finset.mem_univ, uniformOfFinset_apply]

@[simp]
theorem support_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] :
    (uniformOfFintype α).support = ⊤ :=
  Set.ext fun x => by simp [_root_.PMF.mem_support_iff]

theorem mem_support_uniformOfFintype (a : α) : a ∈ (uniformOfFintype α).support := by simp

theorem uniformOfFintype_cast (α β : Type _) [ha : Fintype α] [Nonempty α]
    [hb : Fintype β] [Nonempty β] (h : α = β) :
      cast (congrArg _root_.PMF h) (uniformOfFintype α) = @uniformOfFintype β _ _ := by
  subst h
  ext x
  simp only [cast_eq, uniformOfFintype_apply, inv_inj, Nat.cast_inj]
  exact @Fintype.card_congr α α ha hb (Equiv.refl α)

open Classical in
lemma uniformOfFintype_map_of_bijective {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → β) (hf : Function.Bijective f) :
    (uniformOfFintype α).map f = uniformOfFintype β := by
  have heq := Fintype.card_congr (Equiv.ofBijective f hf)
  ext x; obtain ⟨a, rfl⟩ := hf.2 x
  simp only [_root_.PMF.map_apply, uniformOfFintype_apply, heq, hf.1.eq_iff, eq_comm (a := a)]
  convert tsum_ite_eq a (fun _ : α => ((Fintype.card β : ENNReal)⁻¹))

end UniformOfFintype

end PMF
end MhfeLean
