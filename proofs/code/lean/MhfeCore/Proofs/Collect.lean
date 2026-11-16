import MhfeCore.Code

/-!
# `map` and `collect::<Result<Vec<_>, _>>` over a vector

`Recovery::readings` maps the lengths to readings and collects the results. The lemmas below say
what that gives when every call of the closure succeeds.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- The iterator state `it` yields `Ok y` for each `y` of `ys`, in order, and then ends. -/
def Yields {It B E : Type} (itInst : core.iter.traits.iterator.Iterator It (core.result.Result B E)) :
    It → List B → Prop
  | it, [] => itInst.next it ⦃ p => p.1 = none ⦄
  | it, y :: ys => itInst.next it ⦃ p => p.1 = some (.Ok y) ∧ Yields itInst p.2 ys ⦄

theorem iterToList_list_spec {T : Type} (inst : core.iter.traits.iterator.Iterator (List T) T)
    (hinst : ∀ l, inst.next l ⦃ p => p = (l.head?, l.tail) ⦄) :
    ∀ (l acc : List T),
      alloc.vec.FromIteratorVec.iterToList inst l acc ⦃ r => r = acc.reverse ++ l ⦄ := by
  intro l
  induction l with
  | nil =>
    intro acc
    rw [alloc.vec.FromIteratorVec.iterToList]
    apply WP.spec_bind (hinst [])
    rintro p rfl
    simp
  | cons x xs ih =>
    intro acc
    rw [alloc.vec.FromIteratorVec.iterToList]
    apply WP.spec_bind (hinst (x :: xs))
    rintro p rfl
    simp only [List.head?_cons, List.tail_cons]
    apply WP.spec_mono (ih (x :: acc))
    intro r hr; rw [hr]; simp

/-- Collecting an iterator that yields `Ok y` for each `y` of `ys` gives `Ok` of the vector of
`ys`. -/
theorem from_iter_result_spec {It B E : Type}
    (itInst : core.iter.traits.iterator.Iterator It (core.result.Result B E)) (it : It)
    (ys : List B) (hy : Yields itInst it ys) (hlen : ys.length ≤ Usize.max) :
    core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult.from_iter
      (core.iter.traits.collect.FromIteratorVec B)
      (core.iter.traits.collect.IntoIterator.Blanket itInst) it
      ⦃ r => ∃ v, r = .Ok v ∧ v.val = ys ⦄ := by
  unfold core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult.from_iter
  simp only [core.iter.traits.collect.IntoIterator.Blanket,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter]
  simp only [bind_tc_eq, bind_ok]
  refine WP.spec_bind (Pₘ := fun r => r = .Ok ((it, ([] : List B)).2 ++ ys)) ?_ ?_
  · have hy' : Yields itInst (it, ([] : List B)).1 ys := hy
    generalize (it, ([] : List B)) = st0 at hy' ⊢
    clear hy hlen
    induction ys generalizing st0 with
    | nil =>
      rw [loop.eq_1]
      simp only [Yields] at hy'
      simp only [bind_tc_eq, Std.bind_assoc]
      apply WP.spec_bind hy'
      rintro ⟨o, it1⟩ ho
      simp only at ho
      subst ho
      simp
    | cons y ys ih =>
      rw [loop.eq_1]
      simp only [Yields] at hy'
      simp only [bind_tc_eq, Std.bind_assoc]
      apply WP.spec_bind hy'
      rintro ⟨o, it1⟩ ⟨ho, hrest⟩
      simp only at ho hrest
      subst ho
      show Std.bind (ok (ControlFlow.cont (it1, st0.2 ++ [y]))) _ ⦃ _ ⦄
      rw [bind_ok]
      show loop _ (it1, st0.2 ++ [y]) ⦃ _ ⦄
      refine WP.spec_mono (ih (it1, st0.2 ++ [y]) hrest) ?_
      intro r hr; rw [hr]; simp
  · rintro r rfl
    simp only [List.nil_append, bind_tc_eq]
    unfold alloc.vec.FromIteratorVec.from_iter
    simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]
    simp only [bind_tc_eq, Std.bind_assoc]
    apply WP.spec_bind (iterToList_list_spec _ (by intro l; cases l <;> simp) ys [])
    rintro r rfl
    rw [dif_pos (by simpa using hlen)]
    simp

/-- Mapping a vector with a closure that gives `Ok (g x)` for each element `x` yields `g` of the
elements, in order. -/
theorem map_vec_yields {T B E Fc : Type}
    (fnInst : core.ops.function.FnMut Fc T (core.result.Result B E)) (c : Fc) (g : T → B) :
    ∀ (l : List T) (v : alloc.vec.Vec T), v.val = l →
      (∀ x ∈ l, fnInst.call_mut c x ⦃ p => p = (.Ok (g x), c) ⦄) →
      Yields (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
        (core.iter.traits.iterator.IteratorVecIntoIter T) fnInst) ⟨v, c⟩ (l.map g) := by
  intro l
  induction l with
  | nil =>
    intro v hv _
    simp only [Yields, List.map_nil, core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator,
      core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
      core.iter.traits.iterator.IteratorVecIntoIter, alloc.vec.into_iter.IteratorIntoIter.next]
    split
    · simp only [bind_tc_eq, bind_ok]
      show ok (none, _) ⦃ _ ⦄
      simp
    · rename_i h; rw [hv] at h; simp at h
  | cons x xs ih =>
    intro v hv hc
    simp only [Yields, List.map_cons, core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator,
      core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
      core.iter.traits.iterator.IteratorVecIntoIter, alloc.vec.into_iter.IteratorIntoIter.next]
    split
    · rename_i h; rw [hv] at h; simp at h
    · rename_i hd tl h
      rw [hv] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [bind_tc_eq, bind_ok]
      show Std.bind (fnInst.call_mut c x) _ ⦃ _ ⦄
      apply WP.spec_bind (hc x (by simp))
      rintro p rfl
      show ok _ ⦃ _ ⦄
      rw [WP.spec_ok]
      refine ⟨rfl, ?_⟩
      exact ih _ (by simp) (fun y hy => hc y (by simp [hy]))

end MhfeProofs
