import MhfeCore.Proofs.Geometry

/-!
# Packing of suite 3 in the code

`pack` writes `X = E || Trunc_r(SHA-256(E))`, `unpack` checks one layout and `detected_lengths`
lists the short layouts that match, as the specification's `pack`, `layoutMatches` and `detected`.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- SHA-256 of the specification, from the model of the hash. -/
noncomputable def shaF (b : List Std.U8) : List Std.U8 := (MhfeModel.sha256 b).val

theorem shaF_length (b : List Std.U8) : (shaF b).length = 32 := by simp [shaF]

theorem entropy_of_words_spec (w : Std.Usize) (hw : w.val ≤ 24) :
    packing.entropy_of_words w ⦃ e => e.val = MhfeSpec.entropyBytes w.val ⦄ := by
  unfold packing.entropy_of_words
  step*
  simp [MhfeSpec.entropyBytes, *]

theorem words_of_entropy_spec (b : Std.Usize) (hb : b.val ≤ 32) :
    packing.words_of_entropy b ⦃ w => w.val = b.val / 4 * 3 ⦄ := by
  unfold packing.words_of_entropy
  step*

theorem state_words_spec : packing.STATE_WORDS ⦃ w => w.val = 24 ⦄ := by
  unfold packing.STATE_WORDS packing.words_of_entropy
  simp only [packing.STATE_BYTES]
  step*

/-- `pack` writes the specification's `X` for an entropy of at most 32 bytes. -/
theorem pack_spec (e : Slice Std.U8) (he : e.val.length ≤ 32) :
    packing.pack e ⦃ s => SecretOk s ∧ s.len.val = MhfeSpec.stateBytes ∧
      secretBytes s = MhfeSpec.pack shaF e.val ⦄ := by
  unfold packing.pack
  simp only [packing.STATE_BYTES, sha2.Sha256.digest, Shared0T.Insts.CoreConvertAsRef.as_ref,
    Slice.Insts.CoreConvertAsRefSlice.as_ref]
  let* ⟨ state, hok, hlen, hbytes ⟩ ← zeroed_spec
  let* ⟨ s, back0, hs, hback0 ⟩ ← as_mut_bytes_spec
  have hsl : s.val.length = 32 := by rw [hs]; simp [secretBytes, hbytes, hlen]
  let* ⟨ source, verifier, back1, hsrc, hver, hback1 ⟩ ← split_at_mut_ok
  have hel : e.len.val = e.val.length := by simp [Slice.len]
  have hvl : verifier.val.length = 32 - e.val.length := by rw [hver]; simp; omega
  have hsl' : source.val.length = e.val.length := by rw [hsrc]; simp; omega
  step*
  · subst source1
    have hv0 : verifier.val = [] := by simp [Slice.length] at b_post; simp_all
    have hb1 := hback1 e verifier hel.symm (by rw [hvl, hsl, hel])
    obtain ⟨ok0, len0, by0⟩ := hback0 (back1 (e, verifier)) (by
      simp only [Slice.length]; rw [hb1, hsl]; simp; omega)
    refine ⟨ok0, by rw [len0, hlen]; rfl, ?_⟩
    rw [by0, hb1, hv0]
    have hn : ¬ e.val.length < 32 := by
      have : verifier.val.length = 0 := by rw [hv0]; rfl
      omega
    simp [MhfeSpec.pack, MhfeSpec.stateBytes, hn]
  · simp [Slice.len, Slice.length]; omega
  · subst source1
    subst verifier1
    have hne : verifier.val ≠ [] := by
      intro h; simp [Slice.length, h] at b_post; simp_all
    have hlt : e.val.length < 32 := by
      have : verifier.val.length ≠ 0 := by simpa using hne
      omega
    have hs1v : s1.val = (shaF e.val).take (32 - e.val.length) := by
      rw [s1_post]; simp [List.slice, shaF, Slice.len, hvl]
    have hs1l : s1.val.length = 32 - e.val.length := by rw [hs1v]; simp [shaF_length]
    have hb1 := hback1 e s1 hel.symm (by rw [hs1l, hsl, hel])
    obtain ⟨ok0, len0, by0⟩ := hback0 (back1 (e, s1)) (by
      simp only [Slice.length]; rw [hb1, hsl]; simp [hs1l]; omega)
    refine ⟨ok0, by rw [len0, hlen]; rfl, ?_⟩
    rw [by0, hb1, hs1v]
    simp [MhfeSpec.pack, MhfeSpec.stateBytes, hlt]

theorem slice_eq_u8_spec (a b : Slice Std.U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a b ⦃ r => r ↔ a = b ⦄ :=
  core.slice.cmp.PartialEqSlice.eq_homo_spec _ a b (by
    intro x y; simp [core.cmp.PartialEqU8, core.cmp.PartialEq.ne])

theorem entropyBytes_le (w : Nat) (hw : w ∈ MhfeSpec.wordCounts) :
    16 ≤ MhfeSpec.entropyBytes w ∧ MhfeSpec.entropyBytes w ≤ 32 := by
  simp [MhfeSpec.wordCounts] at hw
  rcases hw with h | h | h | h | h <;> subst h <;> decide

/-- `unpack` of a 32-byte state of suite 3 reads the layout of `words` words: the entropy when the
verifier matches, `VerifierMismatch` when it does not. -/
theorem unpack_spec (st : Slice Std.U8) (hst : st.val.length = MhfeSpec.stateBytes)
    (w : Std.Usize) (hw : w.val ∈ MhfeSpec.wordCounts) :
    packing.unpack st w ⦃ r => match r with
      | .Ok e => e.val = st.val.take (MhfeSpec.entropyBytes w.val) ∧
          MhfeSpec.layoutMatches shaF st.val w.val = true
      | .Err err => err = .VerifierMismatch ∧
          MhfeSpec.layoutMatches shaF st.val w.val = false ⦄ := by
  have hE := entropyBytes_le w.val hw
  have hw24 : w.val ≤ 24 := by simp [MhfeSpec.wordCounts] at hw; omega
  simp only [MhfeSpec.stateBytes] at hst
  unfold packing.unpack
  simp only [sha2.Sha256.digest, Shared0T.Insts.CoreConvertAsRef.as_ref,
    Slice.Insts.CoreConvertAsRefSlice.as_ref]
  let* ⟨ i, hi ⟩ ← entropy_of_words_spec
  step*
  · -- no verifier: the 24-word layout
    have hv0 : verifier.val = [] := by simp [Slice.length] at b_post; simp_all
    refine ⟨by rw [entropy_post2, hi], ?_⟩
    have hE32 : MhfeSpec.entropyBytes w.val = 32 := by
      have := congrArg List.length entropy_post3
      rw [hv0] at this; simp at this; omega
    simp [MhfeSpec.layoutMatches, MhfeSpec.stateBytes, hE32, hst]
  · let* ⟨ m, hm ⟩ ← slice_eq_u8_spec
    have hsv : s.val = (shaF (st.val.take (MhfeSpec.entropyBytes w.val))).take
        (MhfeSpec.stateBytes - MhfeSpec.entropyBytes w.val) := by
      rw [s_post, entropy_post2, hi]
      simp [List.slice, shaF, Slice.len, MhfeSpec.stateBytes, entropy_post3, hi, hst]
    have hlm : MhfeSpec.layoutMatches shaF st.val w.val = decide (verifier = s) := by
      simp only [MhfeSpec.layoutMatches]
      rw [← hsv, ← hi, ← entropy_post3]
      by_cases h : verifier = s
      · subst h; simp
      · have : verifier.val ≠ s.val := fun e => h (Slice.ext _ _ e)
        simp [h, this]
    step*

/-- A state of suite 4 has no verifier: `unpack` gives it back whole. -/
theorem unpack_exact (st : Slice Std.U8) (w : Std.Usize) (hw : w.val ∈ MhfeSpec.wordCounts)
    (hst : st.val.length = MhfeSpec.entropyBytes w.val) :
    packing.unpack st w ⦃ r => ∃ e, r = .Ok e ∧ e.val = st.val ⦄ := by
  have hE := entropyBytes_le w.val hw
  have hw24 : w.val ≤ 24 := by simp [MhfeSpec.wordCounts] at hw; omega
  unfold packing.unpack
  let* ⟨ i, hi ⟩ ← entropy_of_words_spec
  step*
  · refine ⟨entropy, rfl, ?_⟩
    rw [entropy_post2, hi, ← hst, List.take_length]

/-! ## The iterators of `detected_lengths` -/

/-- The next element of a list that `P` keeps, and the rest after it. -/
def filterNext {T : Type} (P : T → Bool) : List T → Option T × List T
  | [] => (none, [])
  | x :: xs => if P x then (some x, xs) else filterNext P xs

theorem filterNext_none {T : Type} (P : T → Bool) (l : List T) (h : (filterNext P l).1 = none) :
    l.filter P = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : P x
    · simp [filterNext, hx] at h
    · simp [filterNext, hx] at h; simp [hx, ih h]

theorem filterNext_some {T : Type} (P : T → Bool) (l : List T) (x : T)
    (h : (filterNext P l).1 = some x) :
    l.filter P = x :: (filterNext P l).2.filter P ∧ (filterNext P l).2.length < l.length := by
  induction l with
  | nil => simp [filterNext] at h
  | cons y ys ih =>
    by_cases hy : P y
    · simp [filterNext, hy] at h ⊢; subst h; simp [hy]
    · simp [filterNext, hy] at h ⊢
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨by simp [hy, h1], by omega⟩

theorem filterNext_sub {T : Type} (P : T → Bool) (l : List T) (y : T)
    (h : y ∈ (filterNext P l).2) : y ∈ l := by
  induction l with
  | nil => simp [filterNext] at h
  | cons x xs ih =>
    by_cases hx : P x
    · simp [filterNext, hx] at h; simp [h]
    · simp [filterNext, hx] at h; simp [ih h]

theorem filter_next_spec {T Pt : Type} {N : Std.Usize}
    (fnInst : core.ops.function.FnMut Pt T Bool) (P : T → Bool) (st : Pt) (l : List T)
    (hP : ∀ x ∈ l, fnInst.call_mut st x ⦃ r => r = (P x, st) ⦄) :
    core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next
      (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N) fnInst ⟨⟨l⟩, st⟩
      ⦃ r => r = ((filterNext P l).1, ⟨⟨(filterNext P l).2⟩, st⟩) ⦄ := by
  unfold core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next
  induction l with
  | nil =>
    rw [loop.eq_1]
    simp [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator,
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next, filterNext]
  | cons x xs ih =>
    rw [loop.eq_1]
    simp [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator,
      core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next]
    apply WP.spec_bind (hP x (by simp))
    rintro r rfl
    by_cases hx : P x
    · simp [hx, filterNext]
    · simp [hx, filterNext]
      exact ih (fun y hy => hP y (by simp [hy]))

theorem iterToList_filter_spec {T Pt : Type} {N : Std.Usize}
    (fnInst : core.ops.function.FnMut Pt T Bool) (P : T → Bool) (st : Pt) :
    ∀ (n : Nat) (l acc : List T), l.length ≤ n →
      (∀ x ∈ l, fnInst.call_mut st x ⦃ r => r = (P x, st) ⦄) →
      alloc.vec.FromIteratorVec.iterToList
        (core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator
          (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T N) fnInst)
        ⟨⟨l⟩, st⟩ acc ⦃ r => r = acc.reverse ++ l.filter P ⦄ := by
  intro n
  induction n with
  | zero =>
    intro l acc hl hP
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [alloc.vec.FromIteratorVec.iterToList]
    simp only [core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator]
    apply WP.spec_bind (filter_next_spec fnInst P st [] hP)
    rintro r rfl
    simp [filterNext]
  | succ n ih =>
    intro l acc hl hP
    rw [alloc.vec.FromIteratorVec.iterToList]
    simp only [core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator]
    apply WP.spec_bind (filter_next_spec fnInst P st l hP)
    rintro r rfl
    cases h : (filterNext P l).1 with
    | none => simp [filterNext_none P l h]
    | some x =>
      obtain ⟨hf, hlt⟩ := filterNext_some P l x h
      apply WP.spec_mono (ih (filterNext P l).2 (x :: acc) (by omega)
        (fun y hy => hP y (filterNext_sub P l y hy)))
      intro r hr
      rw [hr, hf]; simp

theorem short_word_counts_val :
    packing.SHORT_WORD_COUNTS.val = [12#usize, 15#usize, 18#usize, 21#usize] := by
  simp [packing.SHORT_WORD_COUNTS]

/-- `detected_lengths` of a 32-byte state lists the short layouts that match, in ascending order:
the specification's `detected`. -/
theorem detected_lengths_spec (st : Slice Std.U8) (hst : st.val.length = MhfeSpec.stateBytes) :
    packing.detected_lengths st ⦃ v =>
      v.val.map (·.val) = MhfeSpec.detected shaF st.val ∧ v.val.length ≤ 4 ⦄ := by
  unfold packing.detected_lengths
  simp only [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.iter.traits.iterator.Iterator.filter.default,
    core.iter.traits.iterator.Iterator.collect.default, core.iter.traits.collect.FromIteratorVec,
    alloc.vec.FromIteratorVec.from_iter, core.iter.traits.collect.IntoIterator.Blanket,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_tc_ok]
  have hP : ∀ x ∈ packing.SHORT_WORD_COUNTS.val,
      packing.detected_lengths.closure.Insts.CoreOpsFunctionFnMutTupleShared1UsizeBool.call_mut
        st x ⦃ r => r = (MhfeSpec.layoutMatches shaF st.val x.val, st) ⦄ := by
    intro x hx
    rw [short_word_counts_val] at hx
    have hxw : x.val ∈ MhfeSpec.wordCounts := by
      simp at hx; rcases hx with h | h | h | h <;> subst h <;> decide
    unfold packing.detected_lengths.closure.Insts.CoreOpsFunctionFnMutTupleShared1UsizeBool.call_mut
    apply WP.spec_bind (unpack_spec st hst x hxw)
    intro r hr
    cases r with
    | Ok e => simp only at hr; simp [core.result.Result.is_ok, hr.2]
    | Err e => simp only at hr; simp [core.result.Result.is_ok, hr.2]
  let* ⟨ l, hl ⟩ ← iterToList_filter_spec (N := 4#usize)
    packing.detected_lengths.closure.Insts.CoreOpsFunctionFnMutTupleShared1UsizeBool
    (fun x => MhfeSpec.layoutMatches shaF st.val x.val) st 4 packing.SHORT_WORD_COUNTS.val []
    (by rw [short_word_counts_val]; simp) hP
  have hl4 : l.length ≤ 4 := by
    rw [hl]; simp only [List.reverse_nil, List.nil_append]
    exact (List.length_filter_le _ _).trans (by simp [short_word_counts_val])
  step*
  · simp only [alloc.vec.Vec.from_val]
    refine ⟨?_, hl4⟩
    simp only [hl, List.reverse_nil, List.nil_append]
    rw [show (fun x : Std.Usize => MhfeSpec.layoutMatches shaF st.val x.val) =
      (fun n => MhfeSpec.layoutMatches shaF st.val n) ∘ (fun x : Std.Usize => x.val) from rfl,
      ← List.filter_map]
    simp [short_word_counts_val, MhfeSpec.detected, MhfeSpec.shortWordCounts]

end MhfeProofs
