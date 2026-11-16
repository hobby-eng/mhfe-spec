import MhfeCore.Proofs.Recovery
import MhfeCore.Proofs.Collect

/-!
# The readings of a recovered state

`Recovery::readings` checks the stated length against the admission table, takes the lengths of
the readings by the length rules (suite 3) or the container's own length (suite 4), and gives for
each length the phrase whose entropy is the first `ENT/8` bytes of the state.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- The first `n` bytes of `x` as a slice. -/
def entropySlice (x : List Std.U8) (n : Nat) : Slice Std.U8 :=
  if h : (x.take n).length ≤ Usize.max then Slice.from (x.take n) h else Slice.new Std.U8

/-- The reading of the length `w` from the state `x`: the phrase of `w` words whose entropy is the
first `ENT/8` bytes of `x`, verified when `w` is among the detected lengths `d`. -/
def readingOf (x : List Std.U8) (d : List Std.Usize) (w : Std.Usize) : recovery.Reading where
  phrase := ⟨⟨BitVec.ofNat _ ((entropySlice x (MhfeSpec.entropyBytes w.val)).length / 4 * 3)⟩,
    entropySlice x (MhfeSpec.entropyBytes w.val)⟩
  verified := decide (w ∈ d)

theorem entropySlice_val (x : List Std.U8) (n : Nat) (h : n ≤ 32) :
    (entropySlice x n).val = x.take n := by
  unfold entropySlice
  rw [dif_pos (by simp; scalar_tac)]
  simp

/-- The reading of a phrase length has that many words and the first `ENT/8` bytes of the state
as its entropy. -/
theorem readingOf_phrase (x : List Std.U8) (d : List Std.Usize) (w : Std.Usize)
    (hw : w.val ∈ MhfeSpec.wordCounts) (hx : MhfeSpec.entropyBytes w.val ≤ x.length) :
    (readingOf x d w).phrase.wordCount.val = w.val ∧
    (readingOf x d w).phrase.entropyBytes.val = x.take (MhfeSpec.entropyBytes w.val) ∧
    ((readingOf x d w).verified = true ↔ w ∈ d) := by
  have hE := entropyBytes_le w.val hw
  have hv := entropySlice_val x (MhfeSpec.entropyBytes w.val) hE.2
  refine ⟨?_, hv, by simp [readingOf]⟩
  simp only [readingOf, Slice.length, hv, List.length_take, Nat.min_eq_left hx]
  simp [MhfeSpec.wordCounts] at hw
  rcases hw with h | h | h | h | h <;> rw [h] <;> simp [MhfeSpec.entropyBytes] <;>
    simp only [UScalar.val, BitVec.toNat_ofNat] <;>
    rcases System.Platform.numBits_eq with hb | hb <;> simp [hb]

abbrev readingsClosure :=
  recovery.Recovery.readings.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultReadingError

/-- The closure of `readings` gives the reading of a length whose layout unpacks. -/
theorem readings_closure_spec (rec : recovery.Recovery) (hok : SecretLe rec.state)
    (w : Std.Usize) (hw : w.val ∈ MhfeSpec.wordCounts)
    (hX : MhfeSpec.entropyBytes w.val ≤ (secretBytes rec.state).length)
    (hun : ∀ s : Slice Std.U8, s.val = secretBytes rec.state → packing.unpack s w ⦃ r =>
      ∃ e, r = .Ok e ∧ e.val = (secretBytes rec.state).take (MhfeSpec.entropyBytes w.val) ⦄) :
    readingsClosure.call_mut rec w ⦃ p =>
      p = (.Ok (readingOf (secretBytes rec.state) rec.detected.val w), rec) ⦄ := by
  have hE := entropyBytes_le w.val hw
  unfold readingsClosure
  simp only [recovery.Recovery.readings.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultReadingError]
  unfold recovery.Recovery.readings.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultReadingError.call_mut
  let* ⟨ s, hs ⟩ ← secret_as_bytes_le_spec
  apply WP.spec_bind (hun s hs)
  rintro r ⟨e, rfl, he⟩
  have hel : e.length = MhfeSpec.entropyBytes w.val := by
    simp only [Slice.length, he, List.length_take]; omega
  have henc : e.length ∈ ([16, 20, 24, 28, 32] : List Nat) := by
    rw [hel]; simp [MhfeSpec.wordCounts] at hw
    rcases hw with h | h | h | h | h <;> rw [h] <;> decide
  have hes : e = entropySlice (secretBytes rec.state) (MhfeSpec.entropyBytes w.val) :=
    Slice.ext _ _ (by rw [he, entropySlice_val _ _ hE.2])
  simp only [core.result.Result.Insts.CoreOpsTry.branch, phrase.Phrase.encode]
  step*
  rw [if_pos henc]
  step*
  let* ⟨ b, hb ⟩ ← contains_usize_spec
  simp only [readingOf, ← hes, hb]
  simp [alloc.vec.Vec.deref]

/-- The lengths that the length rules give are detected lengths or 24. -/
theorem lengthRules_sub (s : Option Nat) (d L : List Nat) (h : MhfeSpec.lengthRules s d = some L) :
    ∀ n ∈ L, n ∈ d ∨ n = 24 := by
  intro n hn
  cases s with
  | none =>
    simp only [MhfeSpec.lengthRules, Option.some.injEq] at h
    subst h
    unfold MhfeSpec.readingsWithoutLength at hn
    split at hn <;> simp_all
  | some m =>
    simp only [MhfeSpec.lengthRules] at h
    split_ifs at h with h1 h2 h3 <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
      rw [← h] at hn
    · simp at hn; subst hn; exact Or.inl h1
    · simp at hn; exact hn
    · unfold MhfeSpec.readingsWithoutLength at hn
      split at hn <;> simp_all

theorem layoutMatches_24 (x : List Std.U8) (hx : x.length = MhfeSpec.stateBytes) :
    MhfeSpec.layoutMatches shaF x 24 = true := by
  simp [MhfeSpec.layoutMatches, MhfeSpec.entropyBytes, MhfeSpec.stateBytes] at *
  simp [hx]

theorem detected_sub (x : List Std.U8) (n : Nat) (h : n ∈ MhfeSpec.detected shaF x) :
    n ∈ MhfeSpec.wordCounts ∧ MhfeSpec.layoutMatches shaF x n = true := by
  simp only [MhfeSpec.detected, List.mem_filter] at h
  refine ⟨?_, h.2⟩
  have := h.1
  simp [MhfeSpec.shortWordCounts] at this
  simp [MhfeSpec.wordCounts]; omega

/-- `readings` of a state of suite 3: when the stated length is admitted and the length rules give
the lengths `L`, the readings of `L`, in order; otherwise an error. -/
theorem readings_spec_3 (rec : recovery.Recovery) (hs : rec.suite = .TwentyFourWords)
    (hcw : rec.container_words.val = 24) (hok : SecretLe rec.state)
    (hlen : rec.state.len.val = MhfeSpec.stateBytes)
    (hd : rec.detected.val.map (·.val) = MhfeSpec.detected shaF (secretBytes rec.state))
    (hd4 : rec.detected.val.length ≤ 4) (stated : Option Std.Usize) :
    recovery.Recovery.readings rec stated ⦃ r => match r with
      | .Ok v => MhfeSpec.admitsLength 24 (stated.map (·.val)) ∧ ∃ L : List Std.Usize,
          MhfeSpec.lengthRules (stated.map (·.val)) (MhfeSpec.detected shaF (secretBytes rec.state)) =
            some (L.map (·.val)) ∧
          v.val = L.map (readingOf (secretBytes rec.state) rec.detected.val)
      | .Err _ => ¬ MhfeSpec.admitsLength 24 (stated.map (·.val)) ∨
          MhfeSpec.lengthRules (stated.map (·.val))
            (MhfeSpec.detected shaF (secretBytes rec.state)) = none ⦄ := by
  have hX : (secretBytes rec.state).length = MhfeSpec.stateBytes := by
    rw [secretBytes_length _ hok, hlen]
  unfold recovery.Recovery.readings stack.cleared stack.run
  simp only [stack.overwrite,
    recovery.Recovery.readings.closure.Insts.CoreOpsFunctionFnOnceTupleResultVecReadingError]
  unfold recovery.Recovery.readings.closure.Insts.CoreOpsFunctionFnOnceTupleResultVecReadingError.call_once
  simp only [bind_tc_eq, Std.bind_assoc]
  show Std.bind (Std.bind (recovery.admit rec.container_words stated) _) _ ⦃ _ ⦄
  simp only [Std.bind_assoc]
  apply WP.spec_bind (admit_spec rec.container_words stated)
  intro r1 hr1
  rw [hcw] at hr1
  cases r1 with
  | Err e =>
    have hna : ¬ MhfeSpec.admitsLength 24 (stated.map (·.val)) := fun h => by
      simpa using hr1.mpr h
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.«from», hna]
  | Ok u =>
    have ha : MhfeSpec.admitsLength 24 (stated.map (·.val)) := hr1.mp rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hs]
    simp only [bind_tc_eq, Std.bind_assoc]
    have hdd : rec.detected.deref.val = rec.detected.val := by simp [alloc.vec.Vec.deref]
    apply WP.spec_bind (lengths_spec stated rec.detected.deref (by rw [hdd]; exact hd4))
    intro r2 hr2
    rw [hdd, hd] at hr2
    cases r2 with
    | Err e =>
      simp only at hr2
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.«from», hr2.1]
    | Ok val =>
      simp only at hr2
      simp only [bind_ok, alloc.vec.IntoIteratorVec.into_iter,
        core.iter.traits.iterator.Iterator.map.default,
        core.iter.traits.iterator.Iterator.collect.default,
        core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult]
      have hmem : ∀ x ∈ val.val, x.val ∈ MhfeSpec.wordCounts ∧
          MhfeSpec.layoutMatches shaF (secretBytes rec.state) x.val = true := by
        intro x hx
        rcases lengthRules_sub _ _ _ hr2 x.val (List.mem_map_of_mem hx) with h | h
        · exact detected_sub _ _ h
        · rw [h]; exact ⟨by decide, layoutMatches_24 _ hX⟩
      have hy := map_vec_yields readingsClosure rec
        (readingOf (secretBytes rec.state) rec.detected.val) val.val val rfl (fun x hx => by
          obtain ⟨hw, hm⟩ := hmem x hx
          have hE := entropyBytes_le x.val hw
          refine readings_closure_spec rec hok x hw (by rw [hX]; exact hE.2) ?_
          intro s hs
          apply WP.spec_mono (unpack_spec s (by rw [hs, hX]) x hw)
          intro r hr
          cases r with
          | Ok e => exact ⟨e, rfl, by rw [hr.1, hs]⟩
          | Err e => simp [hs, hm] at hr)
      refine WP.spec_bind (Pₘ := fun r => ∃ v, r = .Ok v ∧
        v.val = val.val.map (readingOf (secretBytes rec.state) rec.detected.val)) ?_ ?_
      · refine WP.spec_bind (Pₘ := fun ii => ii = val) ((WP.spec_ok _).mpr rfl) ?_
        rintro ii rfl
        exact from_iter_result_spec _ _ _ hy (by simp only [List.length_map]; scalar_tac)
      · rintro r ⟨v, rfl, hv⟩
        simp only [WP.spec_ok]
        exact ⟨ha, val.val, hr2, hv⟩

/-- `readings` of a state of suite 4: when the stated length is admitted, the one reading of the
container's own length, whose entropy is the whole state; otherwise an error. -/
theorem readings_spec_4 (rec : recovery.Recovery) (hs : rec.suite = .SameLength)
    (hok : SecretLe rec.state) (w : Nat) (hw : w ∈ MhfeSpec.wordCounts)
    (hcw : rec.container_words.val = w) (hlen : rec.state.len.val = MhfeSpec.entropyBytes w)
    (stated : Option Std.Usize) :
    recovery.Recovery.readings rec stated ⦃ r => match r with
      | .Ok v => MhfeSpec.admitsLength w (stated.map (·.val)) ∧
          v.val = [readingOf (secretBytes rec.state) rec.detected.val rec.container_words]
      | .Err _ => ¬ MhfeSpec.admitsLength w (stated.map (·.val)) ⦄ := by
  have hX : (secretBytes rec.state).length = MhfeSpec.entropyBytes w := by
    rw [secretBytes_length _ hok, hlen]
  unfold recovery.Recovery.readings stack.cleared stack.run
  simp only [stack.overwrite]
  unfold recovery.Recovery.readings.closure.Insts.CoreOpsFunctionFnOnceTupleResultVecReadingError.call_once
  show Std.bind (Std.bind (recovery.admit rec.container_words stated) _) _ ⦃ _ ⦄
  simp only [Std.bind_assoc]
  apply WP.spec_bind (admit_spec rec.container_words stated)
  intro r1 hr1
  rw [hcw] at hr1
  cases r1 with
  | Err e =>
    have hna : ¬ MhfeSpec.admitsLength w (stated.map (·.val)) := fun h => by
      simpa using hr1.mpr h
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.«from», hna]
  | Ok u =>
    have ha : MhfeSpec.admitsLength w (stated.map (·.val)) := hr1.mp rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hs]
    have hwv : rec.container_words.val ∈ MhfeSpec.wordCounts := by rw [hcw]; exact hw
    have hE := entropyBytes_le _ hwv
    have hy := map_vec_yields readingsClosure rec
      (readingOf (secretBytes rec.state) rec.detected.val) [rec.container_words]
      (alloc.slice.Slice.into_vec (Array.make 1#usize [rec.container_words]).to_slice)
      (by simp [alloc.slice.Slice.into_vec, alloc.vec.Vec.val]) (fun x hx => by
        simp at hx; subst hx
        refine readings_closure_spec rec hok _ hwv (by rw [hX, hcw]) ?_
        intro s hs'
        apply WP.spec_mono (unpack_exact s _ hwv (by rw [hs', hX, hcw]))
        rintro r ⟨e, rfl, he⟩
        refine ⟨e, rfl, ?_⟩
        rw [he, hs', hcw, ← hX, List.take_length])
    simp only [alloc.vec.IntoIteratorVec.into_iter,
      core.iter.traits.iterator.Iterator.map.default,
      core.iter.traits.iterator.Iterator.collect.default,
      core.result.Result.Insts.CoreIterTraitsCollectFromIteratorResult]
    refine WP.spec_bind (Pₘ := fun r => ∃ v, r = .Ok v ∧
      v.val = [readingOf (secretBytes rec.state) rec.detected.val rec.container_words]) ?_ ?_
    · refine WP.spec_bind (Pₘ := fun y => y = (Array.make 1#usize [rec.container_words]).to_slice)
        (by simp [lift, WP.spec_ok]) ?_
      rintro y rfl
      refine WP.spec_bind (Pₘ := fun ii => ii =
        alloc.slice.Slice.into_vec (Array.make 1#usize [rec.container_words]).to_slice)
        ((WP.spec_ok _).mpr rfl) ?_
      rintro ii rfl
      refine WP.spec_bind (Pₘ := fun m => m = ⟨alloc.slice.Slice.into_vec
        (Array.make 1#usize [rec.container_words]).to_slice, rec⟩) ((WP.spec_ok _).mpr rfl) ?_
      rintro m rfl
      exact from_iter_result_spec _ _ _ hy (by simp; scalar_tac)
    · rintro r ⟨v, rfl, hv⟩
      simp only [WP.spec_ok]
      exact ⟨ha, hv⟩

end MhfeProofs
