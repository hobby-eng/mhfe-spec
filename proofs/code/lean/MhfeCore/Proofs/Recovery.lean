import MhfeCore.Proofs.Packing

/-!
# Recovery in the code: the suite of a container, the admission table and the length rules
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-! ## The suite a container selects -/

/-- The suite of the code that a container of `words` words selects. -/
def codeSuiteOf (words : Nat) : suite.Suite :=
  if words = 24 then .TwentyFourWords else .SameLength

theorem suiteOfContainer_code (w : Nat) (hw : w ∈ MhfeSpec.wordCounts) :
    MhfeSpec.suiteOfContainer w = some (specSuite (codeSuiteOf w)) := by
  simp [MhfeSpec.wordCounts] at hw
  rcases hw with h | h | h | h | h <;> subst h <;> decide

theorem of_container_loop_spec (words : Std.Usize) :
    ∀ (n : Nat) (k : Std.Usize), k.val + n = 4 →
      suite.Suite.of_container_loop words k ⦃ o => o =
        if words.val ∈ ([12, 15, 18, 21] : List Nat).drop k.val then some .SameLength else none ⦄ := by
  intro n
  induction n with
  | zero =>
    intro k hk
    rw [suite.Suite.of_container_loop]
    step*
    all_goals (have hk' : k.val = 4 := by omega)
    all_goals first
      | (simp [hk'])
      | (exfalso; simp_all [Slice.len, short_word_counts_val])
  | succ n ih =>
    intro k hk
    rw [suite.Suite.of_container_loop]
    have hk4 : k.val < 4 := by omega
    have hk' : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by omega
    step*
    · rcases hk' with h | h | h | h <;> simp_all [short_word_counts_val]
    · rw [o_post, short1_post]
      rcases hk' with h | h | h | h <;> simp_all [short_word_counts_val] <;> scalar_tac

/-- `Suite::of_container` selects suite 3 for 24 words and suite 4 for 12 to 21 words: the
specification's `suiteOfContainer`. -/
theorem of_container_spec (words : Std.Usize) (hw : words.val ∈ MhfeSpec.wordCounts) :
    suite.Suite.of_container words ⦃ o => o = some (codeSuiteOf words.val) ⦄ := by
  unfold suite.Suite.of_container
  let* ⟨ sw, hsw ⟩ ← state_words_spec
  have hw' : words.val = 12 ∨ words.val = 15 ∨ words.val = 18 ∨ words.val = 21 ∨
      words.val = 24 := by simpa [MhfeSpec.wordCounts] using hw
  split
  · rename_i h
    have : words.val = 24 := by rw [h, hsw]
    simp [codeSuiteOf, this]
  · rename_i h
    have h24 : words.val ≠ 24 := by intro h'; apply h; scalar_tac
    apply WP.spec_mono (of_container_loop_spec words 4 0#usize (by simp))
    intro o ho
    rw [ho]
    simp only [codeSuiteOf, h24, if_false]
    rcases hw' with h | h | h | h | h <;> simp_all

/-! ## The admission table -/

theorem contains_usize_spec (s : Slice Std.Usize) (x : Std.Usize) :
    core.slice.Slice.contains core.cmp.PartialEqUsize s x ⦃ b => b = decide (x ∈ s.val) ⦄ := by
  unfold core.slice.Slice.contains
  generalize s.val = l
  induction l with
  | nil => simp [List.anyM, pure, WP.spec_ok]
  | cons y ys ih =>
    simp only [List.anyM]
    by_cases h : x = y
    · subst h; simp [pure, WP.spec_ok]
    · simp [h]
      exact ih

theorem mem_usize (w : Std.Usize) (l : List Std.Usize) : w ∈ l ↔ w.val ∈ l.map (·.val) := by
  constructor
  · intro h; exact List.mem_map_of_mem h
  · intro h
    obtain ⟨y, hy, hyv⟩ := List.mem_map.mp h
    have : y = w := UScalar.eq_of_val_eq hyv
    subst this; exact hy

/-- `admit` accepts exactly the stated lengths that the specification's admission table admits. -/
theorem admit_spec (cw : Std.Usize) (stated : Option Std.Usize) :
    recovery.admit cw stated ⦃ r =>
      (r = .Ok () ↔ MhfeSpec.admitsLength cw.val (stated.map (·.val))) ⦄ := by
  unfold recovery.admit
  cases stated with
  | none => simp [MhfeSpec.admitsLength]
  | some w =>
    simp only [phrase.WORD_COUNTS, bind_tc_ok]
    step*
    let* ⟨ b, hb ⟩ ← contains_usize_spec
    have hsv : s.val = [12#usize, 15#usize, 18#usize, 21#usize, 24#usize] := by
      rw [s_post]; simp
    have hmem : w ∈ s.val ↔ w.val ∈ MhfeSpec.wordCounts := by
      rw [mem_usize, hsv]; simp [MhfeSpec.wordCounts]
    split
    · rename_i hbt
      have hin : w.val ∈ MhfeSpec.wordCounts := by rw [← hmem]; simpa [hbt] using hb
      let* ⟨ sw, hsw ⟩ ← state_words_spec
      simp only [MhfeSpec.admitsLength, Option.map_some, hin, true_and]
      split
      · rename_i hne
        have hne' : cw.val ≠ 24 := by intro h; simp [bne_iff_ne] at hne; apply hne; scalar_tac
        split
        · rename_i hne2
          have : w.val ≠ cw.val := by intro h; simp [bne_iff_ne] at hne2; apply hne2; scalar_tac
          simp [hne', this]
        · rename_i heq
          have : w.val = cw.val := by simp [bne_iff_ne] at heq; rw [heq]
          simp [this]
      · rename_i heq
        have : cw.val = 24 := by simp [bne_iff_ne] at heq; rw [heq, hsw]
        simp [this]
    · rename_i hbf
      have hnin : w.val ∉ MhfeSpec.wordCounts := by rw [← hmem]; simpa [hbf] using hb
      simp [MhfeSpec.admitsLength, hnin]

/-! ## The length rules -/

/-- `lengths` (translated by hand, `Assumptions/Translations.lean`) gives the lengths of the
readings by the specification's `lengthRules`, and `VerifierMismatch` where the rules give no
reading. -/
theorem lengths_spec (stated : Option Std.Usize) (d : Slice Std.Usize)
    (hd : d.val.length ≤ 4) :
    recovery.lengths stated d ⦃ r => match r with
      | .Ok v => MhfeSpec.lengthRules (stated.map (·.val)) (d.val.map (·.val)) =
          some (v.val.map (·.val))
      | .Err e => MhfeSpec.lengthRules (stated.map (·.val)) (d.val.map (·.val)) = none ∧
          e = .VerifierMismatch ⦄ := by
  unfold recovery.lengths
  let* ⟨ sw, hsw ⟩ ← state_words_spec
  have hsw' : sw = 24#usize := UScalar.eq_of_val_eq (by rw [hsw]; rfl)
  subst hsw'
  have hmemd : ∀ w : Std.Usize, w ∈ d.val ↔ w.val ∈ d.val.map (·.val) := fun w => mem_usize w d.val
  generalize hdl : d.val = dl at *
  have h24 : ∀ w : Std.Usize, w = 24#usize ↔ w.val = 24 :=
    fun w => ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq (by rw [h]; rfl)⟩
  cases stated with
  | none =>
    rcases dl with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp [MhfeSpec.lengthRules, MhfeSpec.readingsWithoutLength]
    · simp [MhfeSpec.lengthRules, MhfeSpec.readingsWithoutLength]
    · simp at hd
      simp only [MhfeSpec.lengthRules, MhfeSpec.readingsWithoutLength, Option.map_none]
      rw [dif_pos (by simp; scalar_tac)]
      simp
  | some w =>
    by_cases hw : w ∈ dl
    · simp [hw, MhfeSpec.lengthRules, (hmemd w).mp hw]
    · have hw' : w.val ∉ dl.map (·.val) := fun h => hw ((hmemd w).mpr h)
      clear hmemd
      simp only [Option.map_some, MhfeSpec.lengthRules, hw', if_false, hw, ite_false]
      rcases dl with _ | ⟨a, _ | ⟨b, t⟩⟩
      · by_cases h : w.val = 24
        · simp [(h24 w).mpr h, h]
        · have : w ≠ 24#usize := fun e => h ((h24 w).mp e)
          simp [this, h]
      · by_cases h : w.val = 24
        · have : w = 24#usize := (h24 w).mpr h
          simp only [this, ne_eq, not_true_eq_false, if_false, h, if_true]
          rw [dif_pos (by simp; scalar_tac)]
          simp
        · have : w ≠ 24#usize := fun e => h ((h24 w).mp e)
          simp [this, h, MhfeSpec.readingsWithoutLength]
      · simp at hd
        rw [dif_pos (by simp; scalar_tac)]
        by_cases h : w.val = 24
        · simp [h]
        · simp [h, MhfeSpec.readingsWithoutLength]

/-! ## The recovered state -/

theorem secretBytes_length (s : protect.Secret) (hs : SecretLe s) :
    (secretBytes s).length = s.len.val := by
  simp [secretBytes, SecretLe] at *; omega

theorem SecretOk.le {s : protect.Secret} (hs : SecretOk s) : SecretLe s := by
  simp [SecretOk, SecretLe] at *; omega

theorem secret_as_bytes_le_spec (s : protect.Secret) (hs : SecretLe s) :
    protect.Secret.as_bytes s ⦃ b => b.val = secretBytes s ⦄ := by
  unfold protect.Secret.as_bytes
  simp only [os.Pages.as_slice, bind_tc_ok]
  simp only [SecretLe] at hs
  step*
  all_goals simp_all [secretBytes, List.slice, Slice.length]

/-- `Recovery::new` for suite 3 keeps the 32-byte state and the lengths detected in it. -/
theorem recovery_new_3 (st : protect.Secret) (hok : SecretLe st)
    (hlen : st.len.val = MhfeSpec.stateBytes) :
    recovery.Recovery.new .TwentyFourWords st ⦃ rec =>
      rec.suite = .TwentyFourWords ∧ rec.container_words.val = 24 ∧ rec.state = st ∧
      rec.detected.val.map (·.val) = MhfeSpec.detected shaF (secretBytes st) ∧
      rec.detected.val.length ≤ 4 ⦄ := by
  unfold recovery.Recovery.new
  let* ⟨ s, hs ⟩ ← secret_as_bytes_le_spec
  let* ⟨ d, hd1, hd2 ⟩ ← detected_lengths_spec
  · rw [hs, secretBytes_length st hok, hlen]
  let* ⟨ sw, hsw ⟩ ← state_words_spec
  rw [hs] at hd1
  exact ⟨hsw, hd1, hd2⟩

/-- `Recovery::new` for suite 4 keeps the state, whose length gives the container's word count,
and detects no length. -/
theorem recovery_new_4 (st : protect.Secret) (hok : SecretLe st) (w : Nat)
    (hw : w ∈ MhfeSpec.wordCounts) (hlen : st.len.val = MhfeSpec.entropyBytes w) :
    recovery.Recovery.new .SameLength st ⦃ rec =>
      rec.suite = .SameLength ∧ rec.container_words.val = w ∧ rec.state = st ∧
      rec.detected.val = [] ⦄ := by
  unfold recovery.Recovery.new
  have hE := entropyBytes_le w hw
  let* ⟨ s, hs ⟩ ← secret_as_bytes_le_spec
  have hsl : s.len.val = MhfeSpec.entropyBytes w := by
    simp [Slice.len]; rw [hs, secretBytes_length st hok, hlen]
  let* ⟨ cw, hcw ⟩ ← words_of_entropy_spec
  rw [hcw, hsl]
  simp [MhfeSpec.wordCounts] at hw
  rcases hw with h | h | h | h | h <;> subst h <;> decide

end MhfeProofs
