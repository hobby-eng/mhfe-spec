import MhfeCore.Proofs.Cipher

/-!
# Recovering a created container gives back the encrypted state

`encrypt_spec` says what a created container holds; `decrypt_spec` says which state `decrypt`
recovers from a container. The theorems below join them: the suite that the container's length
selects is the suite it was created under, and the recovered state is the state that creation
encrypted (the packed original in suite 3, the original's entropy in suite 4).
-/

open Aeneas Aeneas.Std RustM mhfe_core MhfeModelLink

namespace MhfeProofs

/-- The forward rounds keep both halves at `h` bytes. -/
theorem forwardRounds_length (m : Nat → MhfeSpec.Bytes → MhfeSpec.Bytes) (h : Nat)
    (hm : ∀ i r, (m i r).length = h) :
    ∀ (n : Nat) (st : MhfeSpec.Bytes × MhfeSpec.Bytes), st.1.length = h → st.2.length = h →
      (MhfeSpec.forwardRounds m n st).1.length = h ∧ (MhfeSpec.forwardRounds m n st).2.length = h := by
  intro n
  induction n with
  | zero => intro st h1 h2; exact ⟨h1, h2⟩
  | succ n ih =>
    intro st h1 h2
    obtain ⟨a, b⟩ := ih st h1 h2
    constructor
    · simp only [MhfeSpec.forwardRounds, MhfeSpec.forwardRound]; exact b
    · simp only [MhfeSpec.forwardRounds, MhfeSpec.forwardRound, MhfeSpec.xorBytes,
        List.length_zipWith, hm, a, Nat.min_self]

/-- `Perm` keeps the length of a state of two halves. -/
theorem perm_length (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize)
    (c : MhfeSpec.Setting) (hh : c.half ≤ 32) (x : MhfeSpec.Bytes) (hx : x.length = 2 * c.half) :
    (MhfeSpec.perm (modelPrims A) c x).length = 2 * c.half := by
  have hm : ∀ i r, (MhfeSpec.roundMask (modelPrims A) c i r).length = c.half :=
    fun i r => roundMask_length _ c (modelPrims_wellFormed A) hh i r
  obtain ⟨a, b⟩ := forwardRounds_length _ c.half hm MhfeSpec.rounds (x.take c.half, x.drop c.half)
    (by simp; omega) (by simp; omega)
  simp only [MhfeSpec.perm, List.length_append, a, b]; omega

/-- In suite 3 the permutation does not depend on the phrase length of the setting. -/
theorem permInv_three_words (F : MhfeSpec.Primitives) (w1 w2 pim mem : Nat) (pw : MhfeSpec.Bytes) :
    MhfeSpec.permInv F ⟨.three, w1, pim, mem, pw⟩ = MhfeSpec.permInv F ⟨.three, w2, pim, mem, pw⟩ := by
  have hm : MhfeSpec.roundMask F ⟨.three, w1, pim, mem, pw⟩ =
      MhfeSpec.roundMask F ⟨.three, w2, pim, mem, pw⟩ := by
    funext i r
    simp [MhfeSpec.roundMask, MhfeSpec.Setting.half, MhfeSpec.Suite.halfBytes, MhfeSpec.Suite.ent]
  funext y
  simp only [MhfeSpec.permInv, hm, MhfeSpec.Setting.half, MhfeSpec.Suite.halfBytes]

/-- A container that `encrypt` created selects, by its length, the suite it was created under, and
`Perm^-1` of its entropy under that selection is the state that creation encrypted. With
`decrypt_spec`, the state that `decrypt` recovers from the container is that state. -/
theorem created_container_recovers (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize)
    (su : suite.Suite) (original : phrase.Phrase) (hp : PhraseOk original)
    (hsu : su = .SameLength → original.wordCount.val ≠ 24) (work : suite.WorkFactor)
    (pw : password.Password) (container : phrase.Phrase)
    (hc : CreationOk A (settingOf su original.wordCount.val work pw)
      (createState su original.entropyBytes.val) container) :
    codeSuiteOf container.wordCount.val = su ∧
    MhfeSpec.permInv (modelPrims A)
        (settingOf (codeSuiteOf container.wordCount.val) container.wordCount.val work pw)
        container.entropyBytes.val = createState su original.entropyBytes.val := by
  obtain ⟨hY, _, hinv, hwc⟩ := hc
  have hp1 := hp.1
  cases su with
  | TwentyFourWords =>
    have hX : (createState .TwentyFourWords original.entropyBytes.val).length = 32 := by
      have hE := entropyBytes_le _ hp1
      have hl := hp.2
      simp only [createState, MhfeSpec.pack]
      split_ifs with hlt
      · simp only [List.length_append, List.length_take, shaF_length, MhfeSpec.stateBytes] at *
        omega
      · simp only [MhfeSpec.stateBytes] at hlt; omega
    have hlen : container.entropyBytes.val.length = 32 := by
      rw [hY, perm_length A _ (by simp [settingOf, MhfeSpec.Setting.half, specSuite,
        MhfeSpec.Suite.halfBytes]) _ (by rw [hX]; rfl)]
      rfl
    have h24 : container.wordCount.val = 24 := by rw [hwc, hlen]
    have hcs : codeSuiteOf container.wordCount.val = .TwentyFourWords := by simp [codeSuiteOf, h24]
    refine ⟨hcs, ?_⟩
    rw [hcs]
    simp only [settingOf, specSuite] at hinv ⊢
    rw [permInv_three_words _ _ original.wordCount.val]
    exact hinv
  | SameLength =>
    have h24 := hsu rfl
    have hE := entropyBytes_le _ hp1
    have hhalf : (settingOf .SameLength original.wordCount.val work pw).half * 2 =
        MhfeSpec.entropyBytes original.wordCount.val := by
      simp only [settingOf, MhfeSpec.Setting.half]
      rw [Nat.mul_comm, half_twice _ _ hp1 (by simp [codeSuiteOf, h24])]
    have hlen : container.entropyBytes.val.length = MhfeSpec.entropyBytes original.wordCount.val := by
      rw [hY, perm_length A _ (by omega) _ (by simp only [createState]; rw [hp.2]; omega)]
      omega
    have hw : container.wordCount.val = original.wordCount.val := by
      rw [hwc, hlen]
      simp [MhfeSpec.wordCounts] at hp1
      rcases hp1 with h | h | h | h | h <;> rw [h] <;> decide
    have hcs : codeSuiteOf container.wordCount.val = .SameLength := by
      simp [codeSuiteOf, hw, h24]
    refine ⟨hcs, ?_⟩
    rw [hcs, hw]
    exact hinv

end MhfeProofs
