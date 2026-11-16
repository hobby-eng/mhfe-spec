import MhfeCore.Proofs.Readings
import MhfeCore.Proofs.ModelCode

/-!
# Creating a container and recovering its state

`Mhfe::decrypt` checks the suite and the stated length before any Argon2id work and recovers
`Perm^-1` of the container's entropy; `Mhfe::encrypt` gives a container whose entropy is `Perm`
of the packed original, after the creation check.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- The callback of a host: it always returns, with any decision. -/
def HostCallbackTotal {T1 A : Type}
    (fnInst : core.ops.function.FnMut T1 A (core.ops.control_flow.ControlFlow Unit Unit)) : Prop :=
  ∀ s a, ∃ v, fnInst.call_mut s a = ok v

/-- A phrase as the code holds one: a phrase length and its entropy. -/
def PhraseOk (p : phrase.Phrase) : Prop :=
  p.wordCount.val ∈ MhfeSpec.wordCounts ∧
    p.entropyBytes.val.length = MhfeSpec.entropyBytes p.wordCount.val

theorem suite_ne_spec (a b : suite.Suite) :
    core.cmp.PartialEq.ne.trait_default suite.Suite.Insts.CoreCmpPartialEqSuite a b ⦃ r =>
      (r = true ↔ a ≠ b) ⦄ := by
  cases a <;> cases b <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      suite.Suite.Insts.CoreCmpPartialEqSuite.eq, suite.Suite.read_discriminant]

theorem suite_is_some_and_spec {E T1 : Type} (inst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit)) (o : Option suite.Suite) (sel : suite.Suite) :
    core.option.Option.is_some_and
      (cipher.Mhfe.decrypt.closure.closure.Insts.CoreOpsFunctionFnOnceTupleSuiteBool inst fnInst)
      o sel ⦃ r => (r = true ↔ ∃ s, o = some s ∧ s ≠ sel) ⦄ := by
  cases o with
  | none => simp [core.option.Option.is_some_and]
  | some s =>
    simp only [core.option.Option.is_some_and,
      cipher.Mhfe.decrypt.closure.closure.Insts.CoreOpsFunctionFnOnceTupleSuiteBool,
      cipher.Mhfe.decrypt.closure.closure.Insts.CoreOpsFunctionFnOnceTupleSuiteBool.call_once]
    apply WP.spec_mono (suite_ne_spec s sel)
    intro r hr; rw [hr]; simp

attribute [local step] of_container_spec suite_is_some_and_spec core.option.Option.expect.spec

/-- With a suite that the container's length does not select, `decrypt` refuses the container
before any Argon2id work: the theorem holds for every engine, also one whose calls never return. -/
theorem decrypt_suite_not_admitted {E T1 : Type} (inst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit))
    (self : cipher.Mhfe E) (container : phrase.Phrase)
    (hp : container.wordCount.val ∈ MhfeSpec.wordCounts) (pw : password.Password)
    (stated : Option Std.Usize) (s : suite.Suite) (hs : s ≠ codeSuiteOf container.wordCount.val)
    (cb : T1) :
    cipher.Mhfe.decrypt inst fnInst self container pw stated (some s) cb ⦃ r _ _ =>
      r = .Err (.SuiteNotAdmitted container.wordCount) ⦄ := by
  unfold cipher.Mhfe.decrypt stack.cleared stack.run
  simp only [stack.overwrite]
  unfold cipher.Mhfe.decrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTupleRecoveryError.call_once
  simp only [phrase.Phrase.words]
  step*
  have hx : x = true := by simp_all
  rw [if_pos hx]
  step*
  show ok (_, self, cb) ⦃ _ ⦄
  simp

/-- With an admitted suite and a stated length that the admission table does not admit, `decrypt`
refuses the container before any Argon2id work, for every engine. -/
theorem decrypt_length_not_admitted {E T1 : Type} (inst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit))
    (self : cipher.Mhfe E) (container : phrase.Phrase)
    (hp : container.wordCount.val ∈ MhfeSpec.wordCounts) (pw : password.Password)
    (stated : Option Std.Usize) (su : Option suite.Suite)
    (hsu : ∀ s, su = some s → s = codeSuiteOf container.wordCount.val)
    (hna : ¬ MhfeSpec.admitsLength container.wordCount.val (stated.map (·.val))) (cb : T1) :
    cipher.Mhfe.decrypt inst fnInst self container pw stated su cb ⦃ r _ _ => ∃ e, r = .Err e ⦄ := by
  unfold cipher.Mhfe.decrypt stack.cleared stack.run
  simp only [stack.overwrite]
  unfold cipher.Mhfe.decrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTupleRecoveryError.call_once
  simp only [phrase.Phrase.words]
  step*
  have hx : x = false := by
    cases su with
    | none => simp_all
    | some s => have := hsu s rfl; simp_all
  rw [if_neg (by simp [hx])]
  let* ⟨ r, hr ⟩ ← admit_spec
  cases r with
  | Ok u => exact absurd (hr.mp rfl) hna
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.«from»]
    step*
    show ok (_, self, cb) ⦃ _ ⦄
    simp

/-- The callback that `decrypt` gives to `inverse` returns whenever the host's callback does. -/
theorem decrypt_callback_total {E T1 : Type} (inst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit)) (h : HostCallbackTotal fnInst) :
    CallbackTotal
      (cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
        inst fnInst) := by
  intro s i _
  obtain ⟨⟨cf, t⟩, hv⟩ := h s (i, suite.ROUNDS)
  refine ⟨(cf, t), ?_⟩
  simp [cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut, hv]

/-- What a recovery of a container of `w` words under the code's suite `su` holds: the state, of the
right length, and for suite 3 the detected lengths, as `readings_spec_3` and `readings_spec_4` need
them. -/
def RecoveryOk (rec : recovery.Recovery) (su : suite.Suite) (w : Nat) : Prop :=
  rec.suite = su ∧ SecretLe rec.state ∧
  (su = .TwentyFourWords → rec.container_words.val = 24 ∧
    rec.state.len.val = MhfeSpec.stateBytes ∧
    rec.detected.val.map (·.val) = MhfeSpec.detected shaF (secretBytes rec.state) ∧
    rec.detected.val.length ≤ 4) ∧
  (su = .SameLength → rec.container_words.val = w ∧
    rec.state.len.val = MhfeSpec.entropyBytes w ∧ rec.detected.val = [])

theorem entropy_secret_spec (p : phrase.Phrase) (hp : PhraseOk p) :
    phrase.Phrase.entropy p ⦃ s => SecretOk s ∧ secretBytes s = p.entropyBytes.val ⦄ := by
  have hE := entropyBytes_le _ hp.1
  have hl := hp.2
  simp only [phrase.Phrase.entropy, WP.spec_ok, SecretOk, secretBytes]
  have : (⟨BitVec.ofNat _ p.entropyBytes.val.length⟩ : Std.Usize).val = p.entropyBytes.val.length := by
    simp only [UScalar.val, BitVec.toNat_ofNat]
    rcases System.Platform.numBits_eq with hb | hb <;> simp [UScalarTy.numBits, hb] <;> omega
  simp only [Slice.length] at *
  constructor
  · exact this.symm
  · rw [this, List.take_length]

theorem half_twice (su : suite.Suite) (w : Nat) (hw : w ∈ MhfeSpec.wordCounts)
    (hsu : su = codeSuiteOf w) :
    2 * (specSuite su).halfBytes w = MhfeSpec.entropyBytes w := by
  subst hsu
  simp [MhfeSpec.wordCounts] at hw
  rcases hw with h | h | h | h | h <;> subst h <;> decide

/-- `decrypt` recovers `Perm^-1` of the container's entropy under the suite that the container's
length selects; the recovery it returns holds that state. -/
theorem decrypt_spec {E T1 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (fnInst : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit)) (hcb : HostCallbackTotal fnInst)
    (self : cipher.Mhfe E) (hwork : WorkOk self.work) (container : phrase.Phrase)
    (hp : PhraseOk container) (pw : password.Password) (hpw : SecretOk pw.encoded)
    (stated : Option Std.Usize) (su : Option suite.Suite) (cb : T1) :
    cipher.Mhfe.decrypt inst fnInst self container pw stated su cb ⦃ r _ _ =>
      ∀ rec, r = .Ok (.Continue rec) →
        RecoveryOk rec (codeSuiteOf container.wordCount.val) container.wordCount.val ∧
        secretBytes rec.state = MhfeSpec.permInv (modelPrims A)
          (settingOf (codeSuiteOf container.wordCount.val) container.wordCount.val self.work pw)
          container.entropyBytes.val ⦄ := by
  have hp1 := hp.1
  unfold cipher.Mhfe.decrypt stack.cleared stack.run
  simp only [stack.overwrite]
  unfold cipher.Mhfe.decrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTupleRecoveryError.call_once
  simp only [phrase.Phrase.words]
  step*
  subst_vars
  simp only [Option.some.injEq] at *
  subst_vars
  by_cases hx : x = true
  · rw [if_pos hx]
    step*
    show ok (_, self, cb) ⦃ _ ⦄
    simp
  · rw [if_neg hx]
    let* ⟨ r, hr ⟩ ← admit_spec
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.«from»]
      step*
      show ok (_, self, cb) ⦃ _ ⦄
      simp
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch]
      step*
      have hpm := permutation_spec inst self pw (codeSuiteOf container.wordCount.val)
        container.wordCount hp1 hwork hpw
      let* ⟨ pp, hm, hpe ⟩ ← hpm
      obtain ⟨p2, pback⟩ := pp
      simp only at hm hpe
      have hes := entropy_secret_spec container hp
      step*
      have hab := secret_as_bytes_spec x x_post
      let* ⟨ s1, hs1 ⟩ ← hab
      have hy : s1.val.length = 2 * (settingOf (codeSuiteOf container.wordCount.val)
          container.wordCount.val self.work pw).half := by
        rw [hs1, x_post1, hp.2]; simp only [settingOf, MhfeSpec.Setting.half]
        rw [half_twice _ _ hp1 rfl]
      have hinv := inverse_spec inst A hA _ (decrypt_callback_total inst fnInst hcb) p2 _ hm s1 hy cb
      let* ⟨ rr, e3, he3, hpost ⟩ ← hinv
      obtain ⟨res, p3, ib, c1, ib1⟩ := rr
      simp only at he3 hpost
      cases res with
      | Err err =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.«from»]
        step*
        show ok (_, _, _) ⦃ _ ⦄
        simp
      | Ok cf =>
        cases cf with
        | Break u =>
          simp only [core.ops.control_flow.ControlFlow.map_continue]
          step*
          show ok (_, _, _) ⦃ _ ⦄
          simp
        | Continue st =>
          obtain ⟨hst, hlen, hle, hz⟩ := hpost st rfl
          simp only [core.ops.control_flow.ControlFlow.map_continue,
            cipher.Mhfe.decrypt.closure.closure_2.Insts.CoreOpsFunctionFnOnceTupleSecretRecovery,
            cipher.Mhfe.decrypt.closure.closure_2.Insts.CoreOpsFunctionFnOnceTupleSecretRecovery.call_once]
          have hst' : secretBytes st = MhfeSpec.permInv (modelPrims A)
              (settingOf (codeSuiteOf container.wordCount.val) container.wordCount.val self.work pw)
              container.entropyBytes.val := by rw [hst, hs1, x_post1]
          have hlen' : st.len.val = MhfeSpec.entropyBytes container.wordCount.val := by
            rw [hlen]; simp only [settingOf, MhfeSpec.Setting.half]; exact half_twice _ _ hp1 rfl
          have hnew : recovery.Recovery.new (codeSuiteOf container.wordCount.val) st ⦃ rec =>
              RecoveryOk rec (codeSuiteOf container.wordCount.val) container.wordCount.val ∧
              rec.state = st ⦄ := by
            by_cases h24 : container.wordCount.val = 24
            · have hcs : codeSuiteOf container.wordCount.val = .TwentyFourWords := by
                simp [codeSuiteOf, h24]
              rw [hcs]
              apply WP.spec_mono (recovery_new_3 st hle (by rw [hlen', h24]; rfl))
              rintro rec ⟨h1, h2, h3, h4, h5⟩
              subst h3
              exact ⟨⟨h1, hle, fun _ => ⟨h2, by rw [hlen', h24]; rfl, h4, h5⟩,
                fun h => by simp at h⟩, rfl⟩
            · have hcs : codeSuiteOf container.wordCount.val = .SameLength := by
                simp [codeSuiteOf, h24]
              rw [hcs]
              apply WP.spec_mono (recovery_new_4 st hle _ hp1 hlen')
              rintro rec ⟨h1, h2, h3, h4⟩
              subst h3
              exact ⟨⟨h1, hle, fun h => by simp at h, fun _ => ⟨h2, hlen', h4⟩⟩, rfl⟩
          step*
          show ok (_, _, _) ⦃ _ ⦄
          simp only [WP.spec_ok]
          intro rec hrec
          simp only [core.result.Result.Ok.injEq,
            core.ops.control_flow.ControlFlow.Continue.injEq] at hrec
          subst hrec
          exact ⟨x_post, by rw [st_post]; exact hst'⟩

/-! ## Creation -/

/-- The state that creation encrypts: the packed original in suite 3, its entropy in suite 4. -/
noncomputable def createState (su : suite.Suite) (e : List Std.U8) : List Std.U8 :=
  match su with
  | .TwentyFourWords => MhfeSpec.pack shaF e
  | .SameLength => e

theorem encode_spec (y : Slice Std.U8) (hy : y.length ∈ ([16, 20, 24, 28, 32] : List Nat)) :
    phrase.Phrase.encode y ⦃ r =>
      r = .Ok ⟨⟨BitVec.ofNat _ (y.length / 4 * 3)⟩, y⟩ ⦄ := by
  unfold phrase.Phrase.encode
  rw [if_pos hy]
  simp

theorem usize_ofNat_val (n : Nat) (h : n < 2 ^ 32) :
    (⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
  simp only [UScalar.val, BitVec.toNat_ofNat]
  rcases System.Platform.numBits_eq with hb | hb <;> simp [UScalarTy.numBits, hb] <;> omega

theorem u8_ofNat_val (n : Nat) : (⟨BitVec.ofNat 8 n⟩ : Std.U8).val = n % 256 := by
  simp [UScalar.val]

theorem as_str_spec (p : phrase.Phrase) (hl : p.entropyBytes.val.length ≤ 32) :
    phrase.Phrase.as_str p ⦃ t => t.val = MhfeModel.phraseText p ⦄ := by
  have h : (MhfeModel.phraseText p).length ≤ Usize.max := by
    simp [MhfeModel.phraseText]; scalar_tac
  unfold phrase.Phrase.as_str
  rw [dif_pos h]
  exact (WP.spec_ok _).mpr (Slice.from_val _ _)

/-- The text of a phrase reads back as the phrase (the model of `Phrase::read_text` on the text
that `Phrase::as_str` gives). -/
theorem read_text_spec (p : phrase.Phrase) (hw : p.wordCount.val < 65536)
    (hl : p.entropyBytes.val.length ≤ 32) (t : Str) (ht : t.val = MhfeModel.phraseText p) :
    phrase.Phrase.read_text t ⦃ r => r = .Ok p ⦄ := by
  unfold phrase.Phrase.read_text
  rw [ht]
  simp only [MhfeModel.phraseText, List.cons_append, List.nil_append]
  have hr : p.entropyBytes.val.length ≤ Usize.max := by scalar_tac
  rw [dif_pos hr]
  simp only [WP.spec_ok, core.result.Result.Ok.injEq]
  cases p with
  | mk wc eb =>
    simp only [phrase.Phrase.mk.injEq]
    refine ⟨?_, Slice.ext _ _ (by simp)⟩
    apply UScalar.eq_of_val_eq
    have e1 := u8_ofNat_val (wc.val / 256)
    have e2 := u8_ofNat_val wc.val
    rw [usize_ofNat_val _ (by rw [e1, e2]; omega), e1, e2]
    simp only at hw ⊢
    omega

/-- In suite 4, `encrypt` refuses a 24-word original before any Argon2id work, for every engine and
every callback. -/
theorem encrypt_same_length_needs_short {E T1 T2 : Type} (inst : engine.Argon2Engine E)
    (fn1 : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit))
    (fn2 : core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow Unit Unit))
    (self : cipher.Mhfe E) (original : phrase.Phrase) (h24 : original.wordCount.val = 24)
    (pw : password.Password) (cb1 : T1) (cb2 : T2) :
    cipher.Mhfe.encrypt inst fn1 fn2 self original pw .SameLength cb1 cb2 ⦃ r _ _ _ =>
      r = .Err .SameLengthNeedsShortPhrase ⦄ := by
  unfold cipher.Mhfe.encrypt stack.cleared stack.run
  simp only [stack.overwrite]
  unfold cipher.Mhfe.encrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTuplePhraseError.call_once
  simp only [phrase.Phrase.words, suite.Suite.Insts.CoreCmpPartialEqSuite.eq,
    suite.Suite.read_discriminant]
  have hsw := state_words_spec
  step*
  simp only [decide_true, ↓reduceIte]
  step*
  rw [if_pos (UScalar.eq_of_val_eq (by simp_all))]
  step*
  show ok _ ⦃ _ ⦄
  simp

theorem u32_add_ok (a b : Std.U32) (h : a.val + b.val ≤ 24) :
    ∃ v, (a + b : RustM Std.U32) = ok v ∧ v.val = a.val + b.val := by
  simp only [HAdd.hAdd, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
  rw [dif_pos (by simp only [UScalar.check_bounds, UScalarTy.numBits, decide_eq_true_eq]
                  show a.val + b.val < _; simp; omega)]
  refine ⟨_, rfl, ?_⟩
  simp only [UScalar.ofNatCore_val_eq]

theorem rounds_twice : (2#u32 * suite.ROUNDS : RustM Std.U32) = ok 24#u32 := by
  simp only [suite.ROUNDS]; rfl

theorem encrypt_forward_callback_total {E T1 T2 : Type} (inst : engine.Argon2Engine E)
    (fn1 : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit))
    (fn2 : core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow Unit Unit))
    (h : HostCallbackTotal fn1) :
    CallbackTotal
      (cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
        inst fn1 fn2) := by
  intro s i _
  obtain ⟨⟨cf, t⟩, hv⟩ := h s (i, 24#u32)
  refine ⟨(cf, t), ?_⟩
  simp [cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut,
    rounds_twice, hv]

theorem encrypt_inverse_callback_total {E T1 T2 : Type} (inst : engine.Argon2Engine E)
    (fn1 : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit))
    (fn2 : core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow Unit Unit))
    (h : HostCallbackTotal fn1) :
    CallbackTotal
      (cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
        inst fn1 fn2) := by
  intro s i hi
  obtain ⟨v, hv1, hv2⟩ := u32_add_ok suite.ROUNDS i (by simp [suite.ROUNDS, MhfeSpec.rounds] at hi ⊢; omega)
  obtain ⟨⟨cf, t⟩, hc⟩ := h s (v, 24#u32)
  refine ⟨(cf, t), ?_⟩
  simp [cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut,
    rounds_twice, hv1, hc]

attribute [local step] slice_eq_u8_spec

/-- The postcondition of a creation: the container's entropy is `Perm` of the state that creation
encrypts, differs from it (no fixed point), and the inverse permutation gives the state back (the
creation check); the container has three words for every four bytes of entropy. -/
def CreationOk (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize)
    (c : MhfeSpec.Setting) (x : List Std.U8) (container : phrase.Phrase) : Prop :=
  container.entropyBytes.val = MhfeSpec.perm (modelPrims A) c x ∧
  container.entropyBytes.val ≠ x ∧
  MhfeSpec.permInv (modelPrims A) c container.entropyBytes.val = x ∧
  container.wordCount.val = container.entropyBytes.val.length / 4 * 3

set_option maxHeartbeats 4000000 in
theorem encrypt_spec {E T1 T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (fn1 : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit)) (hcb1 : HostCallbackTotal fn1)
    (fn2 : core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb2 : HostCallbackTotal fn2)
    (self : cipher.Mhfe E) (hwork : WorkOk self.work) (original : phrase.Phrase)
    (hp : PhraseOk original) (pw : password.Password) (hpw : SecretOk pw.encoded)
    (su : suite.Suite) (cb1 : T1) (cb2 : T2) :
    cipher.Mhfe.encrypt inst fn1 fn2 self original pw su cb1 cb2 ⦃ r _ _ _ =>
      ∀ container, r = .Ok (.Continue container) →
        CreationOk A (settingOf su original.wordCount.val self.work pw)
          (createState su original.entropyBytes.val) container ⦄ := by
  have hp1 := hp.1
  have hE := entropyBytes_le _ hp1
  unfold cipher.Mhfe.encrypt stack.cleared stack.run
  simp only [stack.overwrite]
  unfold cipher.Mhfe.encrypt.closure.Insts.CoreOpsFunctionFnOnceTupleResultControlFlowTuplePhraseError.call_once
  simp only [phrase.Phrase.words, suite.Suite.Insts.CoreCmpPartialEqSuite.eq,
    suite.Suite.read_discriminant]
  have hes := entropy_secret_spec original hp
  cases su with
  | TwentyFourWords =>
    step*
    rw [if_neg (by simp)]
    let* ⟨ ent, hent1, hent2 ⟩ ← hes
    have hab0 := secret_as_bytes_spec ent hent1
    let* ⟨ eb, heb ⟩ ← hab0
    have hebl : eb.val.length ≤ 32 := by rw [heb, hent2, hp.2]; exact hE.2
    let* ⟨ xs, hx1, hx2, hx3 ⟩ ← pack_spec
    have hpm := permutation_spec inst self pw .TwentyFourWords original.wordCount hp1 hwork hpw
    let* ⟨ pp, hm, hpe, hpb ⟩ ← hpm
    obtain ⟨p2, pback⟩ := pp
    simp only at hm hpe hpb
    have hab1 := secret_as_bytes_spec xs hx1
    step*
    rename' x => s1, x_post => hs1
    have hxl : s1.val.length = 2 * (settingOf .TwentyFourWords original.wordCount.val self.work pw).half := by
      rw [hs1, secretBytes_length _ hx1.le, hx2]; rfl
    have hfw := forward_spec inst A hA _ (encrypt_forward_callback_total inst fn1 fn2 hcb1) p2 _ hm
      s1 hxl cb1
    let* ⟨ rr, e3, he3, hpost ⟩ ← hfw
    obtain ⟨res, p3, fb, c1, fb1⟩ := rr
    simp only at he3 hpost
    cases res with
    | Err err =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.«from»]
      step*
      subst x_post
      step*
      show ok _ ⦃ _ ⦄
      simp
    | Ok cf =>
      cases cf with
      | Break u =>
        step*
        subst x_post
        step*
        show ok _ ⦃ _ ⦄
        simp
      | Continue y =>
        obtain ⟨hy, hylen, hyle, hyz⟩ := hpost y rfl
        have hab2 := secret_as_bytes_le_spec y hyle
        step*
        subst x_post
        let* ⟨ s2, hs2 ⟩ ← hab2
        have hs2l : s2.length = 32 := by
          simp only [Slice.length]; rw [hs2, secretBytes_length _ hyle, hylen]; rfl
        simp only [cipher.reject_fixed_point]
        have henc := encode_spec s2 (by rw [hs2l]; decide)
        step*
        by_cases hfx : x = true
        · rw [if_pos hfx]
          simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.«from»]
          step*
          show ok _ ⦃ _ ⦄
          simp
        · rw [if_neg hfx]
          have hne := fun h => hfx (x_post.mpr h)
          simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
          step*
          subst x_post
          simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
          obtain ⟨⟨cf3, t2⟩, hv2⟩ :=
            hcb2 cb2 ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩
          have hcall : fn2.call_mut cb2 ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩ ⦃ q =>
              q = (cf3, t2) ⦄ := by rw [hv2]; exact (WP.spec_ok _).mpr rfl
          cases cf3 with
          | Break u =>
            have hib : core.ops.control_flow.ControlFlow.is_break
                (core.ops.control_flow.ControlFlow.Break u : core.ops.control_flow.ControlFlow Unit Unit)
                ⦃ b => b = true ⦄ := by simp [core.ops.control_flow.ControlFlow.is_break]
            step*
            subst x_post
            step*
            rw [if_pos x_post]
            step*
            show ok _ ⦃ _ ⦄
            simp
          | Continue u =>
            have hib : core.ops.control_flow.ControlFlow.is_break
                (core.ops.control_flow.ControlFlow.Continue u : core.ops.control_flow.ControlFlow Unit Unit)
                ⦃ b => b = false ⦄ := by simp [core.ops.control_flow.ControlFlow.is_break]
            step*
            subst x_post
            step*
            rw [if_neg (by simp [x_post])]
            set P : phrase.Phrase := ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩ with hP
            have hPw : P.wordCount.val = 24 := by
              rw [hP]; simp only; rw [usize_ofNat_val _ (by rw [hs2l]; norm_num), hs2l]
            have hPl : P.entropyBytes.val.length = 32 := by rw [hP]; simpa [Slice.length] using hs2l
            have has := as_str_spec P (by omega)
            have hrt := read_text_spec P (by omega) (by omega)
            have hrok : core.result.Result.ok (core.result.Result.Ok P : core.result.Result
                phrase.Phrase error.Error) ⦃ o => o = some P ⦄ := by simp [core.result.Result.ok]
            have hfil : core.option.Option.filter
                (cipher.Mhfe.encrypt.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared1PhraseBool
                  inst fn1 fn2) (some P) P ⦃ o => o = some P ⦄ := by
              simp [core.option.Option.filter,
                cipher.Mhfe.encrypt.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared1PhraseBool.call_once,
                phrase.Phrase.words]
            have hokor : core.option.Option.ok_or (some P) error.Error.CreationCheckFailed ⦃ r =>
                r = .Ok P ⦄ := by simp [core.option.Option.ok_or]
            have hPok : PhraseOk P := ⟨by rw [hPw]; decide, by rw [hPl, hPw]; rfl⟩
            have hes2 := entropy_secret_spec P hPok
            have hpm2 := permutation_spec inst
              (pback (⟨(fb p3).engine, p2.password, p2.work, p2.geometry⟩ : feistel.Permutation E))
              pw .TwentyFourWords original.wordCount hp1 (by rw [hpb]; exact hwork) hpw
            step*
            iterate 6 (try (subst x_post); try step*)
            obtain ⟨p4, pback1⟩ := x
            have hm2 := x_post
            simp only at hm2
            step*
            have hP4 := x_post
            have hP5 := x_post1
            have hab3 := secret_as_bytes_spec x hP4
            let* ⟨ s5, hs5 ⟩ ← hab3
            simp only [hpb] at hm2
            have hs5l : s5.val.length = 2 * (settingOf .TwentyFourWords original.wordCount.val
                self.work pw).half := by
              rw [hs5, hP5]; simp only [Slice.length] at hs2l; rw [hs2l]; rfl
            have hinv := inverse_spec inst A hA _
              (encrypt_inverse_callback_total inst fn1 fn2 hcb1) p4 _ hm2 s5 hs5l (fb1 c1)
            let* ⟨ rr2, e4, he4, hpost2 ⟩ ← hinv
            obtain ⟨res2, p5, ib, c2, ib1⟩ := rr2
            simp only at he4 hpost2
            cases res2 with
            | Err err =>
              simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.«from»]
              step*
              iterate 3 (try (subst x_post); try step*)
              show ok _ ⦃ _ ⦄
              simp
            | Ok cf =>
              cases cf with
              | Break u =>
                step*
                iterate 3 (try (subst x_post); try step*)
                show ok _ ⦃ _ ⦄
                simp
              | Continue bk =>
                obtain ⟨hbk, hbklen, hbkle, hbkz⟩ := hpost2 bk rfl
                have hab4 := secret_as_bytes_le_spec bk hbkle
                step*
                iterate 3 (try (subst x_post); try step*)
                by_cases hb2 : x = true
                · rw [if_pos hb2]
                  step*
                  show ok _ ⦃ _ ⦄
                  simp only [WP.spec_ok]
                  intro cont hcont
                  simp only [core.result.Result.Ok.injEq,
                    core.ops.control_flow.ControlFlow.Continue.injEq] at hcont
                  subst hcont
                  have hs1bk : s1.val = secretBytes bk := by rw [← x_post.mp hb2]; assumption
                  have hXv : s1.val = createState .TwentyFourWords original.entropyBytes.val := by
                    rw [hs1, hx3, heb, hent2]; rfl
                  have hYv : P.entropyBytes.val = MhfeSpec.perm (modelPrims A)
                      (settingOf .TwentyFourWords original.wordCount.val self.work pw) s1.val := by
                    rw [hP]; simp only; rw [hs2, hy]
                  refine ⟨by rw [hYv, hXv], ?_, ?_, ?_⟩
                  · intro h
                    apply hne
                    apply Slice.ext
                    rw [hXv, ← h, hP]
                  · rw [← hXv, hs1bk, hbk, hs5, hP5, hP]
                  · rw [hPw, hPl]
                · rw [if_neg hb2]
                  step*
                  show ok _ ⦃ _ ⦄
                  simp
  | SameLength =>
    step*
    rw [if_pos (by simp)]
    have hsw := state_words_spec
    step*
    by_cases h24 : original.wordCount.val = 24
    · rw [if_pos (UScalar.eq_of_val_eq (by simp_all))]
      step*
      show ok _ ⦃ _ ⦄
      simp
    · rw [if_neg (fun h => h24 (by rw [h]; simp_all))]
      have hcs : suite.Suite.SameLength = codeSuiteOf original.wordCount.val := by
        simp [codeSuiteOf, h24]
      have hEl : MhfeSpec.entropyBytes original.wordCount.val ∈ ([16, 20, 24, 28, 32] : List Nat) := by
        simp [MhfeSpec.wordCounts] at hp1
        rcases hp1 with h | h | h | h | h <;> rw [h] <;> decide
      have hEw : MhfeSpec.entropyBytes original.wordCount.val / 4 * 3 = original.wordCount.val := by
        simp [MhfeSpec.wordCounts] at hp1
        rcases hp1 with h | h | h | h | h <;> rw [h] <;> decide
      let* ⟨ ent, hent1, hent2 ⟩ ← hes
      have hpm := permutation_spec inst self pw .SameLength original.wordCount hp1 hwork hpw
      step*
      obtain ⟨p2, pback⟩ := x
      have hm := x_post
      have hpe := x_post1
      have hpb := x_post2
      simp only at hm hpe hpb
      have hab1 := secret_as_bytes_spec ent hent1
      step*
      rename' x => s1, x_post => hs1
      have hxl : s1.val.length = 2 * (settingOf .SameLength original.wordCount.val self.work pw).half := by
        rw [hs1, hent2, hp.2]; simp only [settingOf, MhfeSpec.Setting.half]
        rw [half_twice _ _ hp1 hcs]
      have hfw := forward_spec inst A hA _ (encrypt_forward_callback_total inst fn1 fn2 hcb1) p2 _ hm
        s1 hxl cb1
      let* ⟨ rr, e3, he3, hpost ⟩ ← hfw
      obtain ⟨res, p3, fb, c1, fb1⟩ := rr
      simp only at he3 hpost
      cases res with
      | Err err =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.«from»]
        step*
        subst x_post
        step*
        show ok _ ⦃ _ ⦄
        simp
      | Ok cf =>
        cases cf with
        | Break u =>
          step*
          subst x_post
          step*
          show ok _ ⦃ _ ⦄
          simp
        | Continue y =>
          obtain ⟨hy, hylen, hyle, hyz⟩ := hpost y rfl
          have hab2 := secret_as_bytes_le_spec y hyle
          step*
          subst x_post
          let* ⟨ s2, hs2 ⟩ ← hab2
          have hs2l : s2.length = MhfeSpec.entropyBytes original.wordCount.val := by
            simp only [Slice.length]; rw [hs2, secretBytes_length _ hyle, hylen]
            simp only [settingOf, MhfeSpec.Setting.half]; rw [half_twice _ _ hp1 hcs]
          simp only [cipher.reject_fixed_point]
          have henc := encode_spec s2 (by rw [hs2l]; exact hEl)
          step*
          by_cases hfx : x = true
          · rw [if_pos hfx]
            simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              core.convert.FromSame.«from»]
            step*
            show ok _ ⦃ _ ⦄
            simp
          · rw [if_neg hfx]
            have hne := fun h => hfx (x_post.mpr h)
            simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
            step*
            subst x_post
            simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
            obtain ⟨⟨cf3, t2⟩, hv2⟩ :=
              hcb2 cb2 ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩
            have hcall : fn2.call_mut cb2 ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩ ⦃ q =>
                q = (cf3, t2) ⦄ := by rw [hv2]; exact (WP.spec_ok _).mpr rfl
            cases cf3 with
            | Break u =>
              have hib : core.ops.control_flow.ControlFlow.is_break
                  (core.ops.control_flow.ControlFlow.Break u : core.ops.control_flow.ControlFlow Unit Unit)
                  ⦃ b => b = true ⦄ := by simp [core.ops.control_flow.ControlFlow.is_break]
              step*
              subst x_post
              step*
              rw [if_pos x_post]
              step*
              show ok _ ⦃ _ ⦄
              simp
            | Continue u =>
              have hib : core.ops.control_flow.ControlFlow.is_break
                  (core.ops.control_flow.ControlFlow.Continue u : core.ops.control_flow.ControlFlow Unit Unit)
                  ⦃ b => b = false ⦄ := by simp [core.ops.control_flow.ControlFlow.is_break]
              step*
              subst x_post
              step*
              rw [if_neg (by simp [x_post])]
              set P : phrase.Phrase := ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩ with hP
              have hPw : P.wordCount.val = original.wordCount.val := by
                rw [hP]; simp only; rw [usize_ofNat_val _ (by rw [hs2l]; omega), hs2l, hEw]
              have hPl : P.entropyBytes.val.length = MhfeSpec.entropyBytes original.wordCount.val := by
                rw [hP]; simpa [Slice.length] using hs2l
              have has := as_str_spec P (by omega)
              have hrt := read_text_spec P (by rw [hPw]; omega) (by omega)
              have hrok : core.result.Result.ok (core.result.Result.Ok P : core.result.Result
                  phrase.Phrase error.Error) ⦃ o => o = some P ⦄ := by simp [core.result.Result.ok]
              have hfil : core.option.Option.filter
                  (cipher.Mhfe.encrypt.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared1PhraseBool
                    inst fn1 fn2) (some P) P ⦃ o => o = some P ⦄ := by
                simp [core.option.Option.filter,
                  cipher.Mhfe.encrypt.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared1PhraseBool.call_once,
                  phrase.Phrase.words]
              have hokor : core.option.Option.ok_or (some P) error.Error.CreationCheckFailed ⦃ r =>
                  r = .Ok P ⦄ := by simp [core.option.Option.ok_or]
              have hPok : PhraseOk P := ⟨by rw [hPw]; exact hp1, by rw [hPl, hPw]⟩
              have hes2 := entropy_secret_spec P hPok
              have hpm2 := permutation_spec inst
                (pback (⟨(fb p3).engine, p2.password, p2.work, p2.geometry⟩ : feistel.Permutation E))
                pw .SameLength original.wordCount hp1 (by rw [hpb]; exact hwork) hpw
              step*
              iterate 6 (try (subst x_post); try step*)
              obtain ⟨p4, pback1⟩ := x
              have hm2 := x_post
              simp only at hm2
              step*
              have hP4 := x_post
              have hP5 := x_post1
              have hab3 := secret_as_bytes_spec x hP4
              let* ⟨ s5, hs5 ⟩ ← hab3
              simp only [hpb] at hm2
              have hs5l : s5.val.length = 2 * (settingOf .SameLength original.wordCount.val
                  self.work pw).half := by
                rw [hs5, hP5]; simp only [Slice.length] at hs2l; rw [hs2l]
                simp only [settingOf, MhfeSpec.Setting.half]; rw [half_twice _ _ hp1 hcs]
              have hinv := inverse_spec inst A hA _
                (encrypt_inverse_callback_total inst fn1 fn2 hcb1) p4 _ hm2 s5 hs5l (fb1 c1)
              let* ⟨ rr2, e4, he4, hpost2 ⟩ ← hinv
              obtain ⟨res2, p5, ib, c2, ib1⟩ := rr2
              simp only at he4 hpost2
              cases res2 with
              | Err err =>
                simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  core.convert.FromSame.«from»]
                step*
                iterate 3 (try (subst x_post); try step*)
                show ok _ ⦃ _ ⦄
                simp
              | Ok cf =>
                cases cf with
                | Break u =>
                  step*
                  iterate 3 (try (subst x_post); try step*)
                  show ok _ ⦃ _ ⦄
                  simp
                | Continue bk =>
                  obtain ⟨hbk, hbklen, hbkle, hbkz⟩ := hpost2 bk rfl
                  have hab4 := secret_as_bytes_le_spec bk hbkle
                  step*
                  iterate 3 (try (subst x_post); try step*)
                  by_cases hb2 : x = true
                  · rw [if_pos hb2]
                    step*
                    show ok _ ⦃ _ ⦄
                    simp only [WP.spec_ok]
                    intro cont hcont
                    simp only [core.result.Result.Ok.injEq,
                      core.ops.control_flow.ControlFlow.Continue.injEq] at hcont
                    subst hcont
                    have hs1bk : s1.val = secretBytes bk := by rw [← x_post.mp hb2]; assumption
                    have hXv : s1.val = createState .SameLength original.entropyBytes.val := by
                      rw [hs1, hent2]; rfl
                    have hYv : P.entropyBytes.val = MhfeSpec.perm (modelPrims A)
                        (settingOf .SameLength original.wordCount.val self.work pw) s1.val := by
                      rw [hP]; simp only; rw [hs2, hy]
                    refine ⟨by rw [hYv, hXv], ?_, ?_, ?_⟩
                    · intro h
                      apply hne
                      apply Slice.ext
                      rw [hXv, ← h, hP]
                    · rw [← hXv, hs1bk, hbk, hs5, hP5, hP]
                    · rw [hPw, hPl, hEw]
                  · rw [if_neg hb2]
                    step*
                    show ok _ ⦃ _ ⦄
                    simp

end MhfeProofs
