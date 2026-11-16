import MhfeCore.Proofs.RoundTrip

/-!
# The code reaches its results

The theorems of `Feistel.lean` and `Cipher.lean` say what a result is when the code gives one. The
theorems below say that it gives one: with an engine whose calls succeed and callbacks that never
stop the work, `forward` and `inverse` return their state, `decrypt` returns a recovery for every
admitted container, and `encrypt` returns a container unless `Perm(X) = X`.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

attribute [local step] of_container_spec suite_is_some_and_spec core.option.Option.expect.spec
  slice_eq_u8_spec

/-- An engine whose calls all succeed. -/
def EngineOk {E : Type} (inst : engine.Argon2Engine E) : Prop :=
  ∀ st pw salt m t key, inst.argon2id st pw salt m t key ⦃ r _ _ => r = core.result.Result.Ok () ⦄

theorem round_ok {E : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (hOk : EngineOk inst)
    (self : feistel.Permutation E) (c : MhfeSpec.Setting) (hc : Matches self c)
    (space : feistel.Workspace) (l r : List Std.U8) (hw : WsInv space l r)
    (hg : space.geometry = self.geometry) (round : Std.U32) (masked : feistel.Side) :
    feistel.Permutation.round inst self space round masked ⦃ res self1 _back space1 =>
      res = core.result.Result.Ok () ∧ (∃ e, self1 = { self with engine := e }) ∧
      space1.geometry = self.geometry ∧
        WsInv space1 (sideRound masked (MhfeSpec.roundMask (modelPrims A) c round.val) (l, r)).1
          (sideRound masked (MhfeSpec.roundMask (modelPrims A) c round.val) (l, r)).2 ⦄ := by
  have hrm := roundMask_code A self c hc round.val
  obtain ⟨hds, hdm, hhalf, hent, hgeo, hmem, hpim, hmemOk, hpimOk, hpwOk, hpw⟩ := hc
  have hgeo' := hgeo
  obtain ⟨h0, h1⟩ := hgeo'
  have hlenl := hw.left
  have hlenr := hw.right
  unfold feistel.Permutation.round
  let* ⟨ p, pback, hpl, hpr, hpok, hpback ⟩ ← parts_spec
  obtain ⟨PL, PR, PM, PK⟩ := hpok
  rw [hg] at PL PR PM PK hpback
  have hmb : ∀ src : Slice Std.U8, src.val.length = self.geometry.half_bytes.val →
      p.message.length = (be32All [some self.work.memory_level, some self.work.pim,
        self.geometry.entropy_bits, some round]).length + src.length := by
    intro src hs
    simp only [Slice.length, PM, be32All_length, mbOf, hs]
    cases self.geometry.entropy_bits <;> simp
  simp only [MhfeSpec.maxMemoryLevel, MhfeSpec.maxPim] at hmemOk hpimOk
  simp only [password.Password.as_bytes]
  unfold EngineComputes at hA
  unfold EngineOk at hOk
  have hAA : ∀ st pw salt m t key, inst.argon2id st pw salt m t key ⦃ r st' key' =>
      (r = core.result.Result.Ok () → key' = A pw.val salt.val m.val t.val) ∧
      r = core.result.Result.Ok () ⦄ :=
    fun st pw salt m t key => WP.spec_and (hA st pw salt m t key) (hOk st pw salt m t key)
  cases masked
  · simp only
    let* ⟨ msg, hmsg ⟩ ← write_message_spec
    let* ⟨ salt, hsalt ⟩ ← round_salt_spec
    let* ⟨ pw, hpwb ⟩ ← secret_as_bytes_spec
    let* ⟨ mem, hmemv ⟩ ← memory_kib_spec
    let* ⟨ pas, hpas ⟩ ← passes_spec
    let* ⟨ res, eng1, key, hkey, hres ⟩ ← hAA
    subst hres
    have hk := hkey rfl
    rw [hg]
    let* ⟨ mask, hmask ⟩ ← round_mask_spec
    have hml : mask.val.length = self.geometry.half_bytes.val := by
      rw [hmask]; simp [Slice.length, PK]; omega
    have hM : mask.val = MhfeSpec.roundMask (modelPrims A) c round.val r := by
      rw [hmask, hrm, hk, hsalt, hmsg, hpwb, hmemv, hpas, ← hpr]; simp [Slice.length, PK, hg]
    let* ⟨ x, y, hx, hy ⟩ ← swapWithSlice_ok
    · simp only [Slice.length]; rw [xorZip_val _ _ (by rw [hml, PL])]
      simp [MhfeSpec.xorBytes, PL, PR, hml]
    subst hx
    refine ⟨⟨eng1, rfl⟩, ?_⟩
    have hy' : y.val = MhfeSpec.xorBytes l (MhfeSpec.roundMask (modelPrims A) c round.val r) := by
      rw [hy, xorZip_val _ _ (by rw [hml, PL]), hpl, hM]
    obtain ⟨hgeo1, hinv⟩ := hpback ⟨p.right, y, msg, salt, key, mask⟩ (by
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact PR
        · simp only; rw [hy', MhfeSpec.xorBytes]; simp [← hpl, PL, hM.symm, hml]
        · simp only; rw [hmsg, ← hg]; exact message_mbOf _ _ _ _ _ (by rw [hg]; exact PR)
        · exact hml)
    refine ⟨hgeo1, ?_⟩
    simp only [sideRound, MhfeSpec.forwardRound] at hinv ⊢
    rw [hpr, hy'] at hinv
    exact hinv
  · simp only
    let* ⟨ msg, hmsg ⟩ ← write_message_spec
    let* ⟨ salt, hsalt ⟩ ← round_salt_spec
    let* ⟨ pw, hpwb ⟩ ← secret_as_bytes_spec
    let* ⟨ mem, hmemv ⟩ ← memory_kib_spec
    let* ⟨ pas, hpas ⟩ ← passes_spec
    let* ⟨ res, eng1, key, hkey, hres ⟩ ← hAA
    subst hres
    have hk := hkey rfl
    rw [hg]
    let* ⟨ mask, hmask ⟩ ← round_mask_spec
    have hml : mask.val.length = self.geometry.half_bytes.val := by
      rw [hmask]; simp [Slice.length, PK]; omega
    have hM : mask.val = MhfeSpec.roundMask (modelPrims A) c round.val l := by
      rw [hmask, hrm, hk, hsalt, hmsg, hpwb, hmemv, hpas, ← hpl]; simp [Slice.length, PK, hg]
    let* ⟨ x, y, hx, hy ⟩ ← swapWithSlice_ok
    · simp only [Slice.length]; rw [xorZip_val _ _ (by rw [hml, PR])]
      simp [MhfeSpec.xorBytes, PL, PR, hml]
    subst hx
    refine ⟨⟨eng1, rfl⟩, ?_⟩
    have hy' : y.val = MhfeSpec.xorBytes r (MhfeSpec.roundMask (modelPrims A) c round.val l) := by
      rw [hy, xorZip_val _ _ (by rw [hml, PR]), hpr, hM]
    obtain ⟨hgeo1, hinv⟩ := hpback ⟨y, p.left, msg, salt, key, mask⟩ (by
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only; rw [hy', MhfeSpec.xorBytes]; simp [← hpr, PR, hM.symm, hml]
        · exact PL
        · simp only; rw [hmsg, ← hg]; exact message_mbOf _ _ _ _ _ (by rw [hg]; exact PL)
        · exact hml)
    refine ⟨hgeo1, ?_⟩
    simp only [sideRound, MhfeSpec.backwardRound] at hinv ⊢
    rw [hpl, hy'] at hinv
    exact hinv

/-- A callback that lets every round run: it returns `Continue` for the round numbers 1 to 12. -/
def CallbackContinues {T2 : Type}
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit)) :
    Prop :=
  ∀ s i, i.val ≤ MhfeSpec.rounds → ∃ s', fnInst.call_mut s i =
    ok (core.ops.control_flow.ControlFlow.Continue (), s')

theorem forwardLoop_ok {E T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (hOk : EngineOk inst)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb : CallbackContinues fnInst) (c : MhfeSpec.Setting) (st0 : MhfeSpec.Bytes × MhfeSpec.Bytes) :
    ∀ (fuel : Nat) (self : feistel.Permutation E) (space : feistel.Workspace) (cb : T2)
      (k : Std.U32), Matches self c → k.val + fuel = MhfeSpec.rounds →
      WsInv space (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) k.val st0).1
        (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) k.val st0).2 →
      space.geometry = self.geometry →
      MhfeTranslation.forwardLoop inst fnInst self space cb k fuel ⦃ res self1 _cb1 =>
        (∃ e, self1 = { self with engine := e }) ∧
        ∃ sp, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue sp) ∧
          sp.geometry = self.geometry ∧
          WsInv sp (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) MhfeSpec.rounds st0).1
            (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) MhfeSpec.rounds st0).2 ⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro self space cb k hc hk hw hg
    simp only [MhfeTranslation.forwardLoop, WP.spec_ok]
    simp only [Nat.add_zero] at hk
    rw [hk] at hw
    exact ⟨⟨self.engine, rfl⟩, space, rfl, hg, hw⟩
  | succ fuel ih =>
    intro self space cb k hc hk hw hg
    simp only [MhfeTranslation.forwardLoop]
    simp only [MhfeSpec.rounds] at hk
    step as ⟨ i, hi ⟩
    obtain ⟨cb1, hv⟩ := hcb cb i (by simp only [MhfeSpec.rounds]; omega)
    simp only [hv, bind_tc_ok]
    simp [core.ops.control_flow.ControlFlow.is_break]
    let* ⟨ r, self1, bk, space1, hr, e1, he1, hg1, hw1 ⟩ ←
      round_ok inst A hA hOk self c hc space _ _ hw hg k feistel.Side.Left
    subst hr
    simp only
    step as ⟨ next, hnext ⟩
    have hc1 : Matches self1 c := by rw [he1]; exact matches_engine self c hc e1
    have hw1' : WsInv space1
        (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) next.val st0).1
        (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) next.val st0).2 := by
      rw [hnext]; simp only [MhfeSpec.forwardRounds]; exact hw1
    have := ih self1 space1 cb1 next hc1 (by simp [MhfeSpec.rounds]; omega) hw1'
      (by rw [hg1, he1])
    apply WP.spec_mono this
    rintro ⟨res, self2, cb2⟩ ⟨⟨e2, he2⟩, sp, hsp, hsg, hsw⟩
    exact ⟨⟨e2, by rw [he2, he1]⟩, sp, hsp, by rw [hsg, he1], hsw⟩

theorem inverseLoop_ok {E T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (hOk : EngineOk inst)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb : CallbackContinues fnInst) (c : MhfeSpec.Setting) :
    ∀ (fuel : Nat) (self : feistel.Permutation E) (space : feistel.Workspace) (cb : T2)
      (step : Std.U32) (st : MhfeSpec.Bytes × MhfeSpec.Bytes), Matches self c →
      step.val + fuel = MhfeSpec.rounds + 1 → WsInv space st.1 st.2 →
      space.geometry = self.geometry →
      MhfeTranslation.inverseLoop inst fnInst self space cb step fuel ⦃ res self1 _cb1 =>
        (∃ e, self1 = { self with engine := e }) ∧
        ∃ sp, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue sp) ∧
          sp.geometry = self.geometry ∧
          WsInv sp (MhfeSpec.backwardRounds (MhfeSpec.roundMask (modelPrims A) c) fuel st).1
            (MhfeSpec.backwardRounds (MhfeSpec.roundMask (modelPrims A) c) fuel st).2 ⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro self space cb step st hc hk hw hg
    simp only [MhfeTranslation.inverseLoop, WP.spec_ok]
    exact ⟨⟨self.engine, rfl⟩, space, rfl, hg, hw⟩
  | succ fuel ih =>
    intro self space cb step st hc hk hw hg
    simp only [MhfeTranslation.inverseLoop]
    simp only [MhfeSpec.rounds] at hk
    obtain ⟨cb1, hv⟩ := hcb cb step (by simp only [MhfeSpec.rounds]; omega)
    simp only [hv, bind_tc_ok]
    simp [core.ops.control_flow.ControlFlow.is_break]
    step as ⟨ rnd, hrnd ⟩
    have hrv : rnd.val = fuel := by
      rw [hrnd]; simp only [UScalar.val]; simp; omega
    let* ⟨ r, self1, bk, space1, hr, e1, he1, hg1, hw1 ⟩ ←
      round_ok inst A hA hOk self c hc space _ _ hw hg rnd feistel.Side.Right
    subst hr
    simp only
    step as ⟨ next, hnext ⟩
    have hc1 : Matches self1 c := by rw [he1]; exact matches_engine self c hc e1
    have := ih self1 space1 cb1 next
      (sideRound feistel.Side.Right (MhfeSpec.roundMask (modelPrims A) c rnd.val) st) hc1
      (by simp [MhfeSpec.rounds]; omega) hw1 (by rw [hg1, he1])
    apply WP.spec_mono this
    rintro ⟨res, self2, cb2⟩ ⟨⟨e2, he2⟩, sp, hsp, hsg, hsw⟩
    refine ⟨⟨e2, by rw [he2, he1]⟩, sp, hsp, by rw [hsg, he1], ?_⟩
    simp only [sideRound, hrv] at hsw
    simp only [MhfeSpec.backwardRounds]
    exact hsw

/-- With an engine whose calls succeed and a callback that lets every round run, `forward` returns
`Perm(X)`. -/
theorem forward_ok {E T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (hOk : EngineOk inst)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb : CallbackContinues fnInst) (self : feistel.Permutation E) (c : MhfeSpec.Setting)
    (hc : Matches self c) (x : Slice Std.U8) (hx : x.val.length = 2 * c.half) (cb : T2) :
    feistel.Permutation.forward inst fnInst self x cb ⦃ res self1 _back _cb1 _cbBack =>
      (∃ e, self1 = { self with engine := e }) ∧
      ∃ st, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st) ∧
        secretBytes st = MhfeSpec.perm (modelPrims A) c x.val ∧ st.len.val = 2 * c.half ∧
        SecretLe st ⦄ := by
  have hgeo := hc.geo
  have hhalf := hc.half
  unfold feistel.Permutation.forward
  let* ⟨ space, hsg, hsw ⟩ ← workspace_new_spec
  have hloop := forwardLoop_ok inst A hA hOk fnInst hcb c
    (x.val.take c.half, x.val.drop c.half) MhfeSpec.rounds self space cb 0#u32 hc (by scalar_tac)
    (by rw [show (0#u32).val = 0 by scalar_tac]; simp only [MhfeSpec.forwardRounds]
        rw [← hhalf]; exact hsw) (by rw [hsg])
  rw [rounds_val]
  apply WP.spec_bind hloop
  rintro ⟨res, self1, cb1⟩ ⟨⟨e1, he1⟩, sp, rfl, hspg, hspw⟩
  let* ⟨ st, hst, hlen, hle, hz ⟩ ← into_state_spec
  exact ⟨⟨e1, he1⟩, st, rfl, by rw [hst]; simp [MhfeSpec.perm], by rw [hlen, hspg, hhalf], hle⟩

/-- With an engine whose calls succeed and a callback that lets every round run, `inverse` returns
`Perm^-1(Y)`. -/
theorem inverse_ok {E T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (hOk : EngineOk inst)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb : CallbackContinues fnInst) (self : feistel.Permutation E) (c : MhfeSpec.Setting)
    (hc : Matches self c) (y : Slice Std.U8) (hy : y.val.length = 2 * c.half) (cb : T2) :
    feistel.Permutation.inverse inst fnInst self y cb ⦃ res self1 _back _cb1 _cbBack =>
      (∃ e, self1 = { self with engine := e }) ∧
      ∃ st, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st) ∧
        secretBytes st = MhfeSpec.permInv (modelPrims A) c y.val ∧ st.len.val = 2 * c.half ∧
        SecretLe st ⦄ := by
  have hgeo := hc.geo
  have hhalf := hc.half
  unfold feistel.Permutation.inverse
  let* ⟨ space, hsg, hsw ⟩ ← workspace_new_spec
  have hloop := inverseLoop_ok inst A hA hOk fnInst hcb c MhfeSpec.rounds self space cb 1#u32
    (y.val.take c.half, y.val.drop c.half) hc (by simp [MhfeSpec.rounds])
    (by rw [← hhalf]; exact hsw) (by rw [hsg])
  rw [rounds_val]
  apply WP.spec_bind hloop
  rintro ⟨res, self1, cb1⟩ ⟨⟨e1, he1⟩, sp, rfl, hspg, hspw⟩
  let* ⟨ st, hst, hlen, hle, hz ⟩ ← into_state_spec
  exact ⟨⟨e1, he1⟩, st, rfl, by rw [hst]; simp [MhfeSpec.permInv], by rw [hlen, hspg, hhalf], hle⟩

/-- A callback of the host that lets the work go on: it returns `Continue`. -/
def HostContinues {T1 A : Type}
    (fnInst : core.ops.function.FnMut T1 A (core.ops.control_flow.ControlFlow Unit Unit)) : Prop :=
  ∀ s a, ∃ s', fnInst.call_mut s a = ok (core.ops.control_flow.ControlFlow.Continue (), s')

theorem decrypt_callback_continues {E T1 : Type} (inst : engine.Argon2Engine E)
    (fnInst : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit)) (h : HostContinues fnInst) :
    CallbackContinues
      (cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
        inst fnInst) := by
  intro s i _
  obtain ⟨t, hv⟩ := h s (i, suite.ROUNDS)
  refine ⟨t, ?_⟩
  simp [cipher.Mhfe.decrypt.closure.closure_1.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut, hv]

/-- `decrypt` recovers every admitted container: with an engine whose calls succeed and a callback
that lets the rounds run, a container whose suite (if one is given) is the one its length selects
and whose stated length (if one is given) is admitted gives a recovery, which holds
`Perm^-1` of the container's entropy. -/
theorem decrypt_ok {E T1 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (hOk : EngineOk inst)
    (fnInst : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit)) (hcb : HostContinues fnInst)
    (self : cipher.Mhfe E) (hwork : WorkOk self.work) (container : phrase.Phrase)
    (hp : PhraseOk container) (pw : password.Password) (hpw : SecretOk pw.encoded)
    (stated : Option Std.Usize) (su : Option suite.Suite)
    (hsu : ∀ s, su = some s → s = codeSuiteOf container.wordCount.val)
    (ha : MhfeSpec.admitsLength container.wordCount.val (stated.map (·.val))) (cb : T1) :
    cipher.Mhfe.decrypt inst fnInst self container pw stated su cb ⦃ r _ _ =>
      ∃ rec, r = .Ok (.Continue rec) ∧
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
  try simp only [Option.some.injEq] at *
  try subst_vars
  have hx : ¬ x = true := by
    rw [x_post]; rintro ⟨s, hs1, hs2⟩; exact hs2 (hsu s hs1)
  rw [if_neg hx]
  let* ⟨ r, hr ⟩ ← admit_spec
  have hrok : r = .Ok () := hr.mpr ha
  subst hrok
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
  have hinv := inverse_ok inst A hA hOk _ (decrypt_callback_continues inst fnInst hcb) p2 _ hm
    s1 hy cb
  let* ⟨ rr, e3, he3, st, hres, hst, hlen, hle ⟩ ← hinv
  obtain ⟨res, p3, ib, c1, ib1⟩ := rr
  simp only at he3 hres hst hlen hle
  subst hres
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
  exact ⟨_, rfl, x_post, by rw [st_post]; exact hst'⟩

open MhfeBits MhfeBridge MhfeLean MhfeModelLink in
/-- `Perm^-1` undoes `Perm` on states of two halves. -/
theorem permInv_perm (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize)
    (c : MhfeSpec.Setting) (hh : c.half ≤ 32) (x : MhfeSpec.Bytes) (hx : x.length = 2 * c.half) :
    MhfeSpec.permInv (modelPrims A) c (MhfeSpec.perm (modelPrims A) c x) = x := by
  have hF := modelPrims_wellFormed A
  let v : Lemma1.State (8 * c.half) :=
    (fromBytes c.half (x.take c.half), fromBytes c.half (x.drop c.half))
  have hxv : x = toBytes c.half v.1 ++ toBytes c.half v.2 := by
    simp only [v]
    rw [toBytes_fromBytes _ _ (by simp; omega), toBytes_fromBytes _ _ (by simp; omega)]
    simp
  rw [hxv, perm_eq_deniabilityCipher _ c hF hh v]
  simp only
  rw [permInv_eq_deniabilityCipher _ c hF hh]
  simp

theorem encrypt_forward_callback_continues {E T1 T2 : Type} (inst : engine.Argon2Engine E)
    (fn1 : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit))
    (fn2 : core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow Unit Unit))
    (h : HostContinues fn1) :
    CallbackContinues
      (cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
        inst fn1 fn2) := by
  intro s i _
  obtain ⟨t, hv⟩ := h s (i, 24#u32)
  refine ⟨t, ?_⟩
  simp [cipher.Mhfe.encrypt.closure.closure.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut,
    rounds_twice, hv]

theorem encrypt_inverse_callback_continues {E T1 T2 : Type} (inst : engine.Argon2Engine E)
    (fn1 : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit))
    (fn2 : core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow Unit Unit))
    (h : HostContinues fn1) :
    CallbackContinues
      (cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple
        inst fn1 fn2) := by
  intro s i hi
  obtain ⟨v, hv1, hv2⟩ := u32_add_ok suite.ROUNDS i (by simp [suite.ROUNDS, MhfeSpec.rounds] at hi ⊢; omega)
  obtain ⟨t, hc⟩ := h s (v, 24#u32)
  refine ⟨t, ?_⟩
  simp [cipher.Mhfe.encrypt.closure.closure_2.Insts.CoreOpsFunctionFnMutTupleU32ControlFlowTupleTuple.call_mut,
    rounds_twice, hv1, hc]

set_option maxHeartbeats 4000000 in
/-- `encrypt` creates a container: with an engine whose calls succeed and callbacks that let the
work go on, it returns a container for every original that its suite accepts, unless `Perm(X) = X`
(which the specification refuses and a working permutation meets with probability `2^-256`, or
`2^-ENT` in suite 4). -/
theorem encrypt_ok {E T1 T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (hOk : EngineOk inst)
    (fn1 : core.ops.function.FnMut T1 (Std.U32 × Std.U32)
      (core.ops.control_flow.ControlFlow Unit Unit)) (hcb1 : HostContinues fn1)
    (fn2 : core.ops.function.FnMut T2 phrase.Phrase (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb2 : HostContinues fn2)
    (self : cipher.Mhfe E) (hwork : WorkOk self.work) (original : phrase.Phrase)
    (hp : PhraseOk original) (pw : password.Password) (hpw : SecretOk pw.encoded)
    (su : suite.Suite) (hsu : su = .SameLength → original.wordCount.val ≠ 24)
    (hfix : MhfeSpec.perm (modelPrims A) (settingOf su original.wordCount.val self.work pw)
      (createState su original.entropyBytes.val) ≠ createState su original.entropyBytes.val)
    (cb1 : T1) (cb2 : T2) :
    cipher.Mhfe.encrypt inst fn1 fn2 self original pw su cb1 cb2 ⦃ r _ _ _ =>
      ∃ container, r = .Ok (.Continue container) ∧
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
    have hXv : s1.val = createState .TwentyFourWords original.entropyBytes.val := by
      rw [hs1, hx3, heb, hent2]; rfl
    have hh : (settingOf .TwentyFourWords original.wordCount.val self.work pw).half ≤ 32 := by
      have := hm.geo.2; rw [hm.half] at this; omega
    have hfw := forward_ok inst A hA hOk _ (encrypt_forward_callback_continues inst fn1 fn2 hcb1)
      p2 _ hm s1 hxl cb1
    let* ⟨ rr, e3, he3, y, hres, hy, hylen, hyle ⟩ ← hfw
    obtain ⟨res, p3, fb, c1, fb1⟩ := rr
    simp only at he3 hres hy hylen hyle
    subst hres
    have hab2 := secret_as_bytes_le_spec y hyle
    step*
    subst x_post
    let* ⟨ s2, hs2 ⟩ ← hab2
    have hs2l : s2.length = 32 := by
      simp only [Slice.length]; rw [hs2, secretBytes_length _ hyle, hylen]; rfl
    simp only [cipher.reject_fixed_point]
    have henc := encode_spec s2 (by rw [hs2l]; decide)
    step*
    have hfx : ¬ x = true := by
      intro h
      apply hfix
      have h12 := congrArg Slice.val (x_post.mp h)
      rw [hs2, hy, hXv] at h12
      exact h12.symm
    rw [if_neg hfx]
    have hne := fun h => hfx (x_post.mpr h)
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step*
    subst x_post
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨t2, hv2⟩ := hcb2 cb2 ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩
    have hcall : fn2.call_mut cb2 ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩ ⦃ q =>
        q = (core.ops.control_flow.ControlFlow.Continue (), t2) ⦄ := by
      rw [hv2]; exact (WP.spec_ok _).mpr rfl
    have hib : core.ops.control_flow.ControlFlow.is_break
        (core.ops.control_flow.ControlFlow.Continue () : core.ops.control_flow.ControlFlow Unit Unit)
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
    have hinv := inverse_ok inst A hA hOk _
      (encrypt_inverse_callback_continues inst fn1 fn2 hcb1) p4 _ hm2 s5 hs5l (fb1 c1)
    let* ⟨ rr2, e4, he4, bk, hres2, hbk, hbklen, hbkle ⟩ ← hinv
    obtain ⟨res2, p5, ib, c2, ib1⟩ := rr2
    simp only at he4 hres2 hbk hbklen hbkle
    subst hres2
    have hab4 := secret_as_bytes_le_spec bk hbkle
    step*
    iterate 3 (try (subst x_post); try step*)
    have hb2 : x = true := by
      rw [x_post]; apply Slice.ext
      refine Eq.trans (by assumption : _ = secretBytes bk) ?_
      rw [hbk, hs5, hP5, hs2, hy, permInv_perm A _ hh _ hxl]
    rw [if_pos hb2]
    step*
    show ok _ ⦃ _ ⦄
    simp only [WP.spec_ok]
    refine ⟨_, rfl, ?_⟩
    have hs1bk : s1.val = secretBytes bk := by rw [← x_post.mp hb2]; assumption
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
  | SameLength =>
    step*
    rw [if_pos (by simp)]
    have hsw := state_words_spec
    step*
    have h24 := hsu rfl
    rw [if_neg (fun h => h24 (by rw [h]; simp_all))]
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
    have hXv : s1.val = createState .SameLength original.entropyBytes.val := by
      rw [hs1, hent2]; rfl
    have hh : (settingOf .SameLength original.wordCount.val self.work pw).half ≤ 32 := by
      have := hm.geo.2; rw [hm.half] at this; omega
    have hfw := forward_ok inst A hA hOk _ (encrypt_forward_callback_continues inst fn1 fn2 hcb1)
      p2 _ hm s1 hxl cb1
    let* ⟨ rr, e3, he3, y, hres, hy, hylen, hyle ⟩ ← hfw
    obtain ⟨res, p3, fb, c1, fb1⟩ := rr
    simp only at he3 hres hy hylen hyle
    subst hres
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
    have hfx : ¬ x = true := by
      intro h
      apply hfix
      have h12 := congrArg Slice.val (x_post.mp h)
      rw [hs2, hy, hXv] at h12
      exact h12.symm
    rw [if_neg hfx]
    have hne := fun h => hfx (x_post.mpr h)
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step*
    subst x_post
    simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
    obtain ⟨t2, hv2⟩ := hcb2 cb2 ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩
    have hcall : fn2.call_mut cb2 ⟨⟨BitVec.ofNat _ (s2.length / 4 * 3)⟩, s2⟩ ⦃ q =>
        q = (core.ops.control_flow.ControlFlow.Continue (), t2) ⦄ := by
      rw [hv2]; exact (WP.spec_ok _).mpr rfl
    have hib : core.ops.control_flow.ControlFlow.is_break
        (core.ops.control_flow.ControlFlow.Continue () : core.ops.control_flow.ControlFlow Unit Unit)
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
    have hinv := inverse_ok inst A hA hOk _
      (encrypt_inverse_callback_continues inst fn1 fn2 hcb1) p4 _ hm2 s5 hs5l (fb1 c1)
    let* ⟨ rr2, e4, he4, bk, hres2, hbk, hbklen, hbkle ⟩ ← hinv
    obtain ⟨res2, p5, ib, c2, ib1⟩ := rr2
    simp only at he4 hres2 hbk hbklen hbkle
    subst hres2
    have hab4 := secret_as_bytes_le_spec bk hbkle
    step*
    iterate 3 (try (subst x_post); try step*)
    have hb2 : x = true := by
      rw [x_post]; apply Slice.ext
      refine Eq.trans (by assumption : _ = secretBytes bk) ?_
      rw [hbk, hs5, hP5, hs2, hy, permInv_perm A _ hh _ hxl]
    rw [if_pos hb2]
    step*
    show ok _ ⦃ _ ⦄
    simp only [WP.spec_ok]
    refine ⟨_, rfl, ?_⟩
    have hs1bk : s1.val = secretBytes bk := by rw [← x_post.mp hb2]; assumption
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

/-- The original of a suite 3 container is among the readings of its state: with the original's
length stated, the length rules give a list that holds that length (the length alone for a short
original), and the reading of that length is the original's entropy. With `encrypt_ok`,
`created_container_recovers`, `decrypt_ok` and `readings_spec_3`, recovering a created container
with the original's length gives back the original. -/
theorem original_reading (e : List Std.U8) (w : Nat) (hw : w ∈ MhfeSpec.wordCounts)
    (he : e.length = MhfeSpec.entropyBytes w) :
    ∃ L, MhfeSpec.lengthRules (some w) (MhfeSpec.detected shaF (MhfeSpec.pack shaF e)) = some L ∧
      w ∈ L ∧ (w ≠ 24 → L = [w]) ∧
      (MhfeSpec.pack shaF e).take (MhfeSpec.entropyBytes w) = e := by
  have hE := entropyBytes_le w hw
  by_cases h24 : w = 24
  · subst h24
    have hX : MhfeSpec.pack shaF e = e := by
      simp only [MhfeSpec.pack]
      rw [if_neg (by rw [he]; simp [MhfeSpec.stateBytes, MhfeSpec.entropyBytes])]
    have hnd : 24 ∉ MhfeSpec.detected shaF (MhfeSpec.pack shaF e) := by
      simp [MhfeSpec.detected, MhfeSpec.shortWordCounts]
    refine ⟨MhfeSpec.detected shaF (MhfeSpec.pack shaF e) ++ [24], ?_, by simp, by simp, ?_⟩
    · simp only [MhfeSpec.lengthRules, if_neg hnd, if_true]
    · rw [hX]; exact List.take_of_length_le (by rw [he])
  · have hshort : w ∈ MhfeSpec.shortWordCounts := by
      simp [MhfeSpec.wordCounts] at hw; simp [MhfeSpec.shortWordCounts]; omega
    have hlt : e.length < MhfeSpec.stateBytes := by
      simp [MhfeSpec.wordCounts] at hw
      rw [he]; rcases hw with h | h | h | h | h <;> subst h <;> first | decide | omega
    have hX : MhfeSpec.pack shaF e = e ++ (shaF e).take (MhfeSpec.stateBytes - e.length) := by
      simp only [MhfeSpec.pack]; rw [if_pos hlt]
    have htake : (MhfeSpec.pack shaF e).take (MhfeSpec.entropyBytes w) = e := by
      rw [hX, ← he]; simp
    have hm : MhfeSpec.layoutMatches shaF (MhfeSpec.pack shaF e) w = true := by
      simp only [MhfeSpec.layoutMatches]
      rw [htake, hX, ← he]
      simp
    have hd : w ∈ MhfeSpec.detected shaF (MhfeSpec.pack shaF e) := by
      simp only [MhfeSpec.detected, List.mem_filter]; exact ⟨hshort, hm⟩
    exact ⟨[w], by simp [MhfeSpec.lengthRules, hd], by simp, fun _ => rfl, htake⟩

end MhfeProofs
