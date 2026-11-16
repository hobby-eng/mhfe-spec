import MhfeCore.Code
import MhfeCore.Spec.Spec
import MhfeCore.Spec.ModelLink
import MhfeCore.Proofs.Params
import MhfeCore.Proofs.Round
import MhfeCore.Proofs.Message
import MhfeCore.Proofs.Workspace

/-!
# The Feistel permutation of the code is `Perm` of the specification

The theorems hold for every engine that computes a function `A` of its inputs (`EngineComputes`):
the proof takes Argon2id as given and does not look inside the engine.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-! ## The engine and the primitives -/

/-- The engine computes `A`: every call returns, and a call that succeeds writes
`A password salt memoryKiB passes` into the key. An engine may fail (`Err`), for example when it
cannot allocate its memory; it may change its own state. -/
def EngineComputes {E : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) : Prop :=
  ∀ st pw salt m t key, inst.argon2id st pw salt m t key ⦃ r st' key' =>
    r = core.result.Result.Ok () → key' = A pw.val salt.val m.val t.val ⦄

/-- HMAC-SHA-256 under a key of any length, as RFC 2104 defines it from the HMAC of a 64-byte key
block: a key longer than the block is hashed first, and the key is padded with zero bytes to the
block. -/
noncomputable def hmacOfKey (k m : List Std.U8) : List Std.U8 :=
  let k' := if k.length ≤ 64 then k else (MhfeModel.sha256 k).val
  (MhfeModel.hmacSha256 (k' ++ List.replicate (64 - k'.length) 0#u8) m).val

/-- The primitives of the specification, made of the models of the hash functions and of `A`. -/
noncomputable def modelPrims (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) :
    MhfeSpec.Primitives where
  blake2b256 m := (MhfeModel.blake2b256 m).val
  hmacSha256 := hmacOfKey
  argon2id p s m t := (A p s m t).val

theorem modelPrims_wellFormed (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) :
    MhfeModelLink.Primitives.WellFormed (modelPrims A) where
  blake2b256 m := by simp [modelPrims]
  hmacSha256 k m := by simp [modelPrims, hmacOfKey]
  argon2id p s m t := by simp [modelPrims]

/-! ## A permutation of the code and its settings -/

/-- The permutation `p` of the code has the settings `c` of the specification: its geometry has
the domain strings, the half size and the `ENT` of `c`, its work factor is `c`'s and is valid, and
its password holds `c`'s bytes. -/
structure Matches {E : Type} (p : feistel.Permutation E) (c : MhfeSpec.Setting) : Prop where
  ds_salt : p.geometry.ds_salt.val = c.suite.dsSalt
  ds_mask : p.geometry.ds_mask.val = c.suite.dsMask
  half : p.geometry.half_bytes.val = c.half
  ent : p.geometry.entropy_bits.map (·.val) = c.suite.ent c.words
  geo : GeoOk p.geometry
  mem : p.work.memory_level.val = c.mem
  pim : p.work.pim.val = c.pim
  memOk : c.mem ≤ MhfeSpec.maxMemoryLevel
  pimOk : c.pim ≤ MhfeSpec.maxPim
  pwOk : SecretOk p.password.encoded
  pw : secretBytes p.password.encoded = c.password

theorem matches_engine {E : Type} (p : feistel.Permutation E) (c : MhfeSpec.Setting)
    (hc : Matches p c) (e : E) : Matches { p with engine := e } c := by
  obtain ⟨a, b, d, f, g, h, i, j, k, l, m⟩ := hc
  exact ⟨a, b, d, f, g, h, i, j, k, l, m⟩

theorem secret_as_bytes_spec (s : protect.Secret) (hs : SecretOk s) :
    protect.Secret.as_bytes s ⦃ b => b.val = secretBytes s ⦄ := by
  unfold protect.Secret.as_bytes
  simp only [os.Pages.as_slice, bind_tc_ok]
  simp only [SecretOk] at hs
  step*
  all_goals simp_all [secretBytes, List.slice, Slice.length]

/-- The round mask of the specification, computed with the code's geometry and settings. -/
theorem roundMask_code {E : Type} (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize)
    (p : feistel.Permutation E) (c : MhfeSpec.Setting) (hc : Matches p c) (i : Nat)
    (src : List Std.U8) :
    MhfeSpec.roundMask (modelPrims A) c i src =
      (MhfeModel.hmacSha256
        ((A (secretBytes p.password.encoded)
          ((MhfeModel.blake2b256 (p.geometry.ds_salt.val ++
            MhfeSpec.message p.work.memory_level.val p.work.pim.val
              (p.geometry.entropy_bits.map (·.val)) i src)).val.take 16)
          (MhfeSpec.memoryKiB p.work.memory_level.val) (MhfeSpec.passes p.work.pim.val)).val ++
          List.replicate 32 0#u8)
        (p.geometry.ds_mask.val ++
          MhfeSpec.message p.work.memory_level.val p.work.pim.val
            (p.geometry.entropy_bits.map (·.val)) i src)).val.take p.geometry.half_bytes.val := by
  obtain ⟨hds, hdm, hhalf, hent, _, hmem, hpim, _, _, _, hpw⟩ := hc
  simp only [MhfeSpec.roundMask, MhfeSpec.roundMaskOfKey, MhfeSpec.roundSalt, modelPrims,
    hmacOfKey, hds, hdm, hhalf, hent, hmem, hpim, hpw, MhfeSpec.Setting.half]
  simp

/-! ## One round -/

theorem message_length (mem pim : Nat) (ent : Option Nat) (i : Nat) (r : List Std.U8) :
    (MhfeSpec.message mem pim ent i r).length = (if ent.isSome then 4 else 3) * 4 + r.length := by
  cases ent <;> simp [MhfeSpec.message, be32_length] <;> omega

theorem message_mbOf (g : feistel.Geometry) (mem pim i : Nat) (r : List Std.U8)
    (hr : r.length = g.half_bytes.val) :
    (MhfeSpec.message mem pim (g.entropy_bits.map (·.val)) i r).length = mbOf g := by
  rw [message_length, hr, mbOf]; cases g.entropy_bits <;> simp

/-- The round of the specification that the side `masked` takes: the left half takes the mask in
the forward direction, the right half in the inverse direction. -/
def sideRound (masked : feistel.Side) (m : MhfeSpec.Bytes → MhfeSpec.Bytes) :
    MhfeSpec.Bytes × MhfeSpec.Bytes → MhfeSpec.Bytes × MhfeSpec.Bytes :=
  match masked with
  | .Left => MhfeSpec.forwardRound m
  | .Right => MhfeSpec.backwardRound m

theorem xorZip_val (t m : Slice Std.U8) (h : m.val.length = t.val.length) :
    (MhfeTranslation.xorZip t m).val = MhfeSpec.xorBytes t.val m.val := by
  simp [MhfeTranslation.xorZip, MhfeSpec.xorBytes, h]

theorem swapWithSlice_ok (a b : Slice Std.U8) (h : a.length = b.length) :
    MhfeTranslation.swapWithSlice a b ⦃ x y => x = b ∧ y = a ⦄ := by
  simp [MhfeTranslation.swapWithSlice, h]

/-- One round of the code is the round of the specification with the mask `RoundMask(i, ·)`: when
the engine succeeds, the workspace holds the halves after the round; whatever happens, the
permutation keeps its settings. -/
theorem round_spec {E : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (self : feistel.Permutation E) (c : MhfeSpec.Setting) (hc : Matches self c)
    (space : feistel.Workspace) (l r : List Std.U8) (hw : WsInv space l r)
    (hg : space.geometry = self.geometry) (round : Std.U32) (masked : feistel.Side) :
    feistel.Permutation.round inst self space round masked ⦃ res self1 _back space1 =>
      (∃ e, self1 = { self with engine := e }) ∧
      (res = core.result.Result.Ok () → space1.geometry = self.geometry ∧
        WsInv space1 (sideRound masked (MhfeSpec.roundMask (modelPrims A) c round.val) (l, r)).1
          (sideRound masked (MhfeSpec.roundMask (modelPrims A) c round.val) (l, r)).2) ⦄ := by
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
  cases masked
  · simp only
    let* ⟨ msg, hmsg ⟩ ← write_message_spec
    let* ⟨ salt, hsalt ⟩ ← round_salt_spec
    let* ⟨ pw, hpwb ⟩ ← secret_as_bytes_spec
    let* ⟨ mem, hmemv ⟩ ← memory_kib_spec
    let* ⟨ pas, hpas ⟩ ← passes_spec
    let* ⟨ res, eng1, key, hkey ⟩ ← hA
    cases res with
    | Err e => simp [WP.spec_ok]
    | Ok u =>
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
      refine ⟨⟨eng1, rfl⟩, fun _ => ?_⟩
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
    let* ⟨ res, eng1, key, hkey ⟩ ← hA
    cases res with
    | Err e => simp [WP.spec_ok]
    | Ok u =>
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
      refine ⟨⟨eng1, rfl⟩, fun _ => ?_⟩
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


/-! ## The twelve rounds -/

/-- A callback that returns (with any decision) for every round number the loops give it, 1 to 12. -/
def CallbackTotal {T2 : Type}
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit)) :
    Prop :=
  ∀ s i, i.val ≤ MhfeSpec.rounds → ∃ v, fnInst.call_mut s i = ok v

/-- The forward loop from round `k` on, with `fuel = 12 - k` rounds left: when it ends with
`Continue`, the workspace holds the halves after all twelve rounds. -/
theorem forwardLoop_spec {E T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb : CallbackTotal fnInst) (c : MhfeSpec.Setting) (st0 : MhfeSpec.Bytes × MhfeSpec.Bytes) :
    ∀ (fuel : Nat) (self : feistel.Permutation E) (space : feistel.Workspace) (cb : T2)
      (k : Std.U32), Matches self c → k.val + fuel = MhfeSpec.rounds →
      WsInv space (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) k.val st0).1
        (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) k.val st0).2 →
      space.geometry = self.geometry →
      MhfeTranslation.forwardLoop inst fnInst self space cb k fuel ⦃ res self1 _cb1 =>
        (∃ e, self1 = { self with engine := e }) ∧
        ∀ sp, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue sp) →
          sp.geometry = self.geometry ∧
          WsInv sp (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) MhfeSpec.rounds st0).1
            (MhfeSpec.forwardRounds (MhfeSpec.roundMask (modelPrims A) c) MhfeSpec.rounds st0).2 ⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro self space cb k hc hk hw hg
    simp only [MhfeTranslation.forwardLoop, WP.spec_ok]
    refine ⟨⟨self.engine, rfl⟩, ?_⟩
    intro sp hsp
    simp only [core.result.Result.Ok.injEq, core.ops.control_flow.ControlFlow.Continue.injEq] at hsp
    subst hsp
    simp only [Nat.add_zero] at hk
    rw [hk] at hw
    exact ⟨hg, hw⟩
  | succ fuel ih =>
    intro self space cb k hc hk hw hg
    simp only [MhfeTranslation.forwardLoop]
    simp only [MhfeSpec.rounds] at hk
    unfold CallbackTotal at hcb
    step as ⟨ i, hi ⟩
    obtain ⟨⟨cf, cb1⟩, hv⟩ := hcb cb i (by simp only [MhfeSpec.rounds]; omega)
    simp only [hv, bind_tc_ok]
    cases cf with
    | Break u => simp [core.ops.control_flow.ControlFlow.is_break, WP.spec_ok]; exact ⟨self.engine, rfl⟩
    | Continue u =>
      simp [core.ops.control_flow.ControlFlow.is_break]
      let* ⟨ r, self1, bk, space1, e1, he1, hres ⟩ ←
        round_spec inst A hA self c hc space _ _ hw hg k feistel.Side.Left
      cases r with
      | Err err => simp [WP.spec_ok]; exact ⟨e1, he1⟩
      | Ok u =>
        obtain ⟨hg1, hw1⟩ := hres rfl
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
        rintro ⟨res, self2, cb2⟩ ⟨⟨e2, he2⟩, hpost⟩
        refine ⟨⟨e2, by rw [he2, he1]⟩, ?_⟩
        intro sp hsp
        obtain ⟨hsg, hsw⟩ := hpost sp hsp
        exact ⟨by rw [hsg, he1], hsw⟩


/-- The inverse loop with `fuel` rounds left, `step` counting the rounds from 1: when it ends with
`Continue`, the workspace holds the halves after the inverse rounds `fuel - 1, ..., 0`. -/
theorem inverseLoop_spec {E T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb : CallbackTotal fnInst) (c : MhfeSpec.Setting) :
    ∀ (fuel : Nat) (self : feistel.Permutation E) (space : feistel.Workspace) (cb : T2)
      (step : Std.U32) (st : MhfeSpec.Bytes × MhfeSpec.Bytes), Matches self c →
      step.val + fuel = MhfeSpec.rounds + 1 → WsInv space st.1 st.2 →
      space.geometry = self.geometry →
      MhfeTranslation.inverseLoop inst fnInst self space cb step fuel ⦃ res self1 _cb1 =>
        (∃ e, self1 = { self with engine := e }) ∧
        ∀ sp, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue sp) →
          sp.geometry = self.geometry ∧
          WsInv sp (MhfeSpec.backwardRounds (MhfeSpec.roundMask (modelPrims A) c) fuel st).1
            (MhfeSpec.backwardRounds (MhfeSpec.roundMask (modelPrims A) c) fuel st).2 ⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro self space cb step st hc hk hw hg
    simp only [MhfeTranslation.inverseLoop, WP.spec_ok]
    refine ⟨⟨self.engine, rfl⟩, ?_⟩
    intro sp hsp
    simp only [core.result.Result.Ok.injEq, core.ops.control_flow.ControlFlow.Continue.injEq] at hsp
    subst hsp
    exact ⟨hg, hw⟩
  | succ fuel ih =>
    intro self space cb step st hc hk hw hg
    simp only [MhfeTranslation.inverseLoop]
    simp only [MhfeSpec.rounds] at hk
    unfold CallbackTotal at hcb
    obtain ⟨⟨cf, cb1⟩, hv⟩ := hcb cb step (by simp only [MhfeSpec.rounds]; omega)
    simp only [hv, bind_tc_ok]
    cases cf with
    | Break u => simp [core.ops.control_flow.ControlFlow.is_break, WP.spec_ok]; exact ⟨self.engine, rfl⟩
    | Continue u =>
      simp [core.ops.control_flow.ControlFlow.is_break]
      step as ⟨ rnd, hrnd ⟩
      have hrv : rnd.val = fuel := by
        rw [hrnd]; simp only [UScalar.val]; simp; omega
      let* ⟨ r, self1, bk, space1, e1, he1, hres ⟩ ←
        round_spec inst A hA self c hc space _ _ hw hg rnd feistel.Side.Right
      cases r with
      | Err err => simp [WP.spec_ok]; exact ⟨e1, he1⟩
      | Ok u =>
        obtain ⟨hg1, hw1⟩ := hres rfl
        simp only
        step as ⟨ next, hnext ⟩
        have hc1 : Matches self1 c := by rw [he1]; exact matches_engine self c hc e1
        have := ih self1 space1 cb1 next
          (sideRound feistel.Side.Right (MhfeSpec.roundMask (modelPrims A) c rnd.val) st) hc1
          (by simp [MhfeSpec.rounds]; omega) hw1 (by rw [hg1, he1])
        apply WP.spec_mono this
        rintro ⟨res, self2, cb2⟩ ⟨⟨e2, he2⟩, hpost⟩
        refine ⟨⟨e2, by rw [he2, he1]⟩, ?_⟩
        intro sp hsp
        obtain ⟨hsg, hsw⟩ := hpost sp hsp
        refine ⟨by rw [hsg, he1], ?_⟩
        simp only [sideRound, hrv] at hsw
        simp only [MhfeSpec.backwardRounds]
        exact hsw

theorem rounds_val : suite.ROUNDS.val = MhfeSpec.rounds := by
  simp [suite.ROUNDS, MhfeSpec.rounds]

/-- `forward` computes `Perm` of the specification: when it returns `Continue`, the state it
returns holds `Perm(X)`. -/
theorem forward_spec {E T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb : CallbackTotal fnInst) (self : feistel.Permutation E) (c : MhfeSpec.Setting)
    (hc : Matches self c) (x : Slice Std.U8) (hx : x.val.length = 2 * c.half) (cb : T2) :
    feistel.Permutation.forward inst fnInst self x cb ⦃ res self1 _back _cb1 _cbBack =>
      (∃ e, self1 = { self with engine := e }) ∧
      ∀ st, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st) →
        secretBytes st = MhfeSpec.perm (modelPrims A) c x.val ∧ st.len.val = 2 * c.half ∧
        SecretLe st ∧ ∀ b ∈ st.pages.bytes.val.drop st.len.val, b = 0#u8 ⦄ := by
  have hgeo := hc.geo
  have hhalf := hc.half
  unfold feistel.Permutation.forward
  let* ⟨ space, hsg, hsw ⟩ ← workspace_new_spec
  have hloop := forwardLoop_spec inst A hA fnInst hcb c
    (x.val.take c.half, x.val.drop c.half) MhfeSpec.rounds self space cb 0#u32 hc (by scalar_tac)
    (by rw [show (0#u32).val = 0 by scalar_tac]; simp only [MhfeSpec.forwardRounds]
        rw [← hhalf]; exact hsw) (by rw [hsg])
  rw [rounds_val]
  apply WP.spec_bind hloop
  rintro ⟨res, self1, cb1⟩ ⟨⟨e1, he1⟩, hpost⟩
  rcases res with ((sp | u) | err)
  · obtain ⟨hspg, hspw⟩ := hpost sp rfl
    let* ⟨ st, hst, hlen, hle, hz ⟩ ← into_state_spec
    refine ⟨⟨e1, he1⟩, ?_⟩
    intro st' hst'
    simp only [core.result.Result.Ok.injEq, core.ops.control_flow.ControlFlow.Continue.injEq] at hst'
    subst hst'
    refine ⟨by rw [hst]; simp [MhfeSpec.perm], by rw [hlen, hspg, hhalf], hle, hz⟩
  · simp [WP.spec_ok]; exact ⟨e1, he1⟩
  · simp [WP.spec_ok]; exact ⟨e1, he1⟩

/-- `inverse` computes `Perm^-1` of the specification. -/
theorem inverse_spec {E T2 : Type} (inst : engine.Argon2Engine E)
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) (hA : EngineComputes inst A)
    (fnInst : core.ops.function.FnMut T2 Std.U32 (core.ops.control_flow.ControlFlow Unit Unit))
    (hcb : CallbackTotal fnInst) (self : feistel.Permutation E) (c : MhfeSpec.Setting)
    (hc : Matches self c) (y : Slice Std.U8) (hy : y.val.length = 2 * c.half) (cb : T2) :
    feistel.Permutation.inverse inst fnInst self y cb ⦃ res self1 _back _cb1 _cbBack =>
      (∃ e, self1 = { self with engine := e }) ∧
      ∀ st, res = core.result.Result.Ok (core.ops.control_flow.ControlFlow.Continue st) →
        secretBytes st = MhfeSpec.permInv (modelPrims A) c y.val ∧ st.len.val = 2 * c.half ∧
        SecretLe st ∧ ∀ b ∈ st.pages.bytes.val.drop st.len.val, b = 0#u8 ⦄ := by
  have hgeo := hc.geo
  have hhalf := hc.half
  unfold feistel.Permutation.inverse
  let* ⟨ space, hsg, hsw ⟩ ← workspace_new_spec
  have hloop := inverseLoop_spec inst A hA fnInst hcb c MhfeSpec.rounds self space cb 1#u32
    (y.val.take c.half, y.val.drop c.half) hc (by simp [MhfeSpec.rounds])
    (by rw [← hhalf]; exact hsw) (by rw [hsg])
  rw [rounds_val]
  apply WP.spec_bind hloop
  rintro ⟨res, self1, cb1⟩ ⟨⟨e1, he1⟩, hpost⟩
  rcases res with ((sp | u) | err)
  · obtain ⟨hspg, hspw⟩ := hpost sp rfl
    let* ⟨ st, hst, hlen, hle, hz ⟩ ← into_state_spec
    refine ⟨⟨e1, he1⟩, ?_⟩
    intro st' hst'
    simp only [core.result.Result.Ok.injEq, core.ops.control_flow.ControlFlow.Continue.injEq] at hst'
    subst hst'
    refine ⟨by rw [hst]; simp [MhfeSpec.permInv], by rw [hlen, hspg, hhalf], hle, hz⟩
  · simp [WP.spec_ok]; exact ⟨e1, he1⟩
  · simp [WP.spec_ok]; exact ⟨e1, he1⟩

end MhfeProofs
