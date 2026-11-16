import MhfeCore.Code
import MhfeCore.Proofs.Models

/-!
# The secret memory of a permutation
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- The bytes a secret holds. -/
def secretBytes (s : protect.Secret) : List Std.U8 := s.pages.bytes.val.take s.len.val

/-- A well-formed secret: its pages are exactly as long as its length. -/
def SecretOk (s : protect.Secret) : Prop := s.pages.bytes.length = s.len.val

theorem zeroed_spec (n : Std.Usize) (hn : 0 < n.val) :
    protect.Secret.zeroed n ⦃ s => SecretOk s ∧ s.len = n ∧
      s.pages.bytes.val = List.replicate n.val 0#u8 ⦄ := by
  unfold protect.Secret.zeroed protect.Secret.with_capacity
  step*
  have hx : x = n := by
    rw [x_post]; simp [core.cmp.impls.OrdUsize.max]; scalar_tac
  subst hx
  simp [os.unix.Pages.new, MhfeModel.zeros, SecretOk, Slice.length]


/-- The length of the round message: `BE32(MEM) || BE32(PIM) || [BE32(ENT)] || BE32(i) || R`. -/
def mbOf (g : feistel.Geometry) : Nat :=
  (if g.entropy_bits.isSome then 4 else 3) * 4 + g.half_bytes.val

/-- A geometry the code can make: halves of 8 to 16 bytes. -/
def GeoOk (g : feistel.Geometry) : Prop := 0 < g.half_bytes.val ∧ g.half_bytes.val ≤ 16

theorem message_bytes_spec (g : feistel.Geometry) (hg : GeoOk g) :
    feistel.Geometry.message_bytes g ⦃ v => v.val = mbOf g ⦄ := by
  unfold feistel.Geometry.message_bytes
  obtain ⟨h0, h1⟩ := hg
  cases he : g.entropy_bits <;> simp [core.option.Option.is_some, he] <;>
    simp only [feistel.BE32_BYTES] <;> step* <;> simp [mbOf, he, *] <;> scalar_tac

/-- The length of the workspace: both halves, the message, the salt, the key and the mask. -/
def wsLen (g : feistel.Geometry) : Nat := 2 * g.half_bytes.val + mbOf g + 16 + 32 + g.half_bytes.val

/-- A workspace whose halves are `l` and `r`. -/
structure WsInv (w : feistel.Workspace) (l r : List Std.U8) : Prop where
  geo : GeoOk w.geometry
  ok : SecretOk w.secret
  len : w.secret.len.val = wsLen w.geometry
  left : (secretBytes w.secret).take w.geometry.half_bytes.val = l
  right : ((secretBytes w.secret).drop w.geometry.half_bytes.val).take w.geometry.half_bytes.val = r


theorem as_mut_bytes_spec (s : protect.Secret) (hs : SecretOk s) :
    protect.Secret.as_mut_bytes s ⦃ b back =>
      b.val = secretBytes s ∧
      ∀ b' : Slice Std.U8, b'.length = b.length →
        SecretOk (back b') ∧ (back b').len = s.len ∧ secretBytes (back b') = b'.val ⦄ := by
  unfold protect.Secret.as_mut_bytes
  simp only [os.Pages.as_mut_slice, bind_tc_ok]
  step*
  · simp [SecretOk] at hs; simp [hs]
  · refine ⟨by simp [secretBytes, *], ?_⟩
    intro b' hb'
    simp only [SecretOk, Slice.length] at hs hb' s1_post1
    have hl : (index_mut_back b').length = s.pages.bytes.length := by
      simp only [Slice.length, s1_post2, List.length_setSlice!]
    simp only [hl, ite_true, SecretOk, secretBytes, s1_post2]
    refine ⟨by simp only [Slice.length, List.length_setSlice!]; exact hs, ?_⟩
    have : (s.pages.bytes.val.setSlice! 0 b'.val) = b'.val := by
      simp [List.setSlice!, hb', s1_post1, hs]
    rw [this]; apply List.take_of_length_le; rw [hb', s1_post1]


attribute [local step] message_bytes_spec zeroed_spec as_mut_bytes_spec

theorem workspace_new_spec (g : feistel.Geometry) (hg : GeoOk g) (x : Slice Std.U8)
    (hx : x.length = 2 * g.half_bytes.val) :
    feistel.Workspace.new g x ⦃ w =>
      w.geometry = g ∧ WsInv w (x.val.take g.half_bytes.val) (x.val.drop g.half_bytes.val) ⦄ := by
  unfold feistel.Workspace.new
  have hg' := hg
  obtain ⟨h0, h1⟩ := hg'
  have hmb : mbOf g ≤ 32 := by simp only [mbOf]; split <;> omega
  simp only [engine.SALT_BYTES, engine.KEY_BYTES]
  step*
  · simp only [Slice.length, s_post, secretBytes, secret_post1, i4_post]
    simp; omega
  · -- the invariant of the new workspace
    simp only [Slice.length] at *
    have hsl : s.val.length = i4.val := by
      rw [s_post]; simp [secretBytes, secret_post1, i4_post]
    have hlen2 : (index_mut_back s2).val.length = s.val.length := by
      simp only [s1_post2, List.length_setSlice!]
    obtain ⟨hok, hl, hb⟩ := s_post1 _ hlen2
    have hval : (index_mut_back s2).val = x.val ++ s.val.drop x.val.length := by
      rw [s1_post2, s2_post]
      simp only [List.setSlice!, List.take_zero, List.nil_append, Nat.zero_add, Nat.sub_zero]
      rw [show min x.val.length s.val.length = x.val.length by omega]
      simp
    refine ⟨hg, hok, ?_, ?_, ?_⟩
    · simp only [hl, i4_post, wsLen]; omega
    · rw [hb, hval]; simp; omega
    · rw [hb, hval, List.drop_append_of_le_length (by omega : g.half_bytes.val ≤ x.val.length)]
      rw [List.take_append_of_le_length (by simp; omega)]
      rw [List.take_of_length_le (by simp; omega)]


theorem split_at_mut_ok {T : Type} (s : Slice T) (n : Std.Usize) (h : n.val ≤ s.val.length) :
    core.slice.Slice.split_at_mut s n ⦃ res back =>
      res.1.val = s.val.take n.val ∧ res.2.val = s.val.drop n.val ∧
      ∀ a b : Slice T, a.val.length = n.val → b.val.length = s.val.length - n.val →
        (back (a, b)).val = a.val ++ b.val ⦄ := by
  unfold core.slice.Slice.split_at_mut
  simp only [Slice.length] at *
  rw [dif_pos h]; simp only [WP.spec_ok]
  refine ⟨by simp, by simp, ?_⟩
  intro a b ha hb
  simp only [Slice.length, List.length_take, List.length_drop, ha, hb]
  simp [show min n.val s.val.length = n.val by omega]

theorem splitFirstChunk_ok {T : Type} (N : Std.Usize) (s : Slice T) (h : N.val ≤ s.val.length) :
    MhfeTranslation.splitFirstChunkMutExpect N s ⦃ res back =>
      res.1.val = s.val.take N.val ∧ res.2.val = s.val.drop N.val ∧
      ∀ a : Array T N, ∀ b : Slice T, b.val.length = s.val.length - N.val →
        (back (a, b)).val = a.val ++ b.val ⦄ := by
  unfold MhfeTranslation.splitFirstChunkMutExpect
  rw [dif_pos h]; simp only [WP.spec_ok]
  refine ⟨by simp, by simp, ?_⟩
  intro a b hb
  simp [hb]


/-- Parts of the right lengths for a workspace of geometry `g`. -/
def PartsOk (g : feistel.Geometry) (p : feistel.Parts) : Prop :=
  p.left.val.length = g.half_bytes.val ∧ p.right.val.length = g.half_bytes.val ∧
  p.message.val.length = mbOf g ∧ p.mask.val.length = g.half_bytes.val

/-- `Workspace::parts` gives the two halves, a message, a salt, a key and a mask of the right lengths,
and its backward function writes parts of these lengths back in place. -/
theorem parts_spec (w : feistel.Workspace) (l r : List Std.U8) (hw : WsInv w l r) :
    feistel.Workspace.parts w ⦃ p back =>
      p.left.val = l ∧ p.right.val = r ∧ PartsOk w.geometry p ∧
      ∀ p', PartsOk w.geometry p' → (back p').geometry = w.geometry ∧
        WsInv (back p') p'.left.val p'.right.val ⦄ := by
  obtain ⟨hg, hok, hlen, hl, hr⟩ := hw
  have hg' := hg
  obtain ⟨h0, h1⟩ := hg'
  have hmb : mbOf w.geometry ≤ 32 := by simp only [mbOf]; split <;> omega
  unfold feistel.Workspace.parts
  let* ⟨ s, back0, s_post, s_back ⟩ ← as_mut_bytes_spec
  have hsl : s.val.length = wsLen w.geometry := by
    rw [s_post]; simp [secretBytes, SecretOk] at hok ⊢; omega
  let* ⟨ left, rest1, back1, hleft, hrest1, hback1 ⟩ ← split_at_mut_ok
  · simp [wsLen] at hsl; omega
  let* ⟨ right, rest2, back2, hright, hrest2, hback2 ⟩ ← split_at_mut_ok
  · rw [hrest1]; simp [wsLen] at hsl ⊢; omega
  let* ⟨ mbv, mbv_post ⟩ ← message_bytes_spec
  let* ⟨ message, rest3, back3, hmsg, hrest3, hback3 ⟩ ← split_at_mut_ok
  · rw [hrest2, hrest1]; simp [wsLen] at hsl ⊢; omega
  let* ⟨ salt, rest4, back4, hsalt, hrest4, hback4 ⟩ ← splitFirstChunk_ok
  · rw [hrest3, hrest2, hrest1]; simp [wsLen] at hsl ⊢; omega
  let* ⟨ key, mask, back5, hkey, hmask, hback5 ⟩ ← splitFirstChunk_ok
  · rw [hrest4, hrest3, hrest2, hrest1]; simp [wsLen] at hsl ⊢; omega
  simp only [wsLen] at hsl
  have L1 : rest1.val.length = 2 * w.geometry.half_bytes.val + mbOf w.geometry + 48 := by
    rw [hrest1]; simp; omega
  have L2 : rest2.val.length = w.geometry.half_bytes.val + mbOf w.geometry + 48 := by
    rw [hrest2]; simp; omega
  have L3 : rest3.val.length = w.geometry.half_bytes.val + 48 := by
    rw [hrest3]; simp [mbv_post]; omega
  have L4 : rest4.val.length = w.geometry.half_bytes.val + 32 := by
    rw [hrest4]; simp; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hleft, s_post, hl]
  · rw [hright, hrest1, s_post, hr]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hleft]; simp; omega
    · rw [hright]; simp; omega
    · rw [hmsg]; simp [mbv_post]; omega
    · rw [hmask]; simp; omega
  · intro p' hp'
    obtain ⟨pl, pr, pm, pk⟩ := hp'
    have e5 := hback5 p'.key p'.mask (by rw [pk, L4]; omega)
    have e4 := hback4 p'.salt (back5 (p'.key, p'.mask)) (by rw [e5]; simp [L3, pk]; omega)
    have e3 := hback3 p'.message (back4 (p'.salt, back5 (p'.key, p'.mask)))
      (by rw [pm, mbv_post]) (by rw [e4, e5]; simp [L2, L3, pk, mbv_post]; omega)
    have e2 := hback2 p'.right (back3 (p'.message, back4 (p'.salt, back5 (p'.key, p'.mask))))
      (by rw [pr]) (by rw [e3, e4, e5]; simp [L1, pk, pm, mbv_post]; omega)
    have e1 := hback1 p'.left (back2 (p'.right, back3 (p'.message, back4 (p'.salt,
      back5 (p'.key, p'.mask))))) (by rw [pl]) (by rw [e2, e3, e4, e5]; simp [pk, pm, pr]; omega)
    have hlenb : (back1 (p'.left, back2 (p'.right, back3 (p'.message, back4 (p'.salt,
        back5 (p'.key, p'.mask)))))).length = s.length := by
      simp only [Slice.length]; rw [e1, e2, e3, e4, e5]; simp [pk, pm, pr, pl]; omega
    obtain ⟨bok, blen, bbytes⟩ := s_back _ hlenb
    refine ⟨hg, bok, ?_, ?_, ?_⟩
    · simp only; rw [blen, hlen]
    · simp only; rw [bbytes, e1]; simp [pl]
    · simp only; rw [bbytes, e1, e2]; simp [pl, pr]


/-- Writing at index `i` leaves the first `i` elements alone. -/
theorem take_setSlice!_self {α} (s s' : List α) (i : Nat) :
    (s.setSlice! i s').take i = s.take i := by
  simp only [List.setSlice!, List.append_assoc, List.take_append, List.take_take, Nat.min_self,
    List.length_take]
  by_cases hi : i ≤ s.length
  · simp [Nat.min_eq_left hi]
  · have : s.length - i = 0 := by omega
    simp [this]; omega

/-- Wiping a byte slice writes zeros. -/
theorem zeroize_slice_zero (s : Slice Std.U8) :
    Slice.Insts.ZeroizeZeroize.zeroize U8.Insts.ZeroizeDefaultIsZeroes s ⦃ r =>
      r.val = List.replicate s.length 0#u8 ∧ r.length = s.length ⦄ := by
  simp [Slice.Insts.ZeroizeZeroize.zeroize, U8.Insts.ZeroizeDefaultIsZeroes,
    core.default.DefaultU8, core.default.DefaultU8.default]
  right; rfl

/-- Writing `s` at index `i` over the end of `l` and dropping the first `i` elements leaves `s`. -/
theorem drop_setSlice!_end {α} (l s : List α) (i : Nat) (h : i + s.length = l.length) :
    (l.setSlice! i s).drop i = s := by
  have hn : min s.length (l.length - i) = s.length := by omega
  simp only [List.setSlice!, hn, List.take_length]
  rw [List.append_assoc, List.drop_left' (by simp; omega)]
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil]

attribute [-step] zeroize_slice_u8_spec
attribute [local step] zeroize_slice_zero

/-- A secret whose length is at most that of its pages (a truncated secret keeps its pages). -/
def SecretLe (s : protect.Secret) : Prop := s.len.val ≤ s.pages.bytes.length

/-- `Workspace::into_state` keeps the two halves alone and wipes the rest of the workspace: the
message, the salt, the key and the mask. -/
theorem into_state_spec (w : feistel.Workspace) (l r : List Std.U8) (hw : WsInv w l r) :
    feistel.Workspace.into_state w ⦃ s => secretBytes s = l ++ r ∧
      s.len.val = 2 * w.geometry.half_bytes.val ∧ SecretLe s ∧
      ∀ b ∈ s.pages.bytes.val.drop s.len.val, b = 0#u8 ⦄ := by
  obtain ⟨hg, hok, hlen, hl, hr⟩ := hw
  obtain ⟨h0, h1⟩ := hg
  unfold feistel.Workspace.into_state protect.Secret.truncate
  simp only [os.Pages.as_mut_slice]
  have hmb : mbOf w.geometry ≤ 32 := by simp only [mbOf]; split <;> omega
  have hlr : l ++ r = (secretBytes w.secret).take (2 * w.geometry.half_bytes.val) := by
    rw [← hl, ← hr, two_mul, ← List.take_add]
  simp only [SecretOk] at hok
  step*
  · simp only [Slice.length] at *; rw [s1_post2] at *
    refine ⟨?_, by rw [i_post], ?_, ?_⟩
    · simp only [Slice.setSlice!, Slice.from_val, List.length_setSlice!, ite_true, secretBytes]
      rw [hlr, i_post]
      simp only [take_setSlice!_self, secretBytes]
      rw [← hok, List.take_length]
    · simp only [SecretLe, Slice.length, Slice.setSlice!, Slice.from_val, List.length_setSlice!,
        ↓reduceIte]
      have := hlen; simp only [wsLen] at this; omega
    · intro b hb
      simp only [Slice.setSlice!, Slice.from_val, List.length_setSlice!, ↓reduceIte] at hb
      have hs2l : i.val + s2.val.length = w.secret.pages.bytes.val.length := by
        rw [s2_post]; simp only [List.length_replicate, Slice.length] at *; scalar_tac
      rw [drop_setSlice!_end _ _ _ hs2l, s2_post] at hb
      simp at hb; exact hb.2
  · exfalso; simp [wsLen] at hlen; scalar_tac

end MhfeProofs
