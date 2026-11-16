import MhfeCore.Code
import MhfeCore.Spec.Spec
import MhfeCore.Proofs.Models
import MhfeCore.Proofs.Bytes

/-!
# The round message in the code

`write_message` writes the settings through `[Some(MEM), Some(PIM), ENT, Some(i)].into_iter()
.flatten()`; the lemmas below compute that iterator.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- What `flatten` gives next from a list of options: its first `Some` value and the rest. -/
def flatNext : List (Option Std.U32) → Option Std.U32 × List (Option Std.U32)
  | [] => (none, [])
  | none :: t => flatNext t
  | some x :: t => (some x, t)

abbrev FlatIter := core.iter.adapters.flatten.Flatten (core.array.iter.IntoIter (Option Std.U32)
  4#usize) (Option Std.U32) Std.U32 (core.option.IntoIter Std.U32)

abbrev flatNextFn := core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next
  (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator (Option Std.U32) 4#usize)
  (core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter Std.U32)
  (core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator Std.U32)

/-- The state after a call: the rest of the outer list, and an empty inner iterator when a value
came out. -/
def flatState (l : List (Option Std.U32)) : FlatIter :=
  match flatNext l with
  | (some _, t) => ⟨⟨t⟩, some ⟨none⟩⟩
  | (none, _) => ⟨⟨[]⟩, none⟩

theorem flatten_next_none (l : List (Option Std.U32)) :
    flatNextFn ⟨⟨l⟩, none⟩ = ok ((flatNext l).1, flatState l) := by
  simp only [flatNextFn, core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator,
    core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
    core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter,
    core.option.Option.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator,
    core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next]
  induction l with
  | nil =>
    rw [loop.eq_1]
    simp [flatNext, flatState]
  | cons o t ih =>
    rw [loop.eq_1]
    cases o with
    | none =>
      simp
      rw [loop.eq_1]
      simpa [flatNext, flatState] using ih
    | some x =>
      simp
      rw [loop.eq_1]
      simp [flatNext, flatState]

theorem flatten_next_some_none (l : List (Option Std.U32)) :
    flatNextFn ⟨⟨l⟩, some ⟨none⟩⟩ = ok ((flatNext l).1, flatState l) := by
  have h := flatten_next_none l
  simp only [flatNextFn, core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next,
    core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator,
    core.option.IntoIter.Insts.CoreIterTraitsIteratorIterator.next] at h ⊢
  rw [loop.eq_1]
  simpa using h

theorem take_setSlice {α : Type} (l s : List α) (i : Nat) (h : i + s.length ≤ l.length) :
    (l.setSlice! i s).take (i + s.length) = l.take i ++ s := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    simp only [List.getElem_take, List.getElem_append]
    split_ifs with hn
    · simp_lists
    · simp_lists
      simp [show min i l.length = i by omega]

theorem drop_setSlice {α : Type} (l s : List α) (i j : Nat) (hj : i + s.length ≤ j)
    (h : i + s.length ≤ l.length) : (l.setSlice! i s).drop j = l.drop j := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_drop]
    simp_lists

/-- The bytes that the loop writes: `BE32` of every value, in order. -/
def be32All (l : List (Option Std.U32)) : List Std.U8 :=
  (l.filterMap id).flatMap fun v => MhfeSpec.be32 v.val

theorem be32_length (n : Nat) : (MhfeSpec.be32 n).length = 4 := by simp [MhfeSpec.be32]

theorem be32All_length (l : List (Option Std.U32)) :
    (be32All l).length = 4 * (l.filterMap id).length := by
  simp only [be32All, List.length_flatMap, be32_length]
  induction (l.filterMap id) with
  | nil => simp
  | cons a t ih => simp [ih]; ring

theorem write_message_loop_spec (l : List (Option Std.U32)) (f : Option (core.option.IntoIter Std.U32))
    (hf : f = none ∨ f = some ⟨none⟩) (m : Slice Std.U8) (at0 : Std.Usize)
    (h : at0.val + 4 * (l.filterMap id).length ≤ m.length) :
    feistel.write_message_loop ⟨⟨l⟩, f⟩ m at0 ⦃ m' at' =>
      at'.val = at0.val + 4 * (l.filterMap id).length ∧
      m'.val = m.val.take at0.val ++ be32All l ++ m.val.drop at'.val ⦄ := by
  have hnext : flatNextFn ⟨⟨l⟩, f⟩ = ok ((flatNext l).1, flatState l) := by
    rcases hf with rfl | rfl
    · exact flatten_next_none _
    · exact flatten_next_some_none _
  simp only [flatNextFn] at hnext
  induction l generalizing f m at0 with
  | nil =>
    unfold feistel.write_message_loop
    rw [hnext]
    simp [flatNext, be32All]
  | cons o t ih =>
    cases o with
    | none =>
      unfold feistel.write_message_loop
      rw [hnext]
      have h2 := flatten_next_none t
      simp only [flatNextFn] at h2
      have := ih none (Or.inl rfl) m at0 (by simpa using h) h2
      unfold feistel.write_message_loop at this
      rw [h2] at this
      simpa [flatNext, flatState, be32All] using this
    | some x =>
      unfold feistel.write_message_loop
      rw [hnext]
      simp only [flatNext, flatState, bind_tc_ok]
      have hm := m.property
      have h' : at0.val + 4 * ((t.filterMap id).length + 1) ≤ m.length := by
        simpa using h
      clear h
      have hbe : (x.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)) = MhfeSpec.be32 x.val :=
        to_be_bytes_be32 x
      have hlen : (MhfeSpec.be32 x.val).length = 4 := by simp [MhfeSpec.be32]
      simp only [feistel.BE32_BYTES] at *
      simp only [step_simps]
      let* ⟨ i, i_post ⟩ ← Usize.add_spec.step_spec
      let* ⟨ s, index_mut_back, s_post, s_post1, s_post2 ⟩ ←
        core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
      let* ⟨ a, a_post ⟩ ← core.num.U32.to_be_bytes.step_spec
      let* ⟨ s1, s1_post ⟩ ← Array.to_slice.step_spec
      let* ⟨ s2, s2_post ⟩ ← core.slice.Slice.copy_from_slice.step_spec
      let* ⟨ m', at', m'_post, m'_post1 ⟩ ← ih
      · have := flatten_next_some_none t; simpa [flatNextFn] using this
      · have hs2 : s2.val = MhfeSpec.be32 x.val := by
          rw [s2_post, s1_post, Array.val_to_slice, a_post, hbe]
        refine ⟨by rw [m'_post, i_post]; simp; ring, ?_⟩
        rw [m'_post1, s_post2]
        simp only [Slice.setSlice!, Slice.from_val, hs2]
        have e1 := take_setSlice m.val (MhfeSpec.be32 x.val) at0.val (by rw [hlen]; scalar_tac)
        have e2 := drop_setSlice m.val (MhfeSpec.be32 x.val) at0.val at'.val
          (by rw [hlen, m'_post, i_post]; scalar_tac) (by rw [hlen]; scalar_tac)
        rw [hlen] at e1
        rw [i_post, e1, e2]
        simp [be32All]


theorem setSlice_append_end {α : Type} (b d r : List α) (h : d.length = r.length) :
    (b ++ d).setSlice! b.length r = b ++ r := by
  simp [List.setSlice!, h]

/-- The settings that `write_message` writes, as the specification lists them. -/
theorem be32All_settings (mem pim round : Std.U32) (ent : Option Std.U32) :
    be32All [some mem, some pim, ent, some round] =
      MhfeSpec.be32 mem.val ++ MhfeSpec.be32 pim.val ++
        (match ent.map (·.val) with | some e => MhfeSpec.be32 e | none => []) ++
        MhfeSpec.be32 round.val := by
  cases ent <;> simp [be32All]

/-- `write_message` writes `BE32(MEM) || BE32(PIM) || [BE32(ENT)] || BE32(i) || R` when the message
buffer has exactly that length. -/
theorem write_message_spec (msg : Slice Std.U8) (g : feistel.Geometry) (w : suite.WorkFactor)
    (round : Std.U32) (r : Slice Std.U8)
    (hlen : msg.length = (be32All [some w.memory_level, some w.pim, g.entropy_bits, some round]).length
      + r.length) :
    feistel.write_message msg g w round r ⦃ m =>
      m.val = MhfeSpec.message w.memory_level.val w.pim.val (g.entropy_bits.map (·.val)) round.val
        r.val ⦄ := by
  unfold feistel.write_message
  simp only [suite.WorkFactor.impl.memory_level, suite.WorkFactor.impl.pim,
    Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.iter.traits.iterator.Iterator.flatten.default, bind_tc_ok, Array.make_val]
  have hm := msg.property
  have hb := be32All_length [some w.memory_level, some w.pim, g.entropy_bits, some round]
  rw [hb] at hlen
  let* ⟨ m1, at1, h1, h2 ⟩ ← write_message_loop_spec
  rw [← hb] at h1 hlen
  simp only [Nat.zero_add, List.take_zero, List.nil_append] at h1 h2
  step*
  · rw [s_post1]; simp only [Slice.length] at *; simp [h2]; omega
  · simp only [Slice.length] at *
    rw [s_post2, s1_post, h2, h1]
    have hd : (List.drop (be32All [some w.memory_level, some w.pim, g.entropy_bits, some round]).length
        msg.val).length = r.val.length := by simp; omega
    rw [setSlice_append_end _ _ _ hd, be32All_settings]
    simp only [MhfeSpec.message, List.append_assoc]
    cases g.entropy_bits <;> rfl

end MhfeProofs
