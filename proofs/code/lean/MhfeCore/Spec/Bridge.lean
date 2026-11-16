import MhfeCore.Spec.Spec
import MhfeCore.Spec.Bits
import MhfeLean.Chapters.Feistel

/-!
# The byte-level permutation is the Feistel network of the Lean model

`Lemma1.encrypt` and `Lemma1.decrypt` of the Lean model (chapter `Feistel`) are the twelve-round
network on two halves of `w` bits with arbitrary round masks. This file shows that the byte-level
`MhfeSpec.perm` and `MhfeSpec.permInv` are these functions, read through `toBytes`, for masks of the
right length.
-/

open Aeneas Aeneas.Std MhfeSpec MhfeBits MhfeLean

namespace MhfeBridge

/-- The model's mask for the byte-level mask `m`, on halves of `h` bytes. -/
def bvMask (h : Nat) (m : Bytes → Bytes) : BitVec (8 * h) → BitVec (8 * h) :=
  fun r => fromBytes h (m (toBytes h r))

/-- A state of the model as two byte halves. -/
def halvesOf (h : Nat) (v : Lemma1.State (8 * h)) : Bytes × Bytes := (toBytes h v.1, toBytes h v.2)

theorem encrypt_append {w : Nat} (l₁ l₂ : List (BitVec w → BitVec w)) (st : Lemma1.State w) :
    Lemma1.encrypt (l₁ ++ l₂) st = Lemma1.encrypt l₂ (Lemma1.encrypt l₁ st) := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons m rest ih => simp only [List.cons_append, Lemma1.encrypt, ih]

theorem decrypt_append {w : Nat} (l₁ l₂ : List (BitVec w → BitVec w)) (st : Lemma1.State w) :
    Lemma1.decrypt (l₁ ++ l₂) st = Lemma1.decrypt l₁ (Lemma1.decrypt l₂ st) := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons m rest ih => simp only [List.cons_append, Lemma1.decrypt, ih]

/-- One forward round commutes with the reading of the state as bytes. -/
theorem forwardRound_bytes (h : Nat) (m : Bytes → Bytes) (hm : ∀ r, (m r).length = h)
    (v : Lemma1.State (8 * h)) :
    forwardRound m (halvesOf h v) = halvesOf h (Lemma1.forwardRound (bvMask h m) v) := by
  simp only [forwardRound, halvesOf, Lemma1.forwardRound, bvMask, toBytes_xor,
    toBytes_fromBytes h _ (hm _)]

/-- One inverse round commutes with the reading of the state as bytes. -/
theorem backwardRound_bytes (h : Nat) (m : Bytes → Bytes) (hm : ∀ r, (m r).length = h)
    (v : Lemma1.State (8 * h)) :
    backwardRound m (halvesOf h v) = halvesOf h (Lemma1.backwardRound (bvMask h m) v) := by
  simp only [backwardRound, halvesOf, Lemma1.backwardRound, bvMask, toBytes_xor,
    toBytes_fromBytes h _ (hm _)]

/-- `n` forward rounds are `Lemma1.encrypt` with the masks of rounds `0, ..., n-1`. -/
theorem forwardRounds_bytes (h : Nat) (m : Nat → Bytes → Bytes) (hm : ∀ i r, (m i r).length = h)
    (n : Nat) (v : Lemma1.State (8 * h)) :
    forwardRounds m n (halvesOf h v) =
      halvesOf h (Lemma1.encrypt (List.ofFn fun i : Fin n => bvMask h (m i)) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [forwardRounds, ih, List.ofFn_succ_last, encrypt_append, forwardRound_bytes h _ (hm n)]
    rfl

/-- `n` inverse rounds are `Lemma1.decrypt` with the masks of rounds `0, ..., n-1`. -/
theorem backwardRounds_bytes (h : Nat) (m : Nat → Bytes → Bytes) (hm : ∀ i r, (m i r).length = h)
    (n : Nat) (v : Lemma1.State (8 * h)) :
    backwardRounds m n (halvesOf h v) =
      halvesOf h (Lemma1.decrypt (List.ofFn fun i : Fin n => bvMask h (m i)) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [backwardRounds, backwardRound_bytes h _ (hm n), ih, List.ofFn_succ_last, decrypt_append]
    rfl

end MhfeBridge
