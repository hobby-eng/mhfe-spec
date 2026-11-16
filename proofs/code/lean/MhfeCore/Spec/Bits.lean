import Aeneas
import MhfeCore.Spec.Spec

/-!
# Byte strings and bit vectors

The Lean model of the specification works with bit vectors (`BitVec w`), most significant bit
first as the specification reads its strings; the code works with bytes. `fromBytes n` reads a
string of `n` bytes as a vector of `8 n` bits, the first byte in the most significant position, and
`toBytes n` is its inverse. Both carry byte-wise XOR to the XOR of bit vectors.
-/

open Aeneas Aeneas.Std MhfeSpec

namespace MhfeBits

/-- The bytes of a bit vector of `8 n` bits, most significant byte first. -/
def toBytes (n : Nat) (v : BitVec (8 * n)) : Bytes :=
  List.ofFn fun i : Fin n => ⟨v.extractLsb' (8 * (n - 1 - i.val)) 8⟩

/-- The number a byte string denotes, first byte most significant. -/
def beNat : Bytes → Nat
  | [] => 0
  | x :: xs => x.val * 256 ^ xs.length + beNat xs

/-- The bit vector of a string of `n` bytes. -/
def fromBytes (n : Nat) (b : Bytes) : BitVec (8 * n) := BitVec.ofNat (8 * n) (beNat b)

theorem toBytes_length (n : Nat) (v : BitVec (8 * n)) : (toBytes n v).length = n := by
  simp [toBytes]

theorem toBytes_getElem (n : Nat) (v : BitVec (8 * n)) (i : Nat) (h : i < (toBytes n v).length) :
    (toBytes n v)[i] = ⟨v.extractLsb' (8 * (n - 1 - i)) 8⟩ := by
  simp [toBytes]

theorem xorBytes_length (a b : Bytes) : (xorBytes a b).length = min a.length b.length := by
  simp [xorBytes]

/-- `toBytes` carries XOR of bit vectors to XOR of bytes. -/
theorem toBytes_xor (n : Nat) (v w : BitVec (8 * n)) :
    toBytes n (v ^^^ w) = xorBytes (toBytes n v) (toBytes n w) := by
  apply List.ext_getElem
  · simp [toBytes_length, xorBytes_length]
  · intro i h1 h2
    simp only [toBytes_getElem, xorBytes, List.getElem_zipWith]
    show (⟨_⟩ : U8) = ⟨_ ^^^ _⟩
    congr 1
    ext j hj
    simp [BitVec.getElem_extractLsb']

theorem beNat_lt (b : Bytes) : beNat b < 256 ^ b.length := by
  induction b with
  | nil => simp [beNat]
  | cons x xs ih =>
    have hx : x.val < 256 := by have := x.hBounds; simpa using this
    simp only [beNat, List.length_cons, Nat.pow_succ]
    have : x.val * 256 ^ xs.length + beNat xs < (x.val + 1) * 256 ^ xs.length := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    calc _ < (x.val + 1) * 256 ^ xs.length := this
      _ ≤ 256 * 256 ^ xs.length := Nat.mul_le_mul_right _ (by omega)
      _ = 256 ^ xs.length * 256 := Nat.mul_comm _ _

/-- The byte at position `i` of `b` is `beNat b / 256^(|b|-1-i) mod 256`. -/
theorem beNat_byte (b : Bytes) (i : Nat) (h : i < b.length) :
    beNat b / 256 ^ (b.length - 1 - i) % 256 = b[i].val := by
  induction b generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    have hx : x.val < 256 := by have := x.hBounds; simpa using this
    have hr := beNat_lt xs
    cases i with
    | zero =>
      simp only [beNat, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)),
        Nat.div_eq_of_lt hr, Nat.zero_add, Nat.mod_eq_of_lt hx]
    | succ i =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
      have hs : xs.length + 1 - 1 - (i + 1) = xs.length - 1 - i := by omega
      simp only [beNat, List.length_cons, List.getElem_cons_succ, hs]
      have hpos : 0 < 256 ^ (xs.length - 1 - i) := Nat.pow_pos (by omega)
      have e : x.val * 256 ^ xs.length =
          (x.val * 256 ^ i * 256) * 256 ^ (xs.length - 1 - i) := by
        conv_lhs => rw [show xs.length = (xs.length - 1 - i) + (i + 1) by omega]
        rw [Nat.pow_add, Nat.pow_succ]; ring
      rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.add_mul_mod_self_right]
      exact ih i h

/-- `toBytes` undoes `fromBytes` on strings of `n` bytes. -/
theorem toBytes_fromBytes (n : Nat) (b : Bytes) (hb : b.length = n) :
    toBytes n (fromBytes n b) = b := by
  apply List.ext_getElem
  · simp [toBytes_length, hb]
  · intro i h1 h2
    rw [toBytes_getElem]
    have hi : i < n := by simpa [toBytes_length] using h1
    apply UScalar.val_eq_imp
    have hN : beNat b < 2 ^ (8 * n) := by
      have := beNat_lt b; rw [hb] at this; rwa [Nat.pow_mul] 
    show (BitVec.extractLsb' _ 8 (BitVec.ofNat (8 * n) (beNat b))).toNat = _
    rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, Nat.shiftRight_eq_div_pow,
      Nat.pow_mul, ← hb]
    exact beNat_byte b i (by omega)

end MhfeBits
