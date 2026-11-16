import MhfeCore.Spec.Bridge
import MhfeLean.Chapters.DeniabilityModel
import MhfeLean.Chapters.ShortSources

/-!
# The byte-level permutation is the cipher of the security model

The security proofs of the Lean model use ideal tables `a` (Argon2id), `b` (salt) and `h` (mask),
and the round mask `mask i R = h (a (P, b (i, R)), i, R)`. With the tables instantiated by the
primitives of the specification, the byte-level `perm` and `permInv` are the model's cipher and its
inverse, in both models: the width-parametric model of the deniability theorems
(`DeniabilityModel`, suites 3 and 4) and the fixed-width model of the guessing theorems of suite 3
(`KnownPairModel`, `Gamma2Model`).
-/

open Aeneas Aeneas.Std MhfeSpec MhfeBits MhfeBridge MhfeLean

namespace MhfeModelLink

/-- The primitives return 32 bytes, as their types in the code do. -/
structure Primitives.WellFormed (F : Primitives) : Prop where
  blake2b256 : ∀ m, (F.blake2b256 m).length = 32
  hmacSha256 : ∀ k m, (F.hmacSha256 k m).length = 32
  argon2id : ∀ p s m t, (F.argon2id p s m t).length = 32

variable (F : Primitives) (c : Setting)

/-- The salt table: `b (i, R) = Trunc_128(BLAKE2b-256(DS_SALT || message(i, R)))`. -/
def tableB (h : Nat) : Fin 12 × BitVec (8 * h) → BitVec 128 :=
  fun (i, r) => fromBytes 16 (roundSalt F c.suite (message c.mem c.pim (c.suite.ent c.words) i
    (toBytes h r)))

/-- The Argon2id table: `a (P, S) = Argon2id(P, S)` at the setting's memory and passes. -/
def tableA : Bytes × BitVec 128 → BitVec 256 :=
  fun (p, s) => fromBytes 32 (F.argon2id p (toBytes 16 s) (memoryKiB c.mem) (passes c.pim))

/-- The mask table: `h (K, i, R) = Trunc_h(HMAC-SHA-256(K, DS_MASK || message(i, R)))`. -/
def tableH (h : Nat) : BitVec 256 × Fin 12 × BitVec (8 * h) → BitVec (8 * h) :=
  fun (k, i, r) => fromBytes h (roundMaskOfKey F c.suite h (toBytes 32 k)
    (message c.mem c.pim (c.suite.ent c.words) i (toBytes h r)))

theorem roundSalt_length (hF : Primitives.WellFormed F) (s : Suite) (m : Bytes) :
    (roundSalt F s m).length = 16 := by
  simp [roundSalt, hF.blake2b256]

theorem roundMask_length (hF : Primitives.WellFormed F) (hh : c.half ≤ 32) (i : Nat) (r : Bytes) :
    (roundMask F c i r).length = c.half := by
  simp [roundMask, roundMaskOfKey, hF.hmacSha256]; omega

/-- The model's round mask with the instantiated tables is the specification's `RoundMask`. -/
theorem modelMask_eq (hF : Primitives.WellFormed F) (i : Fin 12) (r : BitVec (8 * c.half)) :
    DeniabilityModel.mask c.password (tableA F c) (tableB F c c.half) (tableH F c c.half) i r =
      bvMask c.half (roundMask F c i) r := by
  simp only [DeniabilityModel.mask, tableA, tableB, tableH, bvMask, roundMask, Setting.half,
    toBytes_fromBytes 16 _ (roundSalt_length F hF _ _),
    toBytes_fromBytes 32 _ (hF.argon2id _ _ _ _)]

/-- The model's mask list with the instantiated tables. -/
theorem modelMasks_eq (hF : Primitives.WellFormed F) :
    List.ofFn (DeniabilityModel.mask c.password (tableA F c) (tableB F c c.half)
      (tableH F c c.half)) = List.ofFn fun i : Fin 12 => bvMask c.half (roundMask F c i) := by
  congr 1
  funext i
  funext r
  exact modelMask_eq F c hF i r

theorem cipher_apply (v : Lemma1.State (8 * c.half)) :
    DeniabilityModel.cipher c.password (tableA F c) (tableB F c c.half) (tableH F c c.half) v =
      Lemma1.encrypt (List.ofFn (DeniabilityModel.mask c.password (tableA F c)
        (tableB F c c.half) (tableH F c c.half))) v := rfl

theorem cipher_symm_apply (v : Lemma1.State (8 * c.half)) :
    (DeniabilityModel.cipher c.password (tableA F c) (tableB F c c.half) (tableH F c c.half)).symm
      v = Lemma1.decrypt (List.ofFn (DeniabilityModel.mask c.password (tableA F c)
        (tableB F c c.half) (tableH F c c.half))) v := rfl

/-- `Perm` of the specification is the cipher of the deniability model, for both suites. -/
theorem perm_eq_deniabilityCipher (hF : Primitives.WellFormed F) (hh : c.half ≤ 32)
    (v : Lemma1.State (8 * c.half)) :
    perm F c (toBytes c.half v.1 ++ toBytes c.half v.2) =
      let w := DeniabilityModel.cipher c.password (tableA F c) (tableB F c c.half)
        (tableH F c c.half) v
      toBytes c.half w.1 ++ toBytes c.half w.2 := by
  have hl : ∀ u : BitVec (8 * c.half), (toBytes c.half u).length = c.half := toBytes_length _
  have h12 := forwardRounds_bytes c.half (roundMask F c)
    (fun i r => roundMask_length F c hF hh i r) 12 v
  simp only [halvesOf] at h12
  rw [cipher_apply, modelMasks_eq F c hF]
  simp only [perm, rounds, List.take_left' (hl _), List.drop_left' (hl _), h12]

/-- `Perm^-1` of the specification is the inverse of the cipher of the deniability model. -/
theorem permInv_eq_deniabilityCipher (hF : Primitives.WellFormed F) (hh : c.half ≤ 32)
    (v : Lemma1.State (8 * c.half)) :
    permInv F c (toBytes c.half v.1 ++ toBytes c.half v.2) =
      let w := (DeniabilityModel.cipher c.password (tableA F c) (tableB F c c.half)
        (tableH F c c.half)).symm v
      toBytes c.half w.1 ++ toBytes c.half w.2 := by
  have hl : ∀ u : BitVec (8 * c.half), (toBytes c.half u).length = c.half := toBytes_length _
  have h12 := backwardRounds_bytes c.half (roundMask F c)
    (fun i r => roundMask_length F c hF hh i r) 12 v
  simp only [halvesOf] at h12
  rw [cipher_symm_apply, modelMasks_eq F c hF]
  simp only [permInv, rounds, List.take_left' (hl _), List.drop_left' (hl _), h12]

/-! ## Suite 3 in the model of the guessing theorems

The guessing theorems of suite 3 (Theorems 3 to 5) use the fixed-width model `Gamma2Model`, whose
cipher is `KnownPairModel.cipher` and whose recovery is the oracle program `Gamma2Model.finalize`. -/

/-- `Perm` of suite 3 is `KnownPairModel.cipher` with the instantiated tables. -/
theorem perm_eq_knownPairCipher (hF : Primitives.WellFormed F) (words pim mem : Nat)
    (password : Bytes) (v : Gamma2Model.State) :
    let c : Setting := ⟨.three, words, pim, mem, password⟩
    perm F c (toBytes 16 v.1 ++ toBytes 16 v.2) =
      let w := KnownPairModel.cipher password (tableA F c) (tableB F c 16) (tableH F c 16) v
      toBytes 16 w.1 ++ toBytes 16 w.2 :=
  perm_eq_deniabilityCipher F ⟨.three, words, pim, mem, password⟩ hF (by simp [Setting.half, Suite.halfBytes]) v

/-- `Perm^-1` of suite 3 is the recovery program `Gamma2Model.finalize` of the guessing theorems,
run on the instantiated tables (the verifier table `g` plays no part in it). -/
theorem permInv_eq_finalize (hF : Primitives.WellFormed F) (words pim mem : Nat)
    (password : Bytes) {Entropy : Type} (g : Entropy → Gamma2Model.Hash) (v : Gamma2Model.State) :
    let c : Setting := ⟨.three, words, pim, mem, password⟩
    let T : Gamma2Model.Tables Bytes Entropy := ⟨tableA F c, tableB F c 16, tableH F c 16, g⟩
    permInv F c (toBytes 16 v.1 ++ toBytes 16 v.2) =
      let w := (Gamma2Model.execute T (Gamma2Model.finalize password 12 v le_rfl)).1.1
      toBytes 16 w.1 ++ toBytes 16 w.2 := by
  intro c T
  rw [CipherExecution.finalize_decrypt]
  exact permInv_eq_deniabilityCipher F c hF (by simp [c, Setting.half, Suite.halfBytes]) v

end MhfeModelLink
