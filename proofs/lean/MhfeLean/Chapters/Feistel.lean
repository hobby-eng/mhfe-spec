import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Std
import MhfeLean.Chapters.LegacyPMF

namespace MhfeLean
noncomputable section

/-! # Consistency, uniformity and exact deniability
-/

/-! Finite probability tools shared by the subsequent MHFE formalizations. -/

namespace ProbabilityTools

/-- Independently sample two distributions and retain both values. -/
def independentPair (first : PMF α) (second : PMF β) : PMF (α × β) :=
  first.bind fun a => second.map fun b => (a, b)

/-- Independent pair probabilities are the product of their two point masses. -/
theorem independentPair_apply (first : PMF α) (second : PMF β) (a : α) (b : β) :
    independentPair first second (a, b) = first a * second b := by
  classical
  have tagged (chosen : α) :
      (second.map (fun value => (chosen, value))) (a, b) =
        if a = chosen then second b else 0 := by
    rw [PMF.map_apply]
    by_cases equal : a = chosen
    · subst chosen
      simpa only [Prod.mk.injEq, eq_self_iff_true, true_and, if_true, eq_comm] using
        (tsum_ite_eq b (fun value => second value))
    · simp only [Prod.mk.injEq, equal, false_and, if_false, tsum_zero]
  unfold independentPair
  rw [PMF.bind_apply]
  simp_rw [tagged, mul_ite, mul_zero]
  simpa only [eq_comm] using (tsum_ite_eq a (fun value => first value * second b))

/-- A bijection moves each point mass to its unique inverse image. -/
theorem equiv_apply {First Second : Type} (law : PMF First) (equiv : First ≃ Second)
    (value : Second) : (law.map equiv) value=law (equiv.symm value) := by
  classical
  letI : DecidableEq First := Classical.decEq First
  letI : DecidableEq Second := Classical.decEq Second
  rw [PMF.map_apply]
  have criterion (input : First) : value=equiv input ↔ input=equiv.symm value :=
    eq_comm.trans equiv.apply_eq_iff_eq_symm_apply
  simp_rw [criterion]
  simpa only [eq_comm] using (tsum_ite_eq (equiv.symm value) (fun input => law input))

/-- Uniform sampling from a product is the same as independent uniform sampling. -/
theorem uniform_product [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      independentPair (PMF.uniformOfFintype α) (PMF.uniformOfFintype β) := by
  ext pair
  rw [independentPair_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))

/-- The first projection of a uniform finite product is uniform. -/
theorem uniform_fst [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst = PMF.uniformOfFintype α := by
  rw [uniform_product]
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change ((PMF.uniformOfFintype α).bind fun a =>
    (PMF.uniformOfFintype β).map (Function.const β a)) = PMF.uniformOfFintype α
  simp only [PMF.map_const, PMF.bind_pure]

/-- One value of a uniformly random finite function is uniform. -/
theorem uniform_eval [DecidableEq α] [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (point : α) :
    (PMF.uniformOfFintype (α → β)).map (fun table => table point) =
      PMF.uniformOfFintype β := by
  let split := Equiv.funSplitAt point β
  have transported := PMF.uniformOfFintype_map_of_bijective split split.bijective
  calc
    (PMF.uniformOfFintype (α → β)).map (fun table => table point) =
        ((PMF.uniformOfFintype (α → β)).map split).map Prod.fst := by
      change (PMF.uniformOfFintype (α → β)).map (Prod.fst ∘ split) = _
      exact (PMF.map_comp split _ Prod.fst).symm
    _ = (PMF.uniformOfFintype (β × ({ index : α // index ≠ point } → β))).map
        Prod.fst := by rw [transported]
    _ = PMF.uniformOfFintype β := uniform_fst

end ProbabilityTools

/-!
# MHFE supplement: Lemma 2 (uniformity)

The input state is uniform and sampled independently of an arbitrary distribution
of permutations. The full joint law of the permutation and its output equals
that of the same permutation and a fresh independent uniform state.
-/

namespace Lemma2

variable {α : Type} [Fintype α] [Nonempty α]

/-- Any fixed permutation preserves the uniform distribution. -/
theorem uniform_permutation (permutation : Equiv.Perm α) :
    (PMF.uniformOfFintype α).map permutation = PMF.uniformOfFintype α :=
  PMF.uniformOfFintype_map_of_bijective permutation permutation.bijective

/-- Draw the permutation, independently draw a uniform state, then apply it. -/
def actualJoint (permutations : PMF (Equiv.Perm α)) : PMF (Equiv.Perm α × α) :=
  permutations.bind fun permutation =>
    (PMF.uniformOfFintype α).map fun state => (permutation, permutation state)

/-- Draw the same permutation together with an independent uniform output. -/
def independentJoint (permutations : PMF (Equiv.Perm α)) : PMF (Equiv.Perm α × α) :=
  permutations.bind fun permutation =>
    (PMF.uniformOfFintype α).map fun state => (permutation, state)

/-- Full joint equality proves independence, not only the output's marginal law. -/
theorem uniform_and_independent (permutations : PMF (Equiv.Perm α)) :
    actualJoint permutations = independentJoint permutations := by
  unfold actualJoint independentJoint
  congr 1
  funext permutation
  calc
    (PMF.uniformOfFintype α).map (fun state => (permutation, permutation state)) =
        ((PMF.uniformOfFintype α).map permutation).map (fun state => (permutation, state)) :=
      (PMF.map_comp _ _ _).symm
    _ = (PMF.uniformOfFintype α).map (fun state => (permutation, state)) := by
      rw [uniform_permutation]

/-- Forgetting the permutation leaves the uniform output distribution. -/
theorem output_uniform (permutations : PMF (Equiv.Perm α)) :
    (actualJoint permutations).map Prod.snd = PMF.uniformOfFintype α := by
  simp [actualJoint, PMF.map_bind, PMF.map_comp, Function.comp_def, uniform_permutation]

/-- Point probabilities factor into the permutation's mass and uniform state mass. -/
theorem joint_probability (permutations : PMF (Equiv.Perm α)) (permutation : Equiv.Perm α)
    (state : α) :
    actualJoint permutations (permutation, state) =
      permutations permutation * (Fintype.card α : ENNReal)⁻¹ := by
  rw [uniform_and_independent]
  change ProbabilityTools.independentPair permutations (PMF.uniformOfFintype α)
    (permutation,state) = _
  rw [ProbabilityTools.independentPair_apply,PMF.uniformOfFintype_apply]

/-- The specification's 256-bit state space has exactly 2^256 states. -/
theorem state256_probability (permutations : PMF (Equiv.Perm (Fin (2 ^ 256))))
    (permutation : Equiv.Perm (Fin (2 ^ 256))) (state : Fin (2 ^ 256)) :
    actualJoint permutations (permutation, state) =
      permutations permutation * ((2 : ENNReal) ^ 256)⁻¹ := by
  simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
    joint_probability permutations permutation state

/-- Each XOR translation is a permutation, even when its selector is a bit. -/
def xorPermutation (selector : Bool) : Equiv.Perm Bool where
  toFun value := selector ^^ value
  invFun value := selector ^^ value
  left_inv value := by cases selector <;> cases value <;> rfl
  right_inv value := by cases selector <;> cases value <;> rfl

/-- Without independence, choosing the XOR selector equal to the input gives a constant. -/
theorem dependence_counterexample :
    (PMF.uniformOfFintype Bool).map (fun bit => xorPermutation bit bit) = PMF.pure false := by
  have constant : (fun bit => xorPermutation bit bit) = (fun _ : Bool => false) := by
    funext bit
    cases bit <;> rfl
  rw [constant]
  exact PMF.map_const _ _

end Lemma2

/-! Exact deniability: retain the entire shared environment, disclosure, phrase and usage record. -/
namespace Theorem1
variable {State Password Environment Phrase Record : Type} [Fintype State] [Nonempty State]

/-- A full disclosure retains the environment (including functions), not only its output marginals. -/
abbrev View (Environment State Password Phrase Record : Type) := Environment × State × Password × State × Phrase × Record

variable (permutation : Environment → Password → Equiv.Perm State)
  (phrase : Environment → State → Phrase) (usage : Phrase → PMF Record) (environment : Environment)

def honestKernel (password : Password) : PMF (View Environment State Password Phrase Record) :=
  (PMF.uniformOfFintype State).bind fun source =>
    (usage (phrase environment source)).map fun record =>
      (environment,permutation environment password source,password,source,phrase environment source,record)

def preparedKernel (real disclosed : Password) : PMF (View Environment State Password Phrase Record) :=
  (PMF.uniformOfFintype State).bind fun source =>
    let container := permutation environment real source
    let decoy := (permutation environment disclosed).symm container
    (usage (phrase environment decoy)).map fun record =>
      (environment,container,disclosed,decoy,phrase environment decoy,record)

/-- Uniform reindexing applies to any subsequent randomized observation. -/
theorem uniform_bind {Output : Type} (permutation : Equiv.Perm State) (next : State → PMF Output) :
    (PMF.uniformOfFintype State).bind (fun state => next (permutation state)) =
      (PMF.uniformOfFintype State).bind next := by
  calc
    _ = ((PMF.uniformOfFintype State).map permutation).bind next := by
      simpa only [Function.comp_def] using (PMF.bind_map (PMF.uniformOfFintype State) permutation next).symm
    _ = _ := by rw [Lemma2.uniform_permutation]

/-- Exact fixed-environment identity, including the usage record. No random-function assumption is needed. -/
theorem kernel_eq (real disclosed : Password) :
    preparedKernel permutation phrase usage environment real disclosed =
      honestKernel permutation phrase usage environment disclosed := by
  let changeSource := (permutation environment real).trans (permutation environment disclosed).symm
  let observe := fun source : State =>
    (usage (phrase environment source)).map fun record =>
      (environment,permutation environment disclosed source,disclosed,source,phrase environment source,record)
  have container (source : State) : permutation environment disclosed (changeSource source) =
      permutation environment real source := by simp [changeSource]
  calc
    _ = (PMF.uniformOfFintype State).bind (fun source => observe (changeSource source)) := by
      apply congrArg (fun next => (PMF.uniformOfFintype State).bind next)
      funext source
      simp only [observe,changeSource,Equiv.trans_apply]
      rw [Equiv.apply_symm_apply]
    _ = _ := uniform_bind changeSource observe

/-- The full joint distribution, with independently drawn real and disclosed passwords. -/
theorem joint (environments : PMF Environment) (passwords : PMF Password)
    (permutation : Environment → Password → Equiv.Perm State)
    (phrase : Environment → State → Phrase) (usage : Phrase → PMF Record) :
    (environments.bind fun environment => passwords.bind fun real => passwords.bind fun disclosed =>
      preparedKernel permutation phrase usage environment real disclosed) =
    (environments.bind fun environment => passwords.bind fun disclosed =>
      honestKernel permutation phrase usage environment disclosed) := by
  simp_rw [kernel_eq]
  simp only [PMF.bind_const]

end Theorem1

/-!
# MHFE supplement: Lemma 1 (consistency)

The deterministic Feistel inverse is proved for arbitrary round masks. The BIP39
part models 24 words as 24 groups of 11 bits in most-significant-bit order and
checks the eight checksum bits after regrouping. The checksum is a parameter:
the result holds, in particular, when it is the first eight bits of SHA-256.
This file does not verify a SHA-256 implementation or a wordlist/parser.
-/

namespace Lemma1

/-- Two halves of the same width, in the specification's left/right order. -/
abbrev State (width : Nat) := BitVec width × BitVec width

variable (mask : BitVec width → BitVec width) (state : State width)

/-- One forward round, with its password/settings/index fixed in `mask`. -/
def forwardRound : State width :=
  (state.2, state.1 ^^^ mask state.2)

/-- The inverse uses the output's left half to recompute the same mask. -/
def backwardRound : State width :=
  (state.2 ^^^ mask state.1, state.1)

@[simp] theorem backward_forward
    (mask : BitVec width → BitVec width) (state : State width) :
    backwardRound mask (forwardRound mask state) = state := by
  rcases state with ⟨left, right⟩
  simp [backwardRound, forwardRound, BitVec.xor_assoc]

@[simp] theorem forward_backward
    (mask : BitVec width → BitVec width) (state : State width) :
    forwardRound mask (backwardRound mask state) = state := by
  rcases state with ⟨left, right⟩
  simp [backwardRound, forwardRound, BitVec.xor_assoc]

/-- Apply the masks in increasing round order. -/
def encrypt : List (BitVec width → BitVec width) → State width → State width
  | [], state => state
  | mask :: rest, state => encrypt rest (forwardRound mask state)

/-- Undo the last round first, then continue toward round zero. -/
def decrypt : List (BitVec width → BitVec width) → State width → State width
  | [], state => state
  | mask :: rest, state => backwardRound mask (decrypt rest state)

@[simp] theorem encrypt_decrypt
    (masks : List (BitVec width → BitVec width)) (state : State width) :
    encrypt masks (decrypt masks state) = state := by
  induction masks generalizing state with
  | nil => rfl
  | cons mask rest ih =>
    simp only [encrypt, decrypt, forward_backward, ih]

@[simp] theorem decrypt_encrypt
    (masks : List (BitVec width → BitVec width)) (state : State width) :
    decrypt masks (encrypt masks state) = state := by
  classical
  induction masks generalizing state <;> aesop (add simp [encrypt, decrypt, backward_forward])

-- Suite 3 has twelve rounds and two 128-bit halves.
abbrev Suite3Masks := Fin 12 → BitVec 128 → BitVec 128

def suite3Encrypt (masks : Suite3Masks) := encrypt (List.ofFn masks)
def suite3Decrypt (masks : Suite3Masks) := decrypt (List.ofFn masks)

/-- Bit strings below use the BIP39 most-significant-bit-first order. -/
abbrev Bits (size : Nat) := Fin size → Bool
abbrev Entropy := Bits 256
abbrev Checksum := Bits 8
abbrev Phrase24 := Fin 24 → Bits 11

/-- Concatenate 256 entropy bits and the eight BIP39 checksum bits. -/
def payload (entropy : Entropy) (checksum : Checksum) : Bits 264 :=
  fun index =>
    if h : index.val < 256 then entropy ⟨index.val, h⟩
    else checksum ⟨index.val - 256, by omega⟩

/-- Split all 264 bits into 24 consecutive 11-bit word indices. -/
def wordsOfBits (bits : Bits 264) : Phrase24 :=
  fun word bit => bits ⟨word.val * 11 + bit.val, by omega⟩

/-- Recombine the word-index bits before checking the checksum. -/
def bitsOfWords (words : Phrase24) : Bits 264 :=
  fun index => words ⟨index.val / 11, by omega⟩ ⟨index.val % 11, by omega⟩

@[simp] theorem bits_wordsOfBits (bits : Bits 264) :
    bitsOfWords (wordsOfBits bits) = bits := by
  funext index
  change bits ⟨index.val / 11 * 11 + index.val % 11, _⟩ = bits index
  apply congrArg bits
  apply Fin.ext
  exact Nat.div_add_mod' index.val 11

/-- Read the first 256 bits from the recombined 24-word phrase. -/
def readEntropy (phrase : Phrase24) : Entropy :=
  fun index => bitsOfWords phrase ⟨index.val, by omega⟩

/-- A phrase is valid when its last eight bits equal the checksum of its entropy. -/
def ValidPhrase24 (checksum : Entropy → Checksum) (phrase : Phrase24) : Prop :=
  ∀ bit : Fin 8,
    bitsOfWords phrase ⟨256 + bit.val, by omega⟩ = checksum (readEntropy phrase) bit

/-- Append the checksum and turn the resulting bits into word indices. -/
def encode24 (checksum : Entropy → Checksum) (entropy : Entropy) : Phrase24 :=
  wordsOfBits (payload entropy (checksum entropy))

@[simp] theorem read_encode24 (checksum : Entropy → Checksum) (entropy : Entropy) :
    readEntropy (encode24 checksum entropy) = entropy := by
  funext index
  simp [readEntropy, encode24, payload, index.isLt]

@[simp] theorem encode24_valid (checksum : Entropy → Checksum) (entropy : Entropy) :
    ValidPhrase24 checksum (encode24 checksum entropy) := by
  intro bit
  rw [read_encode24]
  simp only [encode24, bits_wordsOfBits]
  have outsideEntropy : ¬ 256 + bit.val < 256 := by omega
  simp [payload, outsideEntropy]

/-- Read both halves as the 256 entropy bits, left half first. -/
def stateEntropy (state : State 128) : Entropy :=
  fun bit => (state.1 ++ state.2).getMsbD bit.val

/-- The 24-word reading of a recovered state, with a freshly computed checksum. -/
def recoveredPhrase (masks : Suite3Masks) (checksum : Entropy → Checksum) (container : State 128) :
    Phrase24 :=
  encode24 checksum (stateEntropy (suite3Decrypt masks container))

/-- Lemma 1, for every fixed password and settings represented by `roundMasks`. -/
theorem consistency {Password : Type} (roundMasks : Password → Suite3Masks)
    (checksum : Entropy → Checksum) (password : Password) (container : State 128) :
    ValidPhrase24 checksum (recoveredPhrase (roundMasks password) checksum container) ∧
      suite3Encrypt (roundMasks password) (suite3Decrypt (roundMasks password) container) =
        container := by
  constructor
  · exact encode24_valid checksum _
  · exact encrypt_decrypt _ _

-- A relevant negative control: using the wrong half does not give an inverse.
private def wrongBackwardRound : State width :=
  (state.2 ^^^ mask state.2, state.1)

example : wrongBackwardRound id (forwardRound id ((1 : BitVec 1), (0 : BitVec 1))) ≠
    ((1 : BitVec 1), (0 : BitVec 1)) := by decide

end Lemma1

/-!
# MHFE supplement: Lemma 3 (one input, two rounds)

The first two round functions are independent uniform finite function tables.
The input is fixed. Later rounds are any independently sampled finite list of
round functions; their composition is a permutation by Lemma 1.
-/

namespace Lemma3

open Lemma1 ProbabilityTools

/-- The standard bit-vector representation enumerates all 2^width bit strings. -/
def bitEquivFin (width : Nat) : BitVec width ≃ Fin (2 ^ width) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv _ := rfl
  right_inv _ := rfl

local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (bitEquivFin width).symm

/-- XOR with a fixed half is its own inverse. -/
def xorPermutation (fixed : BitVec width) : Equiv.Perm (BitVec width) where
  toFun value := fixed ^^^ value
  invFun value := fixed ^^^ value
  left_inv value := by simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  right_inv value := by simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Evaluate one independent random round function and XOR a fixed value. -/
theorem random_mask (fixed point : BitVec width) :
    (PMF.uniformOfFintype (BitVec width → BitVec width)).map
        (fun table => fixed ^^^ table point) = PMF.uniformOfFintype (BitVec width) := by
  calc
    _ = ((PMF.uniformOfFintype (BitVec width → BitVec width)).map
        (fun table => table point)).map (xorPermutation fixed) :=
      (PMF.map_comp _ _ _).symm
    _ = (PMF.uniformOfFintype (BitVec width)).map (xorPermutation fixed) := by
      rw [uniform_eval]
    _ = PMF.uniformOfFintype (BitVec width) :=
      Lemma2.uniform_permutation _

/-- The actual two-round experiment samples complete, independent random functions. -/
def twoRoundGame (input : State width) : PMF (State width) :=
  (PMF.uniformOfFintype (BitVec width → BitVec width)).bind fun first =>
    (PMF.uniformOfFintype (BitVec width → BitVec width)).map fun second =>
      forwardRound second (forwardRound first input)

/-- The two output halves are jointly uniform, not merely uniform one at a time. -/
theorem twoRound_uniform (input : State width) :
    twoRoundGame input = PMF.uniformOfFintype (State width) := by
  have conditional (first : BitVec width → BitVec width) :
      (PMF.uniformOfFintype (BitVec width → BitVec width)).map
          (fun second => forwardRound second (forwardRound first input)) =
        (PMF.uniformOfFintype (BitVec width)).map
          (fun value => (input.1 ^^^ first input.2, value)) := by
    change (PMF.uniformOfFintype (BitVec width → BitVec width)).map
        (fun second => (input.1 ^^^ first input.2,
          input.2 ^^^ second (input.1 ^^^ first input.2))) = _
    rw [← random_mask input.2 (input.1 ^^^ first input.2)]
    exact (PMF.map_comp _ _ _).symm
  calc
    twoRoundGame input =
        (PMF.uniformOfFintype (BitVec width → BitVec width)).bind fun first =>
          (PMF.uniformOfFintype (BitVec width)).map
            (fun value => (input.1 ^^^ first input.2, value)) := by
      unfold twoRoundGame
      simp_rw [conditional]
    _ = ((PMF.uniformOfFintype (BitVec width → BitVec width)).map
          (fun first => input.1 ^^^ first input.2)).bind
          (fun left => (PMF.uniformOfFintype (BitVec width)).map
            (fun right => (left, right))) := by
      exact (PMF.bind_map
        (PMF.uniformOfFintype (BitVec width → BitVec width))
        (fun first => input.1 ^^^ first input.2)
        (fun left => (PMF.uniformOfFintype (BitVec width)).map
          (fun right => (left, right)))).symm
    _ = independentPair (PMF.uniformOfFintype (BitVec width))
          (PMF.uniformOfFintype (BitVec width)) := by
      rw [random_mask]
      rfl
    _ = PMF.uniformOfFintype (State width) := uniform_product.symm

/-- A finite sequence of later Feistel rounds is a permutation. -/
def laterPermutation (masks : List (BitVec width → BitVec width)) :
    Equiv.Perm (State width) where
  toFun := encrypt masks
  invFun := decrypt masks
  left_inv := decrypt_encrypt masks
  right_inv := encrypt_decrypt masks

/-- Later round functions are sampled independently of the first two. -/
def networkGame (input : State width) (later : PMF (List (BitVec width → BitVec width))) :
    PMF (State width) :=
  later.bind fun masks => (twoRoundGame input).map (encrypt masks)

/-- Lemma 3, allowing any independent distribution for the later round functions. -/
theorem network_uniform (input : State width) (later : PMF (List (BitVec width → BitVec width))) :
    networkGame input later = PMF.uniformOfFintype (State width) := by
  unfold networkGame
  simp_rw [twoRound_uniform]
  have preserved (masks : List (BitVec width → BitVec width)) :
      (PMF.uniformOfFintype (State width)).map (encrypt masks) =
        PMF.uniformOfFintype (State width) :=
    Lemma2.uniform_permutation (laterPermutation masks)
  simp_rw [preserved]
  exact PMF.bind_const _ _

/-- A uniformly sampled round-function vector is the independent two-round/suffix experiment. -/
theorem rounds_uniform (rest : Nat) (source : State width) :
    (PMF.uniformOfFintype (Fin (rest+2) → (BitVec width → BitVec width))).map
      (fun masks => encrypt (List.ofFn masks) source) = PMF.uniformOfFintype (State width) := by
  let split : ((BitVec width → BitVec width) × (BitVec width → BitVec width) ×
      (Fin rest → (BitVec width → BitVec width))) ≃ (Fin (rest+2) → (BitVec width → BitVec width)) :=
    (Equiv.prodCongr (Equiv.refl _) (Fin.consEquiv (fun _ : Fin (rest+1) => (BitVec width → BitVec width)))).trans
      (Fin.consEquiv (fun _ : Fin (rest+2) => (BitVec width → BitVec width)))
  have split_apply (seed : (BitVec width → BitVec width) × (BitVec width → BitVec width) ×
      (Fin rest → (BitVec width → BitVec width))) :
      split seed = Fin.cons seed.1 (Fin.cons seed.2.1 seed.2.2) := rfl
  have first_two (first second : BitVec width → BitVec width) (tail : Fin rest → (BitVec width → BitVec width)) :
      encrypt (List.ofFn (Fin.cons first (Fin.cons second tail))) source =
        encrypt (List.ofFn tail) (forwardRound second (forwardRound first source)) := by
    rw [List.ofFn_cons,List.ofFn_cons,encrypt,encrypt]
  have moved := PMF.uniformOfFintype_map_of_bijective split split.bijective
  rw [← moved,PMF.map_comp]
  conv_lhs => simp only [uniform_product,independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def,split_apply]
  simp only [first_two]
  have commute (first : (BitVec width → BitVec width)) :
      ((PMF.uniformOfFintype ((BitVec width → BitVec width))).bind fun second =>
        (PMF.uniformOfFintype (Fin rest → (BitVec width → BitVec width))).map fun rest =>
          encrypt (List.ofFn rest) (forwardRound second (forwardRound first source)))=
      (PMF.uniformOfFintype (Fin rest → (BitVec width → BitVec width))).bind fun rest =>
        (PMF.uniformOfFintype ((BitVec width → BitVec width))).map fun second =>
          encrypt (List.ofFn rest) (forwardRound second (forwardRound first source)) := PMF.bind_comm _ _ _
  simp_rw [commute]
  rw [PMF.bind_comm (PMF.uniformOfFintype ((BitVec width → BitVec width))) (PMF.uniformOfFintype (Fin rest → (BitVec width → BitVec width)))]
  have after (rest : Fin rest → (BitVec width → BitVec width)) :
      (PMF.uniformOfFintype ((BitVec width → BitVec width))).bind (fun first => (PMF.uniformOfFintype ((BitVec width → BitVec width))).map
        (fun second => encrypt (List.ofFn rest)
          (forwardRound second (forwardRound first source))))=
      PMF.uniformOfFintype (State width) := by
    have law := congrArg (fun distribution : PMF (State width) => distribution.map (encrypt (List.ofFn rest)))
      (Lemma3.twoRound_uniform source)
    have preserved : (PMF.uniformOfFintype (State width)).map (encrypt (List.ofFn rest))=
        PMF.uniformOfFintype (State width) :=
      Lemma2.uniform_permutation (Lemma3.laterPermutation (List.ofFn rest))
    simpa only [Lemma3.twoRoundGame,PMF.map_bind,PMF.map_comp,Function.comp_def] using law.trans preserved
  calc
    _ = (PMF.uniformOfFintype (Fin rest → (BitVec width → BitVec width))).bind (fun _ => PMF.uniformOfFintype (State width)) := by
      apply congrArg (fun next => (PMF.uniformOfFintype (Fin rest → (BitVec width → BitVec width))).bind next)
      funext rest
      exact after rest
    _ = _ := PMF.bind_const _ _

/-- Every complete output state has probability 1/2^(2*width). -/
theorem point_probability (input output : State width)
    (later : PMF (List (BitVec width → BitVec width))) :
    networkGame input later output = ((2 : ENNReal) ^ (width + width))⁻¹ := by
  have half_card : Fintype.card (BitVec width) = 2 ^ width :=
    (Fintype.card_congr (bitEquivFin width)).trans (Fintype.card_fin _)
  rw [network_uniform, PMF.uniformOfFintype_apply]
  change (Fintype.card (BitVec width × BitVec width) : ENNReal)⁻¹ = _
  rw [Fintype.card_prod, half_card, ← Nat.pow_add]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- Two inputs sharing the right half retain a relation after two rounds. -/
theorem shared_right_relation (first second : BitVec width → BitVec width)
    (left otherLeft right : BitVec width) :
    (forwardRound second (forwardRound first (left, right))).1 ^^^
        (forwardRound second (forwardRound first (otherLeft, right))).1 =
      left ^^^ otherLeft := by
  change (left ^^^ first right) ^^^ (otherLeft ^^^ first right) = left ^^^ otherLeft
  rw [BitVec.xor_assoc,
    ← BitVec.xor_assoc (first right) otherLeft (first right),
    BitVec.xor_comm (first right) otherLeft,
    BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

end Lemma3

/-! Instantiate exact deniability with actual twelve-round Feistel permutations at every state width. -/
namespace Theorem1Feistel
variable {Environment Password Phrase Record : Type} {width : Nat}
local instance (size : Nat) : Fintype (BitVec size) :=
  Fintype.ofEquiv (Fin (2^size)) (Lemma3.bitEquivFin size).symm

/-- The inverse is the proved Feistel decryption, not an assumed ideal cipher. -/
def cipher (masks : Fin 12 → BitVec width → BitVec width) : Equiv.Perm (Lemma1.State width) where
  toFun := Lemma1.encrypt (List.ofFn masks)
  invFun := Lemma1.decrypt (List.ofFn masks)
  left_inv := Lemma1.decrypt_encrypt _
  right_inv := Lemma1.encrypt_decrypt _

/-- Width 128 gives suite 3. Widths 64,80,96,112 give suite 4's 128,160,192,224-bit states.
All masks may depend on the retained shared environment and password. -/
theorem joint (environments : PMF Environment) (passwords : PMF Password)
    (masks : Environment → Password → Fin 12 → BitVec width → BitVec width)
    (phrase : Environment → Lemma1.State width → Phrase) (usage : Phrase → PMF Record) :
    (environments.bind fun environment => passwords.bind fun real => passwords.bind fun disclosed =>
      Theorem1.preparedKernel (fun environment password => cipher (masks environment password))
        phrase usage environment real disclosed) =
    (environments.bind fun environment => passwords.bind fun disclosed =>
      Theorem1.honestKernel (fun environment password => cipher (masks environment password))
        phrase usage environment disclosed) :=
  Theorem1.joint environments passwords _ phrase usage

end Theorem1Feistel

end
end MhfeLean
