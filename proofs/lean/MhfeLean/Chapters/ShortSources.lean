/- long: source resampling, completed-chain counting and Theorem 3 are developed together. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import MhfeLean.Chapters.ChainCompletion
import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.Probability
import ToMathlib.Control.WriterT
import VCVio.OracleComp.SimSemantics.SimulateQ

namespace MhfeLean
noncomputable section

/-! # Theorem 3 and G6: password and source recovery
-/

/-!
W1: compress the distinct password ranks of an arbitrary pair set into the
first m global ranks. top2 is the supremum of masses of at most n products in
those first m rows. The variational bound permits any passphrase alphabet;
finite alphabets additionally have a maximizing set of products.
-/
namespace W1
open Finset
variable {N : Nat} {Passphrase : Type} [DecidableEq Passphrase]

def mass (p : Fin N → ENNReal) (s : Passphrase → ENNReal) (pairs : Finset (Fin N × Passphrase)) :
    ENNReal :=
  ∑ pair ∈ pairs, p pair.1 * s pair.2

def top2 (p : Fin N → ENNReal) (s : Passphrase → ENNReal) (m n : Nat) : ENNReal :=
  ⨆ pairs : Finset (Fin N × Passphrase), ⨆ (_ : pairs.card ≤ n),
    ⨆ (_ : ∀ pair ∈ pairs, pair.1.val < m), mass p s pairs

theorem index_lower {k : Nat} (f : Fin k ↪o Fin N) (i : Fin k) : i.val ≤ (f i).val := by
  have lower : ∀ j, ∀ h : j < k, j ≤ (f ⟨j, h⟩).val := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro h
      have previous := ih (by omega)
      have increasing := f.strictMono (show (⟨j, by omega⟩ : Fin k) < ⟨j + 1, h⟩ from by change j < j + 1; omega)
      change (f ⟨j, by omega⟩).val < (f ⟨j + 1, h⟩).val at increasing
      omega
  exact lower i.val i.isLt

def rank (rows : Finset (Fin N)) (row : rows) : Fin rows.card := (rows.orderIsoOfFin rfl).symm row

theorem rank_le (rows : Finset (Fin N)) (row : rows) : (rank rows row).val ≤ row.val.val := by
  have bound := index_lower (rows.orderEmbOfFin rfl) (rank rows row)
  have same : rows.orderEmbOfFin rfl (rank rows row) = row.val := by
    rw [← Finset.coe_orderIsoOfFin_apply]
    exact congrArg Subtype.val ((rows.orderIsoOfFin rfl).apply_symm_apply row)
  rw [same] at bound
  exact bound

/-- W1 for finite normalized password ranks and any passphrase domain. -/
theorem lemma_w1 (p : Fin N → ENNReal) (s : Passphrase → ENNReal) (sorted : Antitone p)
    (pairs : Finset (Fin N × Passphrase)) (m n : Nat) (rowBound : (pairs.image Prod.fst).card ≤ m)
    (pairBound : pairs.card ≤ n) : mass p s pairs ≤ top2 p s m n := by
  classical
  let rows := pairs.image Prod.fst
  have size : rows.card ≤ N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ rows)
  let chosenRow : {pair // pair ∈ pairs} → rows := fun pair =>
    ⟨pair.val.1, Finset.mem_image.mpr ⟨pair.val, pair.property, rfl⟩⟩
  let compressed : {pair // pair ∈ pairs} → Fin N × Passphrase := fun pair =>
    (⟨(rank rows (chosenRow pair)).val, lt_of_lt_of_le (rank rows (chosenRow pair)).isLt size⟩, pair.val.2)
  have injective : Function.Injective compressed := by
    intro first second equal
    have rankEq : rank rows (chosenRow first) = rank rows (chosenRow second) :=
      Fin.ext (congrArg (fun pair : Fin N × Passphrase => pair.1.val) equal)
    have rowEq : first.val.1 = second.val.1 := by
      exact congrArg (fun row : rows => row.val) ((rows.orderIsoOfFin rfl).symm.injective rankEq)
    apply Subtype.ext
    apply Prod.ext rowEq
    simpa only [compressed] using congrArg Prod.snd equal
  let candidates := pairs.attach.image compressed
  have count : candidates.card ≤ n := by
    exact (Finset.card_image_le).trans (by simpa only [Finset.card_attach] using pairBound)
  have restricted : ∀ pair ∈ candidates, pair.1.val < m := by
    intro pair member
    obtain ⟨original, _, equal⟩ := Finset.mem_image.mp member
    rw [← equal]
    exact lt_of_lt_of_le (rank rows (chosenRow original)).isLt rowBound
  have dominates : mass p s pairs ≤ mass p s candidates := by
    unfold mass
    rw [show candidates = pairs.attach.image compressed from rfl, Finset.sum_image]
    · rw [← Finset.sum_attach pairs (fun pair => p pair.1 * s pair.2)]
      apply Finset.sum_le_sum
      intro pair _
      apply mul_le_mul_left
      apply sorted
      change (rank rows (chosenRow pair)).val ≤ pair.val.1.val
      exact rank_le rows (chosenRow pair)
    · intro a _ b _ same
      exact injective same
  exact dominates.trans (le_iSup_of_le candidates (le_iSup_of_le count (le_iSup_of_le restricted le_rfl)))

/-- On finite alphabets the variational top is attained by an actual set of products. -/
theorem top2_attained [Fintype Passphrase] (p : Fin N → ENNReal) (s : Passphrase → ENNReal)
    (m n : Nat) :
    ∃ pairs : Finset (Fin N × Passphrase), pairs.card ≤ n ∧
      (∀ pair ∈ pairs, pair.1.val < m) ∧ mass p s pairs = top2 p s m n := by
  classical
  let family := (Finset.univ : Finset (Finset (Fin N × Passphrase))).filter fun pairs =>
    pairs.card ≤ n ∧ ∀ pair ∈ pairs, pair.1.val < m
  have nonempty : family.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [family, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_empty, zero_le]
    intro pair member
    exact False.elim (Finset.notMem_empty pair member)
  obtain ⟨pairs, member, largest⟩ := Finset.exists_max_image family (mass p s) nonempty
  have valid := (Finset.mem_filter.mp member).2
  refine ⟨pairs, valid.1, valid.2, le_antisymm ?_ ?_⟩
  · exact le_iSup_of_le pairs (le_iSup_of_le valid.1 (le_iSup_of_le valid.2 le_rfl))
  · apply iSup_le
    intro other
    apply iSup_le
    intro count
    apply iSup_le
    intro rows
    exact largest other (Finset.mem_filter.mpr ⟨Finset.mem_univ _, count, rows⟩)

end W1

/-! Sorted password masses and exact finite-set probability accounting. -/
namespace RankedMass
open GameExpectation MomentTools ProbabilityTools
variable {N : Nat}

def top (p : Fin N → ENNReal) (m : Nat) : ENNReal :=
  ∑ index ∈ Finset.univ.filter (fun index : Fin N => index.val < m), p index

/-- Any m selected passwords have no more mass than the m most likely passwords. -/
theorem set_bound (p : Fin N → ENNReal) (sorted : Antitone p) (chosen : Finset (Fin N)) (m : Nat)
    (bounded : chosen.card ≤ m) : (∑ password ∈ chosen,p password) ≤ top p m := by
  classical
  have size : chosen.card ≤ N := by simpa using Finset.card_le_card (Finset.subset_univ chosen)
  let compress : chosen → Fin N := fun password =>
    ⟨(W1.rank chosen password).val,lt_of_lt_of_le (W1.rank chosen password).isLt size⟩
  have injective : Function.Injective compress := by
    intro first second equal
    have ranks : W1.rank chosen first = W1.rank chosen second := Fin.ext (congrArg (fun value : Fin N => value.val) equal)
    exact (chosen.orderIsoOfFin rfl).symm.injective ranks
  let compressed := chosen.attach.image compress
  have included : compressed ⊆ Finset.univ.filter (fun index : Fin N => index.val < m) := by
    intro password member
    obtain ⟨original,_,equal⟩ := Finset.mem_image.mp member
    rw [← equal]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le (W1.rank chosen original).isLt bounded⟩
  calc
    _ ≤ ∑ password ∈ compressed,p password := by
      rw [show compressed = chosen.attach.image compress from rfl,Finset.sum_image]
      · rw [← Finset.sum_attach chosen p]
        apply Finset.sum_le_sum
        intro password _
        exact sorted (W1.rank_le chosen password)
      · intro first _ second _ equal
        exact injective equal
    _ ≤ _ := Finset.sum_le_sum_of_subset included

/-- Expectation of membership is exactly the set's probability mass. -/
theorem membership_mass (passwords : PMF (Fin N)) (chosen : Finset (Fin N)) :
    moment passwords (fun password => if password ∈ chosen then 1 else 0) = ∑ password ∈ chosen,passwords password := by
  classical
  simp only [moment,tsum_fintype,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  simp

/-- The selected set may be fully adaptive to the run, provided that run is independent of P. -/
theorem independent_set_bound {View : Type} (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (views : PMF View) (chosen : View → Finset (Fin N)) (m : Nat)
    (bounded : ∀ view,(chosen view).card ≤ m) :
    moment (independentPair passwords views) (fun selected => if selected.1 ∈ chosen selected.2 then 1 else 0) ≤ top passwords m := by
  classical
  have reverse : independentPair passwords views = views.bind fun view => passwords.map fun password => (password,view) := by
    exact PMF.bind_comm _ _ _
  rw [reverse,MomentTools.bind]
  apply MomentTools.bounded
  intro view
  rw [moment_map]
  change moment passwords (fun password => if password ∈ chosen view then 1 else 0) ≤ _
  rw [membership_mass]
  exact set_bound passwords sorted (chosen view) m (bounded view)

end RankedMass

/-! Whole-chain candidate counting uses actual query multiplicities for every password. -/
namespace CompletedPasswords
open Gamma2Model QueryCounts
variable {N : Nat} {Entropy : Type}

def chosen (queries : List (Point (Fin N) Entropy)) : Finset (Fin N) :=
  Finset.univ.filter fun password => 12 ≤ queries.countP (aFor password)

/-- Every selected password consumes twelve of the actual expensive calls. -/
theorem count (queries : List (Point (Fin N) Entropy)) (kA : Nat) (budget : queries.countP isA ≤ kA) :
    (chosen queries).card ≤ kA/12 := by
  classical
  have paid : 12*(chosen queries).card ≤ kA := by
    calc
      _ = ∑ _ ∈ chosen queries,12 := by simp [Nat.mul_comm]
      _ ≤ ∑ password ∈ chosen queries,queries.countP (aFor password) := by
        apply Finset.sum_le_sum
        intro password member
        exact (Finset.mem_filter.mp member).2
      _ ≤ ∑ password,queries.countP (aFor password) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = queries.countP isA := a_partition queries
      _ ≤ _ := budget
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

/-- Include a final password guess without assuming that its chain was completed. -/
theorem with_guess (queries : List (Point (Fin N) Entropy)) (guess : Fin N) (kA : Nat)
    (budget : queries.countP isA ≤ kA) : (insert guess (chosen queries)).card ≤ kA/12+1 := by
  exact (Finset.card_insert_le _ _).trans (by have := count queries kA budget; omega)

end CompletedPasswords

/-! The full Gamma2 event assembly with the ranked-password main term. -/
namespace Theorem3Assembly
open Gamma2Model G2 G4Order QueryCounts
open GameExpectation MomentTools CompletedPasswords
variable {N : Nat} {Entropy : Type} [DecidableEq Entropy] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

def winOrBad (source : State → Entropy) (out : Outcome (Fin N) Entropy (Fin N)) : Bool := by
  classical
  exact decide (out.result = out.password ∨ Point.g (source out.recovered) ∈ out.adversaryQueries)

def mainTest (out : Outcome (Fin N) Entropy (Fin N)) : Bool :=
  decide (out.password ∈ insert out.result (chosen out.adversaryQueries))

omit [Fintype Entropy] in
/-- Exact deterministic inclusion. A complete real chain needs twelve actual A calls. -/
theorem covered (source : State → Entropy) (password : Fin N) (container : State)
    (tables : Tables (Fin N) Entropy)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N))
    (hit : winOrBad source (outcome password container tables adversary) = true) :
    mainTest (outcome password container tables adversary) = true ∨
      G3Sums.earlyTest (outcome password container tables adversary) = true ∨
      G4.sourceTest source (outcome password container tables adversary) = true := by
  classical
  have details : (outcome password container tables adversary).result = password ∨
      Point.g (source (outcome password container tables adversary).recovered) ∈
        (outcome password container tables adversary).adversaryQueries := of_decide_eq_true hit
  by_cases early : Early (chronologicalRun password container tables adversary)
  · exact Or.inr (Or.inl (decide_eq_true early))
  · by_cases complete : Complete (chronologicalRun password container tables adversary)
    · apply Or.inl
      apply decide_eq_true
      apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,G5.twelve_queries password container tables adversary early complete⟩
    · rcases details with win | bad
      · apply Or.inl
        apply decide_eq_true
        rw [← win]
        exact Finset.mem_insert_self _ _
      · exact Or.inr (Or.inr (decide_eq_true ⟨bad,complete,early⟩))

/-- The final guess and adaptively selected complete chains are independent of the real password in Gamma2. -/
theorem main_bound (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N)) (kA : Nat)
    (budget : ∀ container tables,(execute tables (adversary container)).2.countP isA ≤ kA) :
    ((game passwords adversary).map mainTest) true ≤ RankedMass.top passwords (kA/12+1) := by
  classical
  rw [probability,game_as_input_map,moment_map]
  simpa only [Function.comp_def,mainTest,decide_eq_true_eq,outcome] using
    RankedMass.independent_set_bound passwords sorted (inputsLaw adversary)
    (fun inputs => insert (execute inputs.2 (adversary inputs.1)).1 (chosen (execute inputs.2 (adversary inputs.1)).2))
    (kA/12+1) (fun inputs => with_guess _ _ kA (budget inputs.1 inputs.2))

/-- This is the exact final bound in Gamma2 before the G1/programming transfer back to Gamma0. -/
theorem bound (source : State → Entropy) (firstHalf : Entropy → Half)
    (projects : ∀ state,firstHalf (source state) = state.1) (passwords : PMF (Fin N))
    (sorted : Antitone passwords) (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N))
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP isH ≤ qH)
    (budgetG : ∀ container tables,(execute tables (adversary container)).2.countP G4Programs.isG ≤ qG) :
    ((game passwords adversary).map (winOrBad source)) true ≤
      RankedMass.top passwords (kA/12+1) +
      (qG+qB+12*p1*kA+66)/(2^128 : ENNReal) + qH/(2^256 : ENNReal) := by
  classical
  have pointwise := fun password container tables => covered source password container tables adversary
  have included : ((game passwords adversary).map (winOrBad source)) true ≤
      ((game passwords adversary).map mainTest) true +
      ((game passwords adversary).map G3Sums.earlyTest) true +
      ((game passwords adversary).map (G4.sourceTest source)) true := by
    rw [probability,probability,probability,probability,← MomentTools.add,← MomentTools.add]
    apply G3Assembly.game_pointwise
    intro password container tables
    by_cases hit : winOrBad source (outcome password container tables adversary) = true
    · rcases pointwise password container tables hit with h | h | h <;> simp only [hit, h] <;>
        first | exact le_self_add.trans le_self_add | exact le_add_self.trans le_self_add | exact le_add_self
    · simp [hit]
  have estimate := add_le_add
    (add_le_add (main_bound passwords sorted adversary kA budgetA)
      (G3Assembly.lemma_g3 passwords adversary p1 largest kA qB qH budgetA budgetB budgetH))
    (G4.lemma_g4_source source firstHalf projects passwords adversary qG budgetG)
  apply included.trans
  apply estimate.trans_eq
  simp only [ENNReal.add_div]
  abel

end Theorem3Assembly

/-!
# MHFE supplement: Lemma G1 (exact re-sampling)

Entropy E, the verifier prefix V and the unused hash suffix R are arbitrary
nonempty finite types. The state is E x V and a hash table maps E to V x R.
A bijection swaps the selected hash prefix with fresh verifier randomness.
The proof preserves the whole hash table and any independent environment.
-/

namespace G1

open ProbabilityTools

abbrev Table (E V R : Type) := E → V × R

variable {E V R : Type} [DecidableEq E]

/-- Exchange the selected hash prefix with an extra fresh verifier value. -/
def swapPoint : ((E × Table E V R) × V) ≃ ((E × V) × Table E V R) where
  toFun seed :=
    let entropy := seed.1.1
    let table := seed.1.2
    ((entropy, (table entropy).1),
      Function.update table entropy (seed.2, (table entropy).2))
  invFun output :=
    let entropy := output.1.1
    let table := output.2
    ((entropy, Function.update table entropy (output.1.2, (table entropy).2)),
      (table entropy).1)
  left_inv := by
    rintro ⟨⟨entropy, table⟩, extra⟩
    simp
  right_inv := by
    rintro ⟨⟨entropy, verifier⟩, table⟩
    simp

/-- Apply the fixed cipher permutation after swapping the free verifier bits. -/
def resamplingEquiv (permutation : Equiv.Perm (E × V)) :
    ((E × Table E V R) × V) ≃ ((E × V) × Table E V R) :=
  swapPoint.trans (Equiv.prodCongr permutation (Equiv.refl _))

/-- The original game encrypts entropy packed with its hash verifier. -/
def originalObservation (permutation : Equiv.Perm (E × V)) (seed : E × Table E V R) :
    (E × V) × Table E V R :=
  (permutation (seed.1, (seed.2 seed.1).1), seed.2)

/-- The re-sampled game programs only the prefix at the inverse image's entropy. -/
def programmedObservation (permutation : Equiv.Perm (E × V)) (seed : (E × V) × Table E V R) :
    (E × V) × Table E V R :=
  let state := permutation.symm seed.1
  (seed.1, Function.update seed.2 state.1 (state.2, (seed.2 state.1).2))

/-- Under the coupling, both games expose exactly the same container and table. -/
theorem observations_agree (permutation : Equiv.Perm (E × V)) (seed : (E × Table E V R) × V) :
    programmedObservation permutation (resamplingEquiv permutation seed) =
      originalObservation permutation seed.1 := by
  rcases seed with ⟨⟨entropy, table⟩, extra⟩
  simp [programmedObservation, originalObservation, resamplingEquiv, swapPoint]

variable [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]

/-- Uniform product sampling is independent uniform entropy and uniform hash table. -/
def originalGame (permutation : Equiv.Perm (E × V)) : PMF ((E × V) × Table E V R) :=
  (PMF.uniformOfFintype (E × Table E V R)).map (originalObservation permutation)

/-- The other game independently draws a uniform container and uniform fresh table. -/
def programmedGame (permutation : Equiv.Perm (E × V)) : PMF ((E × V) × Table E V R) :=
  (PMF.uniformOfFintype ((E × V) × Table E V R)).map (programmedObservation permutation)

/-- Exact equality of the conditional joint laws, including the complete hash table. -/
theorem resampling_fixed (permutation : Equiv.Perm (E × V)) : programmedGame (R := R) permutation = originalGame permutation := by
  have transported := PMF.uniformOfFintype_map_of_bijective
    (resamplingEquiv (R := R) permutation) (resamplingEquiv permutation).bijective
  calc
    programmedGame permutation =
        ((PMF.uniformOfFintype ((E × Table E V R) × V)).map
          (resamplingEquiv permutation)).map (programmedObservation permutation) := by
      rw [transported]
      rfl
    _ = (PMF.uniformOfFintype ((E × Table E V R) × V)).map
          (programmedObservation permutation ∘ resamplingEquiv permutation) :=
      PMF.map_comp _ _ _
    _ = (PMF.uniformOfFintype ((E × Table E V R) × V)).map
          (fun seed => originalObservation permutation seed.1) := by
      congr 1
      funext seed
      exact observations_agree permutation seed
    _ = ((PMF.uniformOfFintype ((E × Table E V R) × V)).map Prod.fst).map
          (originalObservation permutation) := by
      exact (PMF.map_comp Prod.fst _ (originalObservation permutation)).symm
    _ = originalGame permutation := by
      rw [uniform_fst]
      rfl

/-- Retain any independent environment, including password and other oracle tables. -/
def originalFull (environment : PMF Context) (cipher : Context → Equiv.Perm (E × V)) :
    PMF (Context × ((E × V) × Table E V R)) :=
  environment.bind fun context =>
    (originalGame (R := R) (cipher context)).map fun result => (context, result)

def programmedFull (environment : PMF Context) (cipher : Context → Equiv.Perm (E × V)) :
    PMF (Context × ((E × V) × Table E V R)) :=
  environment.bind fun context =>
    (programmedGame (R := R) (cipher context)).map fun result => (context, result)

/-- Lemma G1: the password, other oracles, container and programmed hash agree jointly. -/
theorem joint_resampling (environment : PMF Context) (cipher : Context → Equiv.Perm (E × V)) :
    originalFull (R := R) environment cipher = programmedFull environment cipher := by
  unfold originalFull programmedFull
  simp_rw [resampling_fixed]

end G1

/-! G1 transported to the actual cipher state and hash-bit coordinates. -/
namespace CoordinateResampling
variable {E V R S H : Type} [DecidableEq E]

def hashTable (hash : H ≃ (V × R)) : G1.Table E V R ≃ (E → H) where
  toFun table entropy := hash.symm (table entropy)
  invFun table entropy := hash (table entropy)
  left_inv := by intro table; funext entropy; simp
  right_inv := by intro table; funext entropy; simp

def coordinateCipher (state : (E × V) ≃ S) (cipher : Equiv.Perm S) : Equiv.Perm (E × V) :=
  state.trans (cipher.trans state.symm)

def view (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (output : (E × V) × G1.Table E V R) :
    S × (E → H) :=
  (state output.1,hashTable (E := E) hash output.2)

def original (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S) (seed : E × (E → H)) :
    S × (E → H) :=
  (cipher (state (seed.1,(hash (seed.2 seed.1)).1)),seed.2)

def programmed (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S)
    (seed : S × (E → H)) : S × (E → H) :=
  let recovered := state.symm (cipher.symm seed.1)
  (seed.1,Function.update seed.2 recovered.1 (hash.symm (recovered.2,(hash (seed.2 recovered.1)).2)))

theorem transport_update (hash : H ≃ (V × R)) (table : G1.Table E V R) (entropy : E) (value : V × R) :
    hashTable (E := E) hash (Function.update table entropy value) = Function.update (hashTable (E := E) hash table) entropy (hash.symm value) := by
  funext point
  by_cases same : point = entropy <;> simp [hashTable,Function.update,same]

omit [DecidableEq E] in
theorem original_agrees (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S)
    (seed : E × G1.Table E V R) :
    view state hash (G1.originalObservation (coordinateCipher state cipher) seed) =
      original state hash cipher ((Equiv.prodCongr (Equiv.refl E) (hashTable (E := E) hash)) seed) := by
  simp [view,G1.originalObservation,coordinateCipher,original,hashTable]

theorem programmed_agrees (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S)
    (seed : (E × V) × G1.Table E V R) :
    view state hash (G1.programmedObservation (coordinateCipher state cipher) seed) =
      programmed state hash cipher ((Equiv.prodCongr state (hashTable (E := E) hash)) seed) := by
  simp only [view,G1.programmedObservation,coordinateCipher,programmed,Equiv.prodCongr_apply]
  rw [transport_update]
  simp [hashTable]

variable [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
  [Fintype S] [Nonempty S] [Fintype H] [Nonempty H]

/-- The entire actual Y,G pair has the same distribution before and after re-sampling. -/
theorem fixed (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S) :
    (PMF.uniformOfFintype (E × (E → H))).map (original state hash cipher) =
      (PMF.uniformOfFintype (S × (E → H))).map (programmed state hash cipher) := by
  have originalTransport := PMF.uniformOfFintype_map_of_bijective
    (Equiv.prodCongr (Equiv.refl E) (hashTable (E := E) hash)) (Equiv.prodCongr (Equiv.refl E) (hashTable (E := E) hash)).bijective
  have programmedTransport := PMF.uniformOfFintype_map_of_bijective
    (Equiv.prodCongr state (hashTable (E := E) hash)) (Equiv.prodCongr state (hashTable (E := E) hash)).bijective
  calc
    _ = (G1.originalGame (R := R) (coordinateCipher state cipher)).map (view state hash) := by
      rw [← originalTransport,PMF.map_comp]
      unfold G1.originalGame
      rw [PMF.map_comp]
      congr 1
      funext seed
      exact (original_agrees state hash cipher seed).symm
    _ = (G1.programmedGame (R := R) (coordinateCipher state cipher)).map (view state hash) := by
      rw [G1.resampling_fixed]
    _ = _ := by
      rw [← programmedTransport]
      unfold G1.programmedGame
      rw [PMF.map_comp,PMF.map_comp]
      congr 1
      funext seed
      exact programmed_agrees state hash cipher seed

end CoordinateResampling

/-! The actual Gamma2 game regrouped with the independent G table last. -/
namespace CryptoInputs
open Gamma2Model TableFactors ProbabilityTools
variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype
abbrev ABH (Password : Type) := ATable Password × BTable × HTable

def tables (other : ABH Password) (g : GTable Entropy) : Tables Password Entropy :=
  ⟨other.1,other.2.1,other.2.2,g⟩

def pack : (ABH Password × GTable Entropy) ≃ Tables Password Entropy where
  toFun selected := tables selected.1 selected.2
  invFun selected := ((selected.a,selected.b,selected.h),selected.g)
  left_inv := by rintro ⟨⟨a,b,h⟩,g⟩; rfl
  right_inv := by intro selected; cases selected; rfl

theorem factor_g : sampleTables (Password := Password) (Entropy := Entropy) =
    (PMF.uniformOfFintype (ABH Password)).bind fun other =>
      (PMF.uniformOfFintype (GTable Entropy)).map (tables other) :=
  sample_factor pack

/-- All randomness remains independent; this only changes the order of draws. -/
theorem game (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    Gamma2Model.game passwords adversary =
      passwords.bind fun password => (PMF.uniformOfFintype (ABH Password)).bind fun other =>
        (PMF.uniformOfFintype (State × GTable Entropy)).map fun seed =>
          outcome password seed.1 (tables other seed.2) adversary := by
  have seeds (password : Password) (other : ABH Password) :
      ((PMF.uniformOfFintype (State × GTable Entropy)).map fun seed =>
        outcome password seed.1 (tables other seed.2) adversary) =
      (PMF.uniformOfFintype State).bind fun container =>
        (PMF.uniformOfFintype (GTable Entropy)).map fun g => outcome password container (tables other g) adversary := by
    rw [uniform_product]
    simp only [independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def]
  unfold Gamma2Model.game
  simp_rw [factor_g,PMF.map_bind,PMF.map_comp,Function.comp_def,seeds]
  apply congrArg (fun next => passwords.bind next)
  funext password
  exact PMF.bind_comm _ _ _

end CryptoInputs

/-!
Re-sampling two path masks inside one full oracle table. Structural hypotheses
say the two selected rounds do not overlap and their replacement leaves the
other rounds unchanged. These hypotheses must be instantiated, not assumed as
cryptographic independence, before applying this helper to K1.
-/
namespace PathResampling
open Gamma2Model ProbabilityTools
variable {Domain Context : Type} [DecidableEq Domain]

structure System (Domain Context : Type) [DecidableEq Domain] where
  rest : (Domain → Half) → Context
  first : Context → Domain
  second : Context → Half → Domain
  input : Context → State
  suffix : Context → Equiv.Perm State
  apart : ∀ context left, first context ≠ second context left
  keepFirst : ∀ table value, rest (Function.update table (first (rest table)) value) = rest table
  keepSecond : ∀ table left value,
    rest (Function.update table (second (rest table) left) value) = rest table

variable (system : System Domain Context)

variable (table : Domain → Half) (left firstValue secondValue : Half)

def replace : Domain → Half :=
  Function.update (Function.update table (system.first (system.rest table)) firstValue)
    (system.second (system.rest table) left) secondValue

theorem rest_replace :
    system.rest (replace system table left firstValue secondValue) = system.rest table := by
  unfold replace
  have stable := system.keepSecond
    (Function.update table (system.first (system.rest table)) firstValue) left secondValue
  rw [system.keepFirst] at stable
  exact stable

theorem replace_first :
    replace system table left firstValue secondValue (system.first (system.rest table)) = firstValue := by
  simp only [replace, Function.update_of_ne (system.apart _ _), Function.update_self]

theorem replace_second :
    replace system table left firstValue secondValue (system.second (system.rest table) left) = secondValue := by
  simp only [replace, Function.update_self]

theorem replace_twice (table : Domain → Half) (left a b c d : Half) :
    replace system (replace system table left a b) left c d = replace system table left c d := by
  rw [replace]
  simp only [rest_replace]
  funext query
  by_cases secondHit : query = system.second (system.rest table) left
  · simp [replace, Function.update, secondHit]
  · by_cases firstHit : query = system.first (system.rest table)
    · simp [replace, Function.update, firstHit]
    · simp [replace, Function.update, secondHit, firstHit]

theorem replace_original (table : Domain → Half) (left : Half) :
    replace system table left (table (system.first (system.rest table)))
      (table (system.second (system.rest table) left)) = table := by
  simp only [replace, Function.update_eq_self]

def middle (table : Domain → Half) : State :=
  let context := system.rest table
  let input := system.input context
  let left := input.1 ^^^ table (system.first context)
  (left, input.2 ^^^ table (system.second context left))

def output (table : Domain → Half) : State :=
  system.suffix (system.rest table) (middle system table)

def restore (value : State × (Domain → Half)) : Domain → Half :=
  let context := system.rest value.2
  let target := (system.suffix context).symm value.1
  let input := system.input context
  replace system value.2 target.1 (input.1 ^^^ target.1) (input.2 ^^^ target.2)

/-- The complete table is retained; only two selected outputs are exchanged with dummy masks. -/
def exchange : ((Domain → Half) × State) ≃ (State × (Domain → Half)) where
  toFun seed := (output system seed.1, replace system seed.1 (middle system seed.1).1 seed.2.1 seed.2.2)
  invFun value :=
    let context := system.rest value.2
    let target := (system.suffix context).symm value.1
    (restore system value, value.2 (system.first context), value.2 (system.second context target.1))
  left_inv := by
    rintro ⟨table, ⟨firstValue, secondValue⟩⟩
    dsimp only
    simp only [rest_replace, output, Equiv.symm_apply_apply, restore]
    have firstMask : (system.input (system.rest table)).1 ^^^ (middle system table).1 =
        table (system.first (system.rest table)) := by simp [middle]
    have secondMask : (system.input (system.rest table)).2 ^^^ (middle system table).2 =
        table (system.second (system.rest table) (middle system table).1) := by simp [middle]
    simp only [firstMask, secondMask, replace_twice, replace_original, replace_first, replace_second]
  right_inv := by
    rintro ⟨target, table⟩
    let context := system.rest table
    let mid := (system.suffix context).symm target
    have selected : middle system (restore system (target, table)) = mid := by
      simp [restore, middle, rest_replace, replace_first, replace_second, mid, context]
    dsimp only
    apply Prod.ext
    · change system.suffix (system.rest (restore system (target, table)))
        (middle system (restore system (target, table))) = target
      have stable : system.rest (restore system (target, table)) = system.rest table := by
        simp only [restore, rest_replace]
      rw [stable, selected]
      exact Equiv.apply_symm_apply _ _
    · change replace system (restore system (target, table))
        (middle system (restore system (target, table))).1
        (table (system.first context)) (table (system.second context mid.1)) = table
      rw [selected]
      change replace system
        (replace system table mid.1 ((system.input context).1 ^^^ mid.1)
          ((system.input context).2 ^^^ mid.2))
        mid.1 (table (system.first context)) (table (system.second context mid.1)) = table
      rw [replace_twice]
      exact replace_original system table mid.1

end PathResampling

/-! Pure fixed-known-pair model used by the exact K1 re-sampling proof. -/
namespace KnownPairModel
open Gamma2Model TableFactors
variable {Password : Type}
abbrev HInput := Key × Fin 12 × Half

def mask (password : Password) (a : ATable Password) (b : BTable) (h : HTable) (round : Fin 12)
    (right : Half) : Half := h (a (password, b (round, right)), round, right)

def allMasks (password : Password) (a : ATable Password) (b : BTable) (h : HTable) :=
  List.ofFn (fun round : Fin 12 => mask password a b h round)

variable (selected : Fin 11) (password : Password) (a : ATable Password) (b : BTable) (h : HTable)

def beforeMasks :=
  List.ofFn (fun round : Fin selected.val => mask password a b h ⟨round.val, by have := round.isLt; have := selected.isLt; omega⟩)

def afterMasks :=
  List.ofFn (fun round : Fin (10 - selected.val) => mask password a b h
    ⟨selected.val + 2 + round.val, by have := round.isLt; have := selected.isLt; omega⟩)

def roundsEquiv (masks : List (Half → Half)) : Equiv.Perm State where
  toFun := Lemma1.encrypt masks
  invFun := Lemma1.decrypt masks
  left_inv := Lemma1.decrypt_encrypt masks
  right_inv := Lemma1.encrypt_decrypt masks

def cipher (password : Password) (a : ATable Password) (b : BTable) (h : HTable) (source : State) :
    State :=
  Lemma1.encrypt (allMasks password a b h) source

/-- The full table at every H point outside the two selected round indices. -/
abbrev OtherInput (selected : Fin 11) :=
  { query : HInput // query.2.1 ≠ selected.castSucc ∧ query.2.1 ≠ selected.succ }
abbrev Rest (selected : Fin 11) := OtherInput selected → Half

def restrict (selected : Fin 11) (h : HTable) : Rest selected := fun query => h query.val

/-- Filling unused selected-round points with zero is only a way to evaluate the other rounds. -/
def fill (selected : Fin 11) (rest : Rest selected) : HTable := fun query =>
  if outside : query.2.1 ≠ selected.castSucc ∧ query.2.1 ≠ selected.succ
  then rest ⟨query, outside⟩ else 0

theorem mask_fill (round : Fin 12) (outside : round ≠ selected.castSucc ∧ round ≠ selected.succ) :
    mask password a b (fill selected (restrict selected h)) round = mask password a b h round := by
  funext right
  simp only [mask, fill]
  rw [dif_pos outside]
  rfl

/-- Only rounds before j are used to reach W_j. -/
theorem before_fill :
    beforeMasks selected password a b (fill selected (restrict selected h)) = beforeMasks selected password a b h := by
  unfold beforeMasks
  congr 1
  funext round
  apply mask_fill
  constructor <;> intro equal <;> have values := congrArg Fin.val equal <;> simp at values <;> have := round.isLt <;> omega

/-- Only rounds after j+1 are used for the suffix permutation. -/
theorem after_fill :
    afterMasks selected password a b (fill selected (restrict selected h)) = afterMasks selected password a b h := by
  unfold afterMasks
  congr 1
  funext round
  apply mask_fill
  constructor <;> intro equal <;> have values := congrArg Fin.val equal <;> simp at values <;> have := round.isLt <;> omega

/-- Exact partition into prefix, two adjacent rounds, and suffix, including both boundary cases. -/
theorem mask_partition :
    allMasks password a b h = beforeMasks selected password a b h ++
      [mask password a b h selected.castSucc, mask password a b h selected.succ] ++
        afterMasks selected password a b h := by
  fin_cases selected <;> rfl

end KnownPairModel

/-! The actual inverse oracle executor agrees with the pure twelve-round permutation. -/
namespace CipherExecution
open Gamma2Model KnownPairModel Lemma1
variable {Password Entropy : Type}
attribute [local irreducible] finalize

theorem decrypt_append {width : Nat} (first last : List (BitVec width → BitVec width))
    (state : Lemma1.State width) : decrypt (first++last) state = decrypt first (decrypt last state) := by
  induction first with
  | nil => rfl
  | cons mask rest ih => simp only [List.cons_append,decrypt,ih]

def prefixMasks (password : Password) (tables : Tables Password Entropy) (fuel : Nat) (bound : fuel ≤ 12) :=
  List.ofFn (fun index : Fin fuel => mask password tables.a tables.b tables.h ⟨index.val,lt_of_lt_of_le index.isLt bound⟩)

theorem finalize_decrypt (password : Password) (tables : Tables Password Entropy) (fuel : Nat)
    (bound : fuel ≤ 12) (state : State) :
    (execute tables (finalize password fuel state bound)).1.1 = decrypt (prefixMasks password tables fuel bound) state := by
  induction fuel generalizing state with
  | zero => simp only [finalize,execute_pure,prefixMasks,List.ofFn_zero,decrypt]
  | succ fuel ih =>
    rw [FinalCut.finalize_step password tables fuel (by omega) state]
    dsimp only
    rw [ih (by omega)]
    unfold prefixMasks
    rw [List.ofFn_succ_last,decrypt_append]
    rfl

/-- Finalization is the inverse of the same pure cipher used by exact re-sampling. -/
theorem inverse (password : Password) (container : State) (tables : Tables Password Entropy) :
    (execute tables (finalize password 12 container (by omega))).1.1 =
      (roundsEquiv (allMasks password tables.a tables.b tables.h)).symm container := by
  exact finalize_decrypt password tables 12 (by omega) container

end CipherExecution

section

end

/-! Identical execution when the one changed G input was not queried in the unprogrammed game. -/
namespace GProgramming
open Gamma2Model
variable {Password Entropy Result : Type} [DecidableEq Entropy]

def updated (tables : Tables Password Entropy) (entropy : Entropy) (value : Hash) :
    Tables Password Entropy :=
  { tables with g := Function.update tables.g entropy value }

/-- The entire actual answer-dependent execution and transcript agree off the programmed point. -/
theorem execution (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) (entropy : Entropy) (value : Hash)
    (notQueried : Point.g entropy ∉ (execute tables program).2) :
    execute (updated tables entropy value) program = execute tables program := by
  apply TranscriptErasure.execute_agree program (answer tables) (answer (updated tables entropy value))
  intro point member
  cases point with
  | a password salt => rfl
  | b round right => rfl
  | h key round right => rfl
  | g queried =>
    have different : queried ≠ entropy := by
      intro same
      subst queried
      exact notQueried member
    exact Function.update_of_ne different _ _

end GProgramming

/-! Full source-game transfer for the twelve-call password-guessing theorem. -/
namespace Theorem3
open Gamma2Model CryptoInputs KnownPairModel
open GameExpectation MomentTools
variable {N : Nat} {E V R : Type} [DecidableEq E] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] finalize

def cipher (password : Fin N) (other : ABH (Fin N)) : Equiv.Perm State :=
  roundsEquiv (allMasks password other.1 other.2.1 other.2.2)

def entropy (state : (E × V) ≃ State) (input : State) : E := (state.symm input).1

def score (password : Fin N) (other : ABH (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) (Fin N)) (input : State × (E → Hash)) : Bool :=
  decide ((execute (tables other input.2) (adversary input.1)).1 = password)

variable (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (passwords : PMF (Fin N))
  (adversary : State → OracleComp (spec (Fin N) E) (Fin N))

def original : PMF Bool :=
  passwords.bind fun password => (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
    ((PMF.uniformOfFintype (E × (E → Hash))).map
      (CoordinateResampling.original state hash (cipher password other))).map (score password other adversary)

def programmed : PMF Bool :=
  passwords.bind fun password => (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
    ((PMF.uniformOfFintype (State × (E → Hash))).map
      (CoordinateResampling.programmed state hash (cipher password other))).map (score password other adversary)

theorem resampling :
    original state hash passwords adversary = programmed state hash passwords adversary := by
  unfold original programmed
  simp_rw [CoordinateResampling.fixed]

omit [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] in
/-- Pointwise identical-until-Bad transfer; the changed point is the actual inverse entropy. -/
theorem pointwise (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (password : Fin N)
    (other : ABH (Fin N)) (adversary : State → OracleComp (spec (Fin N) E) (Fin N))
    (seed : State × (E → Hash)) :
    (if score password other adversary (CoordinateResampling.programmed state hash (cipher password other) seed) then 1 else 0 : ENNReal) ≤
    (if Theorem3Assembly.winOrBad (entropy state) (outcome password seed.1 (tables other seed.2) adversary) then 1 else 0) := by
  classical
  let plain := tables other seed.2
  let inverse := state.symm ((cipher password other).symm seed.1)
  let output := CoordinateResampling.programmed state hash (cipher password other) seed
  have recovered : (outcome password seed.1 plain adversary).recovered = (cipher password other).symm seed.1 :=
    CipherExecution.inverse password seed.1 plain
  have target : entropy state (outcome password seed.1 plain adversary).recovered = inverse.1 := congrArg (entropy state) recovered
  by_cases win : score password other adversary output = true
  · have larger : Theorem3Assembly.winOrBad (entropy state) (outcome password seed.1 plain adversary) = true := by
      by_cases bad : Point.g (entropy state (outcome password seed.1 plain adversary).recovered) ∈ (execute plain (adversary seed.1)).2
      · exact decide_eq_true (Or.inr bad)
      · have missing : Point.g inverse.1 ∉ (execute plain (adversary seed.1)).2 := by rwa [target] at bad
        have same := GProgramming.execution plain (adversary seed.1) inverse.1
          (hash.symm (inverse.2,(hash (seed.2 inverse.1)).2)) missing
        have realWin : (execute (tables other output.2) (adversary output.1)).1 = password := of_decide_eq_true win
        change (execute (GProgramming.updated plain inverse.1
          (hash.symm (inverse.2,(hash (seed.2 inverse.1)).2))) (adversary seed.1)).1 = password at realWin
        rw [same] at realWin
        exact decide_eq_true (Or.inl realWin)
    dsimp only [plain] at larger
    simp only [show score password other adversary (CoordinateResampling.programmed state hash (cipher password other) seed) = true from win,
      larger,if_true,le_refl]
  · simp only [show score password other adversary (CoordinateResampling.programmed state hash (cipher password other) seed) = false from Bool.eq_false_iff.mpr win,
      Bool.false_eq_true,if_false,zero_le]

/-- This is the original Gamma0 win probability, bounded by the Gamma2 win-or-Bad event. -/
theorem transfer (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) (Fin N)) :
    (original state hash passwords adversary) true ≤
      ((Gamma2Model.game passwords adversary).map (Theorem3Assembly.winOrBad (entropy state))) true := by
  rw [resampling,← MomentTools.bool (programmed state hash passwords adversary),probability,CryptoInputs.game]
  unfold programmed
  simp only [MomentTools.bind,moment_map,Function.comp_def]
  apply mono
  intro password
  apply mono
  intro other
  apply mono
  intro seed
  exact pointwise state hash password other adversary seed

/-- Full original-game twelve-call bound, for the actual cipher and actual programmed hash coordinates. -/
theorem bound (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (entropy state input) = input.1) (passwords : PMF (Fin N))
    (sorted : Antitone passwords) (adversary : State → OracleComp (spec (Fin N) E) (Fin N))
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH)
    (budgetG : ∀ container tables,(execute tables (adversary container)).2.countP G4Programs.isG ≤ qG) :
    (original state hash passwords adversary) true ≤ RankedMass.top passwords (kA/12+1) +
      (qG+qB+12*p1*kA+66)/(2^128 : ENNReal) + qH/(2^256 : ENNReal) :=
  (transfer state hash passwords adversary).trans
    (Theorem3Assembly.bound (entropy state) firstHalf projects passwords sorted adversary
      p1 largest kA qB qH qG budgetA budgetB budgetH budgetG)

end Theorem3

/-! Exact high/low bit coordinates for short-source packing and hash-prefix programming. -/
namespace BitPacking
open Gamma2Model

def append (high low : Nat) : (BitVec high × BitVec low) ≃ BitVec (high+low) where
  toFun bits := bits.1 ++ bits.2
  invFun bits := (bits.extractLsb' low high,bits.extractLsb' 0 low)
  left_inv := by
    rintro ⟨highBits,lowBits⟩
    apply Prod.ext
    · exact BitVec.extractLsb'_append_eq_left
    · exact BitVec.extractLsb'_append_eq_right
  right_inv := by intro bits; exact BitVec.extractLsb'_append_extractLsb'

def cast (first second : Nat) (equal : first = second) : BitVec first ≃ BitVec second :=
  Equiv.cast (congrArg BitVec equal)

def state (tail verifier : Nat) (length : tail+verifier=128) :
    ((Half × BitVec tail) × BitVec verifier) ≃ State :=
  (Equiv.prodAssoc Half (BitVec tail) (BitVec verifier)).trans
    (Equiv.prodCongr (Equiv.refl Half) ((append tail verifier).trans (cast _ _ length)))

def hash (verifier suffix : Nat) (length : verifier+suffix=256) :
    Hash ≃ (BitVec verifier × BitVec suffix) :=
  ((append verifier suffix).trans (cast _ _ length)).symm

/-- The first 128 source bits are the actual first state half. -/
theorem first_half (tail verifier : Nat) (length : tail+verifier=128) (input : State) :
    ((state tail verifier length).symm input).1.1 = input.1 := rfl

end BitPacking

/-! Actual bit-string coordinates for ENT=128,160,192,224 in Theorem 3. -/
namespace ShortSourceCoordinates
open Gamma2Model
attribute [local instance] FiniteBits.fintype

def state (tail verifier : Nat) (length : tail+verifier=128) :
    (BitVec (128+tail) × BitVec verifier) ≃ State :=
  (Equiv.prodCongr (BitPacking.append 128 tail).symm (Equiv.refl _)).trans
    (BitPacking.state tail verifier length)

def firstHalf (tail : Nat) (source : BitVec (128+tail)) : Half :=
  ((BitPacking.append 128 tail).symm source).1

/-- The entropy projection used by G4 is exactly the leading 128 bits of the source. -/
theorem projects (tail verifier : Nat) (length : tail+verifier=128) (input : State) :
    firstHalf tail (Theorem3.entropy (state tail verifier length) input) = input.1 := by
  change ((BitPacking.append 128 tail).symm
    ((BitPacking.append 128 tail) ((BitPacking.state tail verifier length).symm input).1)).1 = input.1
  rw [Equiv.symm_apply_apply]
  exact BitPacking.first_half tail verifier length input

/-- These are the four normative short-source lengths, with their actual verifier sizes. -/
theorem source_lengths :
    (128+0=128 ∧ 0+128=128 ∧ 128+128=256) ∧
    (128+32=160 ∧ 32+96=128 ∧ 96+160=256) ∧
    (128+64=192 ∧ 64+64=128 ∧ 64+192=256) ∧
    (128+96=224 ∧ 96+32=128 ∧ 32+224=256) := by decide

end ShortSourceCoordinates

/-! Independent private coins for the complete original-game Theorem 3. -/
namespace Theorem3Randomized
open Gamma2Model GameExpectation MomentTools
variable {N : Nat} {E V R Strategy : Type} [DecidableEq E] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- The strategy may adapt every query; only its initial private coins are independent. -/
theorem bound (coins : PMF Strategy) (state : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy state input)=input.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : Strategy → State → OracleComp (spec (Fin N) E) (Fin N)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isH ≤ qH)
    (budgetG : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP G4Programs.isG ≤ qG) :
    (coins.bind fun strategy => Theorem3.original state hash passwords (adversary strategy)) true ≤
      RankedMass.top passwords (kA/12+1) +
      (qG+qB+12*p1*kA+66)/(2^128 : ENNReal) + qH/(2^256 : ENNReal) := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact Theorem3.bound state hash firstHalf projects passwords sorted (adversary strategy)
    p1 largest kA qB qH qG (budgetA strategy) (budgetB strategy) (budgetH strategy) (budgetG strategy)

end Theorem3Randomized

/-! The complete Theorem 3 instantiated at the four actual short-source sizes. -/
namespace Suite3ShortBound
attribute [local instance] FiniteBits.fintype

/-- Remaining arguments are exactly the password distribution, adaptive strategy and hard budgets of Theorem 3. -/
def bound {N : Nat} {Strategy : Type} (tail verifier suffix : Nat)
    (stateLength : tail+verifier=128) (hashLength : verifier+suffix=256) (coins : PMF Strategy) :=
  Theorem3Randomized.bound (N := N)
    (E := BitVec (128+tail)) (V := BitVec verifier) (R := BitVec suffix) coins
    (ShortSourceCoordinates.state tail verifier stateLength)
    (BitPacking.hash verifier suffix hashLength)
    (ShortSourceCoordinates.firstHalf tail)
    (ShortSourceCoordinates.projects tail verifier stateLength)

/-- ENT=128, with the actual 128-bit verifier and unprogrammed hash suffix. -/
def words12 {N : Nat} {Strategy : Type} (coins : PMF Strategy) :=
  bound (N := N) 0 128 128 (by decide) (by decide) coins

/-- ENT=160, verifier=96 bits. -/
def words15 {N : Nat} {Strategy : Type} (coins : PMF Strategy) :=
  bound (N := N) 32 96 160 (by decide) (by decide) coins

/-- ENT=192, verifier=64 bits. -/
def words18 {N : Nat} {Strategy : Type} (coins : PMF Strategy) :=
  bound (N := N) 64 64 192 (by decide) (by decide) coins

/-- ENT=224, verifier=32 bits. -/
def words21 {N : Nat} {Strategy : Type} (coins : PMF Strategy) :=
  bound (N := N) 96 32 224 (by decide) (by decide) coins

end Suite3ShortBound

/-! Bad-only assembly for source recovery: no final password-guess allowance. -/
namespace SourceRecoveryAssembly
open Gamma2Model G2 G4Order QueryCounts
open GameExpectation MomentTools CompletedPasswords
variable {N : Nat} {Entropy Result : Type} [DecidableEq Entropy] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

def winOrBad (source : State → Entropy) (out : Outcome (Fin N) Entropy Result) : Bool := by
  classical
  exact decide (Point.g (source out.recovered) ∈ out.adversaryQueries)

def mainTest (out : Outcome (Fin N) Entropy Result) : Bool :=
  decide (out.password ∈ chosen out.adversaryQueries)

omit [Fintype Entropy] in
/-- Exact deterministic inclusion. A complete real chain needs twelve actual A calls. -/
theorem covered (source : State → Entropy) (password : Fin N) (container : State)
    (tables : Tables (Fin N) Entropy) (adversary : State → OracleComp (spec (Fin N) Entropy) Result)
    (hit : winOrBad source (outcome password container tables adversary) = true) :
    mainTest (outcome password container tables adversary) = true ∨
      G3Sums.earlyTest (outcome password container tables adversary) = true ∨
      G4.sourceTest source (outcome password container tables adversary) = true := by
  classical
  have details : Point.g (source (outcome password container tables adversary).recovered) ∈
        (outcome password container tables adversary).adversaryQueries := of_decide_eq_true hit
  by_cases early : Early (chronologicalRun password container tables adversary)
  · exact Or.inr (Or.inl (decide_eq_true early))
  · by_cases complete : Complete (chronologicalRun password container tables adversary)
    · apply Or.inl
      apply decide_eq_true
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,G5.twelve_queries password container tables adversary early complete⟩
    · exact Or.inr (Or.inr (decide_eq_true ⟨details,complete,early⟩))

/-- Adaptively selected twelve-call password rows are independent of P in Gamma2. -/
theorem main_bound (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) Entropy) Result) (kA : Nat)
    (budget : ∀ container tables,(execute tables (adversary container)).2.countP isA ≤ kA) :
    ((game passwords adversary).map mainTest) true ≤ RankedMass.top passwords (kA/12) := by
  classical
  rw [probability,game_as_input_map,moment_map]
  simpa only [Function.comp_def,mainTest,decide_eq_true_eq,outcome] using
    RankedMass.independent_set_bound passwords sorted (inputsLaw adversary)
    (fun inputs => chosen (execute inputs.2 (adversary inputs.1)).2)
    (kA/12) (fun inputs => count _ kA (budget inputs.1 inputs.2))

/-- This is the exact final bound in Gamma2 before the G1/programming transfer back to Gamma0. -/
theorem bound (source : State → Entropy) (firstHalf : Entropy → Half)
    (projects : ∀ state,firstHalf (source state) = state.1) (passwords : PMF (Fin N))
    (sorted : Antitone passwords) (adversary : State → OracleComp (spec (Fin N) Entropy) Result)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP isH ≤ qH)
    (budgetG : ∀ container tables,(execute tables (adversary container)).2.countP G4Programs.isG ≤ qG) :
    ((game passwords adversary).map (winOrBad source)) true ≤
      RankedMass.top passwords (kA/12) +
      (qG+qB+12*p1*kA+66)/(2^128 : ENNReal) + qH/(2^256 : ENNReal) := by
  classical
  have pointwise := fun password container tables => covered source password container tables adversary
  have included : ((game passwords adversary).map (winOrBad source)) true ≤
      ((game passwords adversary).map mainTest) true +
      ((game passwords adversary).map G3Sums.earlyTest) true +
      ((game passwords adversary).map (G4.sourceTest source)) true := by
    rw [probability,probability,probability,probability,← MomentTools.add,← MomentTools.add]
    apply G3Assembly.game_pointwise
    intro password container tables
    by_cases hit : winOrBad source (outcome password container tables adversary) = true
    · rw [hit]
      rcases pointwise password container tables hit with main | early | incomplete
      · rw [main]; exact (le_add_of_nonneg_right (zero_le)).trans (le_add_of_nonneg_right (zero_le))
      · rw [early]; exact (le_add_of_nonneg_left (zero_le)).trans (le_add_of_nonneg_right (zero_le))
      · rw [incomplete]; exact le_add_of_nonneg_left (zero_le)
    · simp only [Bool.eq_false_iff.mpr hit,Bool.false_eq_true,if_false,zero_le]
  have estimate := add_le_add
    (add_le_add (main_bound passwords sorted adversary kA budgetA)
      (G3Assembly.lemma_g3 passwords adversary p1 largest kA qB qH budgetA budgetB budgetH))
    (G4.lemma_g4_source source firstHalf projects passwords adversary qG budgetG)
  apply included.trans
  apply estimate.trans_eq
  simp only [ENNReal.add_div]
  abel

end SourceRecoveryAssembly

/-! A source output can be treated as one additional G query, without changing it. -/
namespace SourceOutputQuery
open Gamma2Model
variable {Password Entropy : Type}

def augment (program : OracleComp (spec Password Entropy) Entropy) :
    OracleComp (spec Password Entropy) Entropy := do
  let source ← program
  let _ ← ask (.g source)
  return source

variable (tables : Tables Password Entropy) (program : OracleComp (spec Password Entropy) Entropy)

/-- The appended query preserves the output and costs precisely one cheap hash call. -/
theorem execution :
    execute tables (augment program) =
      ((execute tables program).1,(execute tables program).2 ++ [.g (execute tables program).1]) := by
  simp only [augment,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,List.append_nil]

/-- In particular, the final answer itself occurs as a queried entropy. -/
theorem member : Point.g (execute tables (augment program)).1 ∈ (execute tables (augment program)).2 := by
  rw [execution]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Budget changes are exact, including repeated output queries. -/
theorem counts :
    (execute tables (augment program)).2.countP QueryCounts.isA = (execute tables program).2.countP QueryCounts.isA ∧
    (execute tables (augment program)).2.countP QueryCounts.isB = (execute tables program).2.countP QueryCounts.isB ∧
    (execute tables (augment program)).2.countP QueryCounts.isH = (execute tables program).2.countP QueryCounts.isH ∧
    (execute tables (augment program)).2.countP G4Programs.isG = (execute tables program).2.countP G4Programs.isG + 1 := by
  simp [execution,List.countP_append,QueryCounts.isA,QueryCounts.isB,QueryCounts.isH,G4Programs.isG]

end SourceOutputQuery

/-! Corollary G6: actual entropy recovery, without a free final password guess. -/
namespace G6
open Gamma2Model CryptoInputs Theorem3
open GameExpectation MomentTools
set_option maxHeartbeats 400000
attribute [local irreducible] finalize
variable {N : Nat} {E V R : Type} [DecidableEq E] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

def score (state : (E × V) ≃ State) (password : Fin N) (other : ABH (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) E) (input : State × (E → Hash)) : Bool :=
  decide ((execute (tables other input.2) (adversary input.1)).1 = entropy state ((cipher password other).symm input.1))

def original (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) E) : PMF Bool :=
  passwords.bind fun password => (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
    ((PMF.uniformOfFintype (E × (E → Hash))).map
      (CoordinateResampling.original state hash (cipher password other))).map (score state password other adversary)

omit [DecidableEq E] [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] in
/-- Recovering entropy here means the actual sampled source, not an arbitrary inverse. -/
theorem sampled_source (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (password : Fin N)
    (other : ABH (Fin N)) (seed : E × (E → Hash)) :
    entropy state ((cipher password other).symm
      (CoordinateResampling.original state hash (cipher password other) seed).1) = seed.1 := by
  simp [entropy,CoordinateResampling.original]

omit [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] in
/-- If the changed G point is absent, the augmented answer is unchanged and cannot be the source. -/
theorem pointwise (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (password : Fin N)
    (other : ABH (Fin N)) (adversary : State → OracleComp (spec (Fin N) E) E)
    (seed : State × (E → Hash)) :
    (if score state password other adversary (CoordinateResampling.programmed state hash (cipher password other) seed) then 1 else 0 : ENNReal) ≤
    (if SourceRecoveryAssembly.winOrBad (entropy state)
      (outcome password seed.1 (tables other seed.2) (fun container => SourceOutputQuery.augment (adversary container))) then 1 else 0) := by
  classical
  let plain := tables other seed.2
  let inverse := state.symm ((cipher password other).symm seed.1)
  let output := CoordinateResampling.programmed state hash (cipher password other) seed
  let augmented := fun container => SourceOutputQuery.augment (adversary container)
  have recovered : (outcome password seed.1 plain augmented).recovered = (cipher password other).symm seed.1 :=
    CipherExecution.inverse password seed.1 plain
  have target : entropy state (outcome password seed.1 plain augmented).recovered = inverse.1 := congrArg (entropy state) recovered
  by_cases hit : score state password other adversary output = true
  · have bad : Point.g inverse.1 ∈ (execute plain (augmented seed.1)).2 := by
      by_contra missing
      have same := GProgramming.execution plain (augmented seed.1) inverse.1
        (hash.symm (inverse.2,(hash (seed.2 inverse.1)).2)) missing
      have win : (execute (tables other output.2) (adversary output.1)).1 = inverse.1 := of_decide_eq_true hit
      have winAug : (execute (tables other output.2) (augmented output.1)).1 = inverse.1 := by
        simpa only [augmented,SourceOutputQuery.execution] using win
      change (execute (GProgramming.updated plain inverse.1
        (hash.symm (inverse.2,(hash (seed.2 inverse.1)).2))) (augmented seed.1)).1 = inverse.1 at winAug
      rw [same] at winAug
      have queried := SourceOutputQuery.member plain (adversary seed.1)
      change Point.g (execute plain (augmented seed.1)).1 ∈ (execute plain (augmented seed.1)).2 at queried
      exact missing (winAug ▸ queried)
    have included : SourceRecoveryAssembly.winOrBad (entropy state) (outcome password seed.1 plain augmented) = true :=
      decide_eq_true (by rwa [target])
    dsimp only [plain,augmented] at included
    simp only [show score state password other adversary (CoordinateResampling.programmed state hash (cipher password other) seed)=true from hit,
      included,if_true,le_refl]
  · simp only [show score state password other adversary (CoordinateResampling.programmed state hash (cipher password other) seed)=false from Bool.eq_false_iff.mpr hit,
      Bool.false_eq_true,if_false,zero_le]

/-- The original source-recovery event transfers to the augmented Gamma2 Bad event. -/
theorem transfer (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) E) :
    (original state hash passwords adversary) true ≤
      ((Gamma2Model.game passwords (fun container => SourceOutputQuery.augment (adversary container))).map
        (SourceRecoveryAssembly.winOrBad (entropy state))) true := by
  rw [← MomentTools.bool (original state hash passwords adversary),probability,CryptoInputs.game]
  unfold original
  simp_rw [CoordinateResampling.fixed]
  simp only [MomentTools.bind,moment_map,Function.comp_def]
  apply mono
  intro password
  apply mono
  intro other
  apply mono
  intro seed
  exact pointwise state hash password other adversary seed

/-- The exact G6 formula, including the extra 2^-128 for a direct source output. -/
theorem bound (state : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (entropy state input)=input.1) (passwords : PMF (Fin N))
    (sorted : Antitone passwords) (adversary : State → OracleComp (spec (Fin N) E) E) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH)
    (budgetG : ∀ container tables,(execute tables (adversary container)).2.countP G4Programs.isG ≤ qG) :
    (original state hash passwords adversary) true ≤ RankedMass.top passwords (kA/12) +
      (qG+1+qB+12*p1*kA+66)/(2^128 : ENNReal) + qH/(2^256 : ENNReal) := by
  apply (transfer state hash passwords adversary).trans
  simpa only [Nat.cast_add,Nat.cast_one] using
    SourceRecoveryAssembly.bound (entropy state) firstHalf projects passwords sorted
      (fun container => SourceOutputQuery.augment (adversary container)) p1 largest kA qB qH (qG+1)
      (fun container tables => (SourceOutputQuery.counts tables (adversary container)).1.trans_le (budgetA container tables))
      (fun container tables => (SourceOutputQuery.counts tables (adversary container)).2.1.trans_le (budgetB container tables))
      (fun container tables => (SourceOutputQuery.counts tables (adversary container)).2.2.1.trans_le (budgetH container tables))
      (fun container tables => (SourceOutputQuery.counts tables (adversary container)).2.2.2.trans_le (Nat.add_le_add_right (budgetG container tables) 1))

/-- Independent private random coins preserve the full source-recovery bound. -/
theorem randomized {Strategy : Type} (coins : PMF Strategy) (state : (E × V) ≃ State)
    (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (entropy state input)=input.1) (passwords : PMF (Fin N))
    (sorted : Antitone passwords) (adversary : Strategy → State → OracleComp (spec (Fin N) E) E)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isH ≤ qH)
    (budgetG : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP G4Programs.isG ≤ qG) :
    (coins.bind fun strategy => original state hash passwords (adversary strategy)) true ≤
      RankedMass.top passwords (kA/12) +
      (qG+1+qB+12*p1*kA+66)/(2^128 : ENNReal) + qH/(2^256 : ENNReal) := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact bound state hash firstHalf projects passwords sorted (adversary strategy)
    p1 largest kA qB qH qG (budgetA strategy) (budgetB strategy) (budgetH strategy) (budgetG strategy)

end G6

end
end MhfeLean
