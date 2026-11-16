/- long: the fractional counting argument and Theorem 4 assembly share one context. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import MhfeLean.Chapters.KnownPairCross
import MhfeLean.Chapters.KnownPairEarly
import MhfeLean.Chapters.KnownPairResampling
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.Probability
import MhfeLean.Chapters.ShortSources

namespace MhfeLean
noncomputable section

/-! # Lemma K4 and Theorem 4: fractional guessing credit
-/

/-! Greedy fractional-password mass bound used by Theorem 4. -/
namespace FractionalMass
variable {N : Nat}

def leadingMass (p : Fin N → ℝ) (whole : Nat) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < whole), p i

/-- Fractional mass is bounded by filling the largest probabilities first. -/
theorem greedy (p weights : Fin N → ℝ) (sorted : Antitone p) (nonnegative : ∀ i,0 ≤ p i)
    (weights_nonnegative : ∀ i,0 ≤ weights i) (weights_bounded : ∀ i,weights i ≤ 1) (whole : Fin N)
    (capacity : ℝ) (budget : ∑ i,weights i ≤ capacity) :
    (∑ i,p i * weights i) ≤ leadingMass p whole.val + (capacity-whole.val)*p whole := by
  classical
  have pointwise (i : Fin N) :
      p i * weights i ≤ (if i.val < whole.val then p i-p whole else 0)+p whole*weights i := by
    by_cases early : i.val < whole.val
    · have order := sorted (show i ≤ whole from Nat.le_of_lt early)
      rw [if_pos early]
      nlinarith [weights_bounded i]
    · have order := sorted (show whole ≤ i from Nat.le_of_not_gt early)
      rw [if_neg early]
      nlinarith [weights_nonnegative i]
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pointwise i)
  have calculation :
      (∑ i : Fin N,((if i.val < whole.val then p i-p whole else 0)+p whole*weights i)) =
      leadingMass p whole.val + ((∑ i,weights i)-whole.val)*p whole := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_filter]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Fin.card_filter_val_lt,
      min_eq_right (Nat.le_of_lt whole.isLt),nsmul_eq_mul,leadingMass]
    ring
  rw [calculation] at total
  exact total.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (sub_le_sub_right budget _) (nonnegative whole)))

end FractionalMass

/-! Closed fractional-top formula, including saturation at the end of the dictionary. -/
namespace FractionalTop
variable {N : Nat}

def value (p : Fin N → ℝ) (whole : Nat) (part : ℝ) : ℝ :=
  if available : whole < N then
    FractionalMass.leadingMass p whole + part*p ⟨whole,available⟩
  else ∑ i,p i

/-- A greedy upper bound; the canonical whole-plus-fraction decomposition is used below. -/
theorem bound (p weights : Fin N → ℝ) (sorted : Antitone p) (nonnegative : ∀ i,0 ≤ p i)
    (weights_nonnegative : ∀ i,0 ≤ weights i) (weights_bounded : ∀ i,weights i ≤ 1) (whole : Nat)
    (part : ℝ) (budget : ∑ i,weights i ≤ whole+part) : (∑ i,p i*weights i) ≤ value p whole part := by
  by_cases available : whole < N
  · rw [value,dif_pos available]
    have estimate := FractionalMass.greedy p weights sorted nonnegative
      weights_nonnegative weights_bounded ⟨whole,available⟩ (whole+part) budget
    simpa only [Nat.cast_add,add_sub_cancel_left] using estimate
  · rw [value,dif_neg available]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (weights_bounded i) (nonnegative i)

/-- The eleven-position average leaves exactly k_A mod 11 over 11 of the next password. -/
theorem known_pair (p weights : Fin N → ℝ) (sorted : Antitone p) (nonnegative : ∀ i,0 ≤ p i)
    (weights_nonnegative : ∀ i,0 ≤ weights i) (weights_bounded : ∀ i,weights i ≤ 1) (kA : Nat)
    (budget : ∑ i,weights i ≤ 1+(kA:ℝ)/11) :
    (∑ i,p i*weights i) ≤ value p (kA/11+1) (((kA%11:Nat):ℝ)/11) := by
  have split : (kA:ℝ) = ((kA%11:Nat):ℝ)+11*((kA/11:Nat):ℝ) := by
    exact_mod_cast (Nat.mod_add_div kA 11).symm
  apply bound p weights sorted nonnegative weights_nonnegative weights_bounded
  convert budget using 1
  push_cast
  linarith

end FractionalTop

/-! Deterministic fractional credit of the actual A-query transcript. -/
namespace KnownPairCredit
open Gamma2Model QueryCounts
variable {N : Nat} {Entropy : Type}

variable (guess : Fin N) (queries : List (Point (Fin N) Entropy))

def weight (password : Fin N) : ℝ :=
  min 1 ((if guess=password then 1 else 0)+(queries.countP (aFor password):ℝ)/11)

/-- Credit is a proof upper bound, not an asserted partial-chain attack. -/
theorem range (password : Fin N) :
    0 ≤ weight guess queries password ∧ weight guess queries password ≤ 1 := by
  constructor
  · apply le_min (by norm_num)
    apply add_nonneg
    · split_ifs <;> norm_num
    · positivity
  · exact min_le_left _ _

/-- The final answer contributes at most one unit; all A calls contribute at most k_A/11. -/
theorem budget (kA : Nat) (calls : queries.countP isA ≤ kA) :
    (∑ password,weight guess queries password) ≤ 1+(kA:ℝ)/11 := by
  classical
  calc
    _ ≤ ∑ password : Fin N,((if guess=password then 1 else 0)+(queries.countP (aFor password):ℝ)/11) := by
      apply Finset.sum_le_sum
      intro password _
      exact min_le_right _ _
    _ = 1+(queries.countP isA:ℝ)/11 := by
      rw [Finset.sum_add_distrib,← Finset.sum_div]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
      rw [← Nat.cast_sum,a_partition]
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right (by exact_mod_cast calls) (by norm_num))

/-- The closed fractional-top bound holds for every realized query transcript. -/
theorem mass_bound (probabilities : Fin N → ℝ) (sorted : Antitone probabilities)
    (nonnegative : ∀ password,0 ≤ probabilities password) (guess : Fin N)
    (queries : List (Point (Fin N) Entropy)) (kA : Nat) (calls : queries.countP isA ≤ kA) :
    (∑ password,probabilities password*weight guess queries password) ≤
      FractionalTop.value probabilities (kA/11+1) (((kA%11:Nat):ℝ)/11) :=
  FractionalTop.known_pair probabilities (weight guess queries) sorted nonnegative
    (fun password => (range guess queries password).1) (fun password => (range guess queries password).2)
    kA (budget guess queries kA calls)

end KnownPairCredit

/-! Finite round-set counting for K4, with overlap handled without double charging. -/
namespace K4Combinatorics
open Finset

/-- Forward prefixes and backward suffixes charge bad adjacent positions to their round union. -/
theorem round_bound (forward backward : Finset (Fin 12))
    (initial : ∀ x ∈ forward, ∀ y : Fin 12, y ≤ x → y ∈ forward)
    (final : ∀ x ∈ backward, ∀ y : Fin 12, x ≤ y → y ∈ backward) :
    ((Finset.univ : Finset (Fin 11)).filter fun j => j.castSucc ∈ forward ∨ j.succ ∈ backward).card ≤
      (forward ∪ backward).card := by
  classical
  let left := (Finset.univ : Finset (Fin 11)).filter fun j => j.castSucc ∈ forward
  let right := (Finset.univ : Finset (Fin 11)).filter fun j => j.succ ∈ backward
  have leftBound : left.card ≤ forward.card := by
    apply Finset.card_le_card_of_injOn Fin.castSucc
    · intro j member
      simpa only [Finset.mem_coe, left, Finset.mem_filter, Finset.mem_univ, true_and] using member
    · intro a _ b _ equal
      exact Fin.castSucc_injective 11 equal
  have rightBound : right.card ≤ backward.card := by
    apply Finset.card_le_card_of_injOn Fin.succ
    · intro j member
      simpa only [Finset.mem_coe, right, Finset.mem_filter, Finset.mem_univ, true_and] using member
    · intro a _ b _ equal
      exact Fin.succ_injective 11 equal
  by_cases disjoint : Disjoint forward backward
  · have shape : ((Finset.univ : Finset (Fin 11)).filter fun j =>
          j.castSucc ∈ forward ∨ j.succ ∈ backward) = left ∪ right := by
      ext j
      simp only [left, right, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [shape, Finset.card_union_of_disjoint disjoint]
    exact (Finset.card_union_le left right).trans (Nat.add_le_add leftBound rightBound)
  · obtain ⟨x, inForward, inBackward⟩ := Finset.not_disjoint_iff.mp disjoint
    have full : forward ∪ backward = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro y
      rcases le_total y x with lower | upper
      · exact Finset.mem_union_left _ (initial x inForward y lower)
      · exact Finset.mem_union_right _ (final x inBackward y upper)
    rw [full, Finset.card_univ, Fintype.card_fin]
    exact (Finset.card_filter_le _ _).trans (by decide)

end K4Combinatorics

/-! Actual queried round sets and adjacent programmed H points in K4. -/
namespace K4Order
open Gamma2Model TwoChainModel CrossModel G2
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

def rounds (out : Outcome2 Password Entropy Result) (direction : Bool) : Finset (Fin 12) := by
  classical
  exact Finset.univ.filter fun r => Queried (run out direction) (bIndex direction r + 1)

/-- The exact n_bad event of each of the eleven adjacent mask-programming positions. -/
def bad (out : Outcome2 Password Entropy Result) : Finset (Fin 11) := by
  classical
  exact Finset.univ.filter fun j =>
    Queried (run out true) (bIndex true j.castSucc + 2) ∨
    Queried (run out false) (bIndex false j.succ + 2)

theorem clean_direction (out : Outcome2 Password Entropy Result) (clean : ¬ Early2 out)
    (direction : Bool) : ¬ Early (run out direction) := by
  cases direction with
  | false => exact fun h => clean (Or.inr h)
  | true => exact fun h => clean (Or.inl h)

theorem queried_member (out : Outcome2 Password Entropy Result) (direction : Bool) (index : Nat) :
    Queried (run out direction) index ↔ (run out direction).point index ∈ out.base.adversaryQueries := by
  simp only [Queried, firstTime, run, queries, List.append_assoc]
  rw [List.idxOf_append]
  by_cases member : (if direction then out.forwardChain else out.base.chain).getD index fallbackPoint ∈ out.base.adversaryQueries
  · simp only [member, if_true, iff_true]
    exact List.idxOf_lt_length_iff.mpr member
  · simp only [member, if_false, iff_false]
    omega

theorem initial (out : Outcome2 Password Entropy Result) (size : ∀ d, (run out d).count = 36)
    (clean : ¬ Early2 out) : ∀ x ∈ rounds out true, ∀ y : Fin 12, y ≤ x → y ∈ rounds out true := by
  classical
  intro x member y lower
  simp only [rounds, Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
  rcases eq_or_lt_of_le lower with same | earlier
  · simpa only [same] using member
  · exact Nat.lt_trans (all_ordered _ (clean_direction out clean true)
      (bIndex true y + 1) (bIndex true x + 1)
      (by simp only [bIndex, ↓reduceIte]; change y.val < x.val at earlier; omega)
      (by rw [size]; simp only [bIndex, ↓reduceIte]; have := x.isLt; omega)) member

theorem final (out : Outcome2 Password Entropy Result) (size : ∀ d, (run out d).count = 36)
    (clean : ¬ Early2 out) : ∀ x ∈ rounds out false, ∀ y : Fin 12, x ≤ y → y ∈ rounds out false := by
  classical
  intro x member y upper
  simp only [rounds, Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
  rcases eq_or_lt_of_le upper with same | earlier
  · simpa only [same] using member
  · exact Nat.lt_trans (all_ordered _ (clean_direction out clean false)
      (bIndex false y + 1) (bIndex false x + 1)
      (by simp only [bIndex, Bool.false_eq_true, ↓reduceIte]; change x.val < y.val at earlier; have := y.isLt; omega)
      (by rw [size]; simp only [bIndex, Bool.false_eq_true, ↓reduceIte]; have := x.isLt; omega)) member

theorem bad_bound (out : Outcome2 Password Entropy Result) (size : ∀ d, (run out d).count = 36)
    (clean : ¬ Early2 out) : (bad out).card ≤ ((rounds out true) ∪ (rounds out false)).card := by
  classical
  apply (Finset.card_le_card (t := Finset.univ.filter fun j : Fin 11 =>
    j.castSucc ∈ rounds out true ∨ j.succ ∈ rounds out false) ?_).trans
    (K4Combinatorics.round_bound _ _ (initial out size clean) (final out size clean))
  intro j member
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
  have preceding (d : Bool) (r : Fin 12)
      (asked : Queried (run out d) (bIndex d r + 2)) : r ∈ rounds out d := by
    simp only [rounds, Finset.mem_filter, Finset.mem_univ, true_and]
    have h := (predecessor out clean d (bIndex d r + 2) (by omega)
      (by rw [size]; cases d <;> simp only [bIndex, Bool.false_eq_true, ↓reduceIte] <;> have := r.isLt <;> omega) asked).1
    (try simp only [Nat.add_sub_cancel] at h ⊢)
    exact h
  exact member.elim (fun h => Or.inl (preceding true j.castSucc h))
    (fun h => Or.inr (preceding false j.succ h))

end K4Order

/-! Full K4 counting of the eleven adjacent programming positions. -/
namespace K4
open Gamma2Model TwoChainModel CrossModel K4Order
open G2 QueryCounts
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] forward finalize

theorem same_chain_round (out : Outcome2 Password Entropy Result)
    (size : ∀ d, (run out d).count = 36) (clean : ¬ Early2 out) (d : Bool) (first second : Fin 12)
    (equal : actualA out d first = actualA out d second) : first = second := by
  have within (r : Fin 12) : bIndex d r + 1 < (run out d).count := by
    rw [size]
    cases d <;> simp only [bIndex, Bool.false_eq_true, ↓reduceIte] <;> have := r.isLt <;> omega
  have indices := per_chain_distinct out clean d
    (a₁ := ⟨bIndex d first + 1, within first⟩)
    (a₂ := ⟨bIndex d second + 1, within second⟩) equal
  have numeric := congrArg Fin.val indices
  apply Fin.ext
  cases d <;> simp only [bIndex, Bool.false_eq_true, ↓reduceIte] at numeric <;>
    have := first.isLt <;> have := second.isLt <;> omega

/-- No cross-round equality holds among the queried A choices, even across chains. -/
theorem round_unique (out : Outcome2 Password Entropy Result) (size : ∀ d, (run out d).count = 36)
    (clean : ¬ Early2 out) (noCross : ¬ Cross out) (left right : Bool) (first second : Fin 12)
    (equal : actualA out left first = actualA out right second) : first = second := by
  cases left <;> cases right
  · exact same_chain_round out size clean false first second equal
  · by_contra different
    exact noCross ⟨second, first, Ne.symm different, equal.symm⟩
  · by_contra different
    exact noCross ⟨first, second, different, equal⟩
  · exact same_chain_round out size clean true first second equal

theorem union_queries (source : State) (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (clean : ¬ Early2 (enrich source (outcome password container tables adversary)))
    (noCross : ¬ Cross (enrich source (outcome password container tables adversary))) :
    ((rounds (enrich source (outcome password container tables adversary)) true) ∪
      (rounds (enrich source (outcome password container tables adversary)) false)).card ≤
      (execute tables (adversary container)).2.countP (aFor password) := by
  classical
  let out := enrich source (outcome password container tables adversary)
  let covered := rounds out true ∪ rounds out false
  let direction : {r // r ∈ covered} → Bool := fun r => decide (r.val ∈ rounds out true)
  let choice : {r // r ∈ covered} → Point Password Entropy := fun r => actualA out (direction r) r.val
  have size : ∀ d, (run out d).count = 36 := fun d => run_count source password container tables adversary d
  have injective : Function.Injective choice := by
    intro first second equal
    apply Subtype.ext
    exact round_unique out size clean noCross (direction first) (direction second) first.val second.val equal
  have member : ∀ r, choice r ∈ ((execute tables (adversary container)).2.filter (aFor password)).toFinset := by
    intro r
    have asked : Queried (run out (direction r)) (bIndex (direction r) r.val + 1) := by
      have present := r.property
      simp only [covered, Finset.mem_union] at present
      by_cases front : r.val ∈ rounds out true
      · simp only [direction, front, decide_true]
        exact (Finset.mem_filter.mp front).2
      · have back := present.resolve_left front
        simp only [direction, front, decide_false]
        exact (Finset.mem_filter.mp back).2
    have inTrace := (queried_member out (direction r) _).mp asked
    obtain ⟨half, _, aPoint⟩ := block source password container tables adversary (direction r) r.val
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    refine ⟨inTrace, ?_⟩
    change aFor password (actualA out (direction r) r.val) = true
    rw [aPoint]
    simp only [aFor, decide_true]
  have subset : Finset.univ.image choice ⊆
      ((execute tables (adversary container)).2.filter (aFor password)).toFinset := by
    intro point found
    obtain ⟨r, _, equal⟩ := Finset.mem_image.mp found
    rw [← equal]
    exact member r
  calc
    covered.card = (Finset.univ.image choice).card := by
      rw [Finset.card_image_of_injective _ injective, Finset.card_univ, Fintype.card_coe]
    _ ≤ _ := Finset.card_le_card subset
    _ ≤ _ := List.toFinset_card_le _
    _ = _ := List.countP_eq_length_filter.symm

/-- Source Lemma K4 on the actual common-table two-chain execution. -/
theorem lemma_k4 (source : State) (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (clean : ¬ Early2 (enrich source (outcome password container tables adversary)))
    (noCross : ¬ Cross (enrich source (outcome password container tables adversary))) :
    (bad (enrich source (outcome password container tables adversary))).card ≤
      min 11 ((execute tables (adversary container)).2.countP (aFor password)) := by
  classical
  apply Nat.le_min.mpr
  constructor
  · exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin 11)
  · exact (bad_bound _ (fun d => run_count source password container tables adversary d) clean).trans
      (union_queries source password container tables adversary clean noCross)

end K4

/-! Equation (2) and its pointwise K4 credit inequality. -/
namespace KnownPairAverage
open Gamma2Model TwoChainModel CrossModel

def average (win : Bool) (positions : Finset (Fin 11)) : ℝ :=
  (∑ position : Fin 11,if win=true ∨ position ∈ positions then 1 else 0)/11

/-- The average is one on a win, and otherwise the fraction of programmed positions queried. -/
theorem identity (win : Bool) (positions : Finset (Fin 11)) :
    average win positions = min 1 ((if win then 1 else 0)+(positions.card:ℝ)/11) := by
  classical
  have count : positions.card ≤ 11 := by simpa using Finset.card_le_card (Finset.subset_univ positions)
  have countReal : (positions.card:ℝ) ≤ 11 := by exact_mod_cast count
  cases win with
  | false =>
    simp only [average,Bool.false_eq_true,false_or,if_false,zero_add]
    have total : (∑ position : Fin 11,if position ∈ positions then (1:ℝ) else 0) = positions.card := by
      rw [← Finset.sum_filter]
      simp
    rw [total,min_eq_right (by linarith)]
  | true =>
    simp only [average,true_or,if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have nonnegative : (0:ℝ) ≤ (positions.card:ℝ)/11 := by positivity
    have lower : (1:ℝ) ≤ 1+(positions.card:ℝ)/11 := by linarith
    rw [min_eq_left lower]
    norm_num

/-- Every average is a probability-sized credit, independently of either chain. -/
theorem bounded (win : Bool) (positions : Finset (Fin 11)) : average win positions ≤ 1 := by
  rw [identity]
  exact min_le_left _ _

variable {N : Nat} {Entropy : Type} [DecidableEq Entropy]

/-- On clean runs, K4 bounds the actual average by the charged A-query weights. -/
theorem clean (source container : State) (password : Fin N) (tables : Tables (Fin N) Entropy)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N))
    (notEarly : ¬ Early2 (enrich source (outcome password container tables adversary)))
    (notCross : ¬ Cross (enrich source (outcome password container tables adversary))) :
    average (decide ((execute tables (adversary container)).1=password))
      (K4Order.bad (enrich source (outcome password container tables adversary))) ≤
    KnownPairCredit.weight (execute tables (adversary container)).1
      (execute tables (adversary container)).2 password := by
  classical
  have count := (K4.lemma_k4 source password container tables adversary notEarly notCross).trans (Nat.min_le_right _ _)
  have realCount : ((K4Order.bad (enrich source (outcome password container tables adversary))).card:ℝ) ≤
      ((execute tables (adversary container)).2.countP (QueryCounts.aFor password):ℝ) := by exact_mod_cast count
  rw [identity]
  unfold KnownPairCredit.weight
  apply min_le_min le_rfl
  apply add_le_add
  · simp only [decide_eq_true_eq,le_refl]
  · exact div_le_div_of_nonneg_right realCount (by norm_num)

end KnownPairAverage

/-! Independent nonnegative expectations can be exchanged without summability assumptions. -/
namespace MomentCommute
open GameExpectation

theorem commute {First Second : Type} (first : PMF First) (second : PMF Second)
    (value : First → Second → ENNReal) :
    moment first (fun x => moment second (value x)) =
      moment second (fun y => moment first (fun x => value x y)) := by
  simp only [moment,← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro y
  apply tsum_congr
  intro x
  ac_rfl

end MomentCommute

/-! Nonnegative expectation form of the eleven-position average. -/
namespace KnownPairAverageENN
open GameExpectation MomentTools

def average (win : Bool) (positions : Finset (Fin 11)) : ENNReal := by
  classical
  exact moment (PMF.uniformOfFintype (Fin 11))
    (fun position => if win=true ∨ position ∈ positions then 1 else 0)

/-- This is precisely a uniform random choice among the eleven programming positions. -/
theorem identity (win : Bool) (positions : Finset (Fin 11)) :
    average win positions = (if win then 1 else (positions.card:ENNReal)/11) := by
  classical
  cases win with
  | true =>
    simp only [average,true_or,if_true]
    exact constant _ _
  | false =>
    simp only [average,Bool.false_eq_true,false_or,if_false]
    have law := FreshSampling.uniform_hit_probability positions
    rw [probability] at law
    (try simp only [decide_eq_true_eq,Fintype.card_fin] at law ⊢)
    exact law

/-- Exact bridge to the real-valued min(1,win+n_bad/11) used by K4's weight bound. -/
theorem real_bridge (win : Bool) (positions : Finset (Fin 11)) :
    average win positions = ENNReal.ofReal (KnownPairAverage.average win positions) := by
  rw [identity,KnownPairAverage.identity,ENNReal.ofReal_min]
  have count : (positions.card:ENNReal)/11 ≤ 1 := by
    have small : positions.card ≤ 11 := by simpa using Finset.card_le_card (Finset.subset_univ positions)
    exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by simpa using (show (positions.card:ENNReal) ≤ 11 by exact_mod_cast small))
  cases win <;> simp only [Bool.false_eq_true,if_false,if_true,zero_add,ENNReal.ofReal_one]
  · rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_natCast]
    norm_num
    exact count
  · have nonnegative : (0:ℝ) ≤ (positions.card:ℝ)/11 := by positivity
    rw [ENNReal.ofReal_add (by norm_num) nonnegative]
    simp

end KnownPairAverageENN

/-! The actual Delta2 fractional password-credit expectation. -/
namespace KnownPairMass
open Gamma2Model GameExpectation MomentTools
open ProbabilityTools
variable {N : Nat} {Entropy : Type} [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm
attribute [local irreducible] finalize

def value (passwords : PMF (Fin N)) (kA : Nat) : ENNReal :=
  ENNReal.ofReal (FractionalTop.value (fun password => (passwords password).toReal)
    (kA/11+1) (((kA%11:Nat):ℝ)/11))

omit [Fintype Entropy] [DecidableEq Entropy] in
/-- The ranked real-mass calculation agrees exactly with the nonnegative probability-weighted sum. -/
theorem pointwise (passwords : PMF (Fin N)) (sorted : Antitone passwords) (guess : Fin N)
    (queries : List (Point (Fin N) Entropy)) (kA : Nat)
    (calls : queries.countP QueryCounts.isA ≤ kA) :
    moment passwords (fun password => ENNReal.ofReal (KnownPairCredit.weight guess queries password)) ≤
      value passwords kA := by
  have realSorted : Antitone (fun password => (passwords password).toReal) := by
    intro first second order
    exact ENNReal.toReal_mono (passwords.apply_ne_top first) (sorted order)
  have estimate := KnownPairCredit.mass_bound (fun password => (passwords password).toReal)
    realSorted (fun _ => ENNReal.toReal_nonneg) guess queries kA calls
  have exactMass : moment passwords (fun password => ENNReal.ofReal (KnownPairCredit.weight guess queries password)) =
      ENNReal.ofReal (∑ password,(passwords password).toReal*KnownPairCredit.weight guess queries password) := by
    rw [moment,tsum_fintype,ENNReal.ofReal_sum_of_nonneg (fun password _ =>
      mul_nonneg ENNReal.toReal_nonneg (KnownPairCredit.range guess queries password).1)]
    apply Finset.sum_congr rfl
    intro password _
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (passwords.apply_ne_top password)]
  rw [exactMass]
  exact ENNReal.ofReal_le_ofReal estimate

/-- The run may choose its guess and A-query allocation adaptively, but remains independent of P in Delta2. -/
theorem bound (source : State) (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N)) (kA : Nat)
    (budget : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA) :
    moment (TwoChainModel.game source passwords adversary) (fun out =>
      ENNReal.ofReal (KnownPairCredit.weight out.base.result out.base.adversaryQueries out.base.password)) ≤
      value passwords kA := by
  rw [TwoChainModel.game,moment_map,game_as_input_map,moment_map]
  unfold independentPair
  rw [MomentTools.bind]
  simp only [moment_map,Function.comp_def]
  change moment passwords (fun password => moment (inputsLaw adversary) (fun inputs =>
    ENNReal.ofReal (KnownPairCredit.weight (execute inputs.2 (adversary inputs.1)).1
      (execute inputs.2 (adversary inputs.1)).2 password))) ≤ _
  rw [MomentCommute.commute]
  apply MomentTools.bounded
  intro inputs
  exact pointwise passwords sorted (execute inputs.2 (adversary inputs.1)).1
    (execute inputs.2 (adversary inputs.1)).2 kA (budget inputs.1 inputs.2)

end KnownPairMass

/-! Actual Delta2 K2/K3/K4 assembly with the exact 419 constant. -/
namespace KnownPairAssembly
open Gamma2Model GameExpectation MomentTools
open TwoChainModel CrossModel
variable {N : Nat} {Entropy : Type} [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

def average (out : Outcome2 (Fin N) Entropy (Fin N)) : ENNReal :=
  KnownPairAverageENN.average (decide (out.base.result=out.base.password)) (K4Order.bad out)

def credit (out : Outcome2 (Fin N) Entropy (Fin N)) : ENNReal :=
  ENNReal.ofReal (KnownPairCredit.weight out.base.result out.base.adversaryQueries out.base.password)

omit [Fintype Entropy] in
/-- Exceptions contribute one only on their actual events; the clean case uses the real K4 query count. -/
theorem covered (source container : State) (password : Fin N) (tables : Tables (Fin N) Entropy)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N)) :
    average (enrich source (outcome password container tables adversary)) ≤
      credit (enrich source (outcome password container tables adversary)) +
      (if K3.test (enrich source (outcome password container tables adversary)) then 1 else 0) +
      (if K2.test (enrich source (outcome password container tables adversary)) then 1 else 0) := by
  classical
  let out := enrich source (outcome password container tables adversary)
  have small : average out ≤ 1 := by
    rw [average,KnownPairAverageENN.real_bridge]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (KnownPairAverage.bounded (decide (out.base.result=out.base.password)) (K4Order.bad out))
  by_cases early : Early2 out
  · have active : K3.test out=true := decide_eq_true early
    change average out ≤ credit out+(if K3.test out then 1 else 0)+(if K2.test out then 1 else 0)
    rw [active,if_pos rfl]
    exact small.trans ((le_add_of_nonneg_left (zero_le)).trans (le_add_of_nonneg_right (zero_le)))
  · have inactive : K3.test out=false := by simp only [K3.test,early,decide_false]
    by_cases cross : Cross out
    · have active : K2.test out=true := decide_eq_true ⟨cross,early⟩
      change average out ≤ credit out+(if K3.test out then 1 else 0)+(if K2.test out then 1 else 0)
      rw [inactive,active]
      simp only [Bool.false_eq_true,if_false,add_zero]
      rw [if_true]
      exact small.trans (le_add_of_nonneg_left (zero_le))
    · have noCross : K2.test out=false := by simp only [K2.test,cross,false_and,decide_false]
      change average out ≤ credit out+(if K3.test out then 1 else 0)+(if K2.test out then 1 else 0)
      simp only [inactive,noCross,Bool.false_eq_true,if_false,add_zero]
      rw [average,KnownPairAverageENN.real_bridge]
      exact ENNReal.ofReal_le_ofReal (KnownPairAverage.clean source container password tables adversary early cross)

/-- Full Delta2 expectation bound; 287 from K3 and 132 from Cross give 419. -/
theorem bound (source : State) (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH) :
    moment (TwoChainModel.game source passwords adversary) average ≤
      KnownPairMass.value passwords kA +
      (24*p1*kA+2*qB+419)/(2^128:ENNReal)+(2*qH+12)/(2^256:ENNReal) := by
  have included : moment (TwoChainModel.game source passwords adversary) average ≤
      moment (TwoChainModel.game source passwords adversary) credit +
      ((TwoChainModel.game source passwords adversary).map K3.test) true +
      ((TwoChainModel.game source passwords adversary).map K2.test) true := by
    rw [probability,probability,← MomentTools.add,← MomentTools.add]
    simp only [TwoChainModel.game,moment_map,Function.comp_def]
    apply G3Assembly.game_pointwise
    intro password container tables
    exact covered source container password tables adversary
  have estimate := add_le_add
    (add_le_add (KnownPairMass.bound source passwords sorted adversary kA budgetA)
      (K3.early_bound source passwords adversary p1 largest kA qB qH budgetA budgetB budgetH))
    (K2.cross_bound source passwords adversary)
  apply included.trans
  apply estimate.trans_eq
  rw [show (419:ENNReal)=287+132 by norm_num]
  simp only [ENNReal.add_div]
  abel

end KnownPairAssembly

/-! Regroup Delta2 into independent P,A,B,G and one common Y,H seed law. -/
namespace DeltaInputs
open Gamma2Model TableFactors TwoChainModel
open ProbabilityTools
variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm
abbrev Others (Password Entropy : Type) := ATable Password × BTable × GTable Entropy

def tables (other : Others Password Entropy) (h : HTable) : Tables Password Entropy :=
  ⟨other.1,other.2.1,h,other.2.2⟩

def seeds : PMF (State × HTable) := PMF.uniformOfFintype _

theorem split_seeds :
    seeds = independentPair (PMF.uniformOfFintype State) (PMF.uniformOfFintype HTable) :=
  uniform_product

def environments (passwords : PMF Password) : PMF (Password × Others Password Entropy) :=
  independentPair passwords (PMF.uniformOfFintype (Others Password Entropy))

/-- The selected programming position does not occur anywhere in this common game. -/
theorem game (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    TwoChainModel.game source passwords adversary =
      (environments passwords).bind fun env => seeds.map fun seed =>
        enrich source (outcome env.1 seed.1 (tables env.2 seed.2) adversary) := by
  unfold TwoChainModel.game Gamma2Model.game environments
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  simp_rw [factor_h]
  rw [split_seeds]
  simp only [independentPair,PMF.map_bind,PMF.bind_bind,PMF.bind_map,PMF.map_comp,Function.comp_def]
  apply congrArg (fun continuation => passwords.bind continuation)
  funext password
  exact PMF.bind_comm _ _ _

end DeltaInputs

/-! Operational identical-until-query transfer for two programmed H masks. -/
namespace HProgramming
open Gamma2Model
variable {Password Entropy Result : Type}
abbrev Input := Key × Fin 12 × Half

def point (input : Input) : Point Password Entropy := .h input.1 input.2.1 input.2.2

def updated (tables : Tables Password Entropy) (first second : Input) (left right : Half) :
    Tables Password Entropy :=
  {tables with h := Function.update (Function.update tables.h first left) second right}

/-- Both the output and full adversary query transcript agree until one of the two changed inputs. -/
theorem execution (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) (first second : Input) (left right : Half)
    (missingFirst : point first ∉ (execute tables program).2)
    (missingSecond : point second ∉ (execute tables program).2) :
    execute (updated tables first second left right) program = execute tables program := by
  apply TranscriptErasure.execute_agree program (answer tables) (answer (updated tables first second left right))
  rintro (_ | _ | ⟨key, round, half⟩ | _) member <;> try rfl
  change point (key,round,half) ∈ (execute tables program).2 at member
  have notFirst : (key,round,half) ≠ first := fun equal => missingFirst (equal ▸ member)
  have notSecond : (key,round,half) ≠ second := fun equal => missingSecond (equal ▸ member)
  simp only [answer,updated,Function.update_of_ne notFirst,Function.update_of_ne notSecond]

end HProgramming

/-! Full two-mask programming transfer before the K4 chain-coordinate identification. -/
namespace KnownPairTransfer
open Gamma2Model TableFactors K1 PathResampling
open GameExpectation MomentTools
variable {Password Entropy : Type} [DecidableEq Password]
/-- Score the actual common-table adversary on the full K1 observation. -/
def score (g : Entropy → Hash) (adversary : State → OracleComp (spec Password Entropy) Password)
    (view : Observation Password) : Bool :=
  decide ((execute ⟨view.2.1,view.2.2.1,view.2.2.2.1,g⟩ (adversary view.2.2.2.2)).1=view.1)

def changed (selected : Fin 11) (source : State) (env : Environment Password)
    (seed : State × HTable) : HProgramming.Input × HProgramming.Input :=
  let sys := K1System.system selected env.1 env.2.1 env.2.2 source
  let context := sys.rest seed.2
  let target := (sys.suffix context).symm seed.1
  (sys.first context,sys.second context target.1)

variable (selected : Fin 11) (source : State) (env : Environment Password) (g : Entropy → Hash)
  (adversary : State → OracleComp (spec Password Entropy) Password)

def winOrBad (seed : State × HTable) : Bool := by
  classical
  let before := execute (⟨env.2.1,env.2.2,seed.2,g⟩ : Tables Password Entropy) (adversary seed.1)
  exact decide (before.1=env.1 ∨ HProgramming.point (changed selected source env seed).1 ∈ before.2 ∨
    HProgramming.point (changed selected source env seed).2 ∈ before.2)

/-- No component event is transferred separately; only win-or-Bad in the unprogrammed game is used. -/
theorem pointwise
    (seed : State × HTable) :
    (if score g adversary (programmed selected source env seed) then 1 else 0 : ENNReal) ≤
      (if winOrBad selected source env g adversary seed then 1 else 0) := by
  classical
  let plain : Tables Password Entropy := ⟨env.2.1,env.2.2,seed.2,g⟩
  let before := execute plain (adversary seed.1)
  let sys := K1System.system selected env.1 env.2.1 env.2.2 source
  let context := sys.rest seed.2
  let target := (sys.suffix context).symm seed.1
  by_cases won : score g adversary (programmed selected source env seed) = true
  · have larger : winOrBad selected source env g adversary seed = true := by
      apply decide_eq_true
      change before.1=env.1 ∨ HProgramming.point (sys.first context) ∈ before.2 ∨
        HProgramming.point (sys.second context target.1) ∈ before.2
      by_cases first : HProgramming.point (sys.first context) ∈ before.2
      · exact Or.inr (Or.inl first)
      by_cases second : HProgramming.point (sys.second context target.1) ∈ before.2
      · exact Or.inr (Or.inr second)
      have same := HProgramming.execution plain (adversary seed.1) (sys.first context)
        (sys.second context target.1) ((sys.input context).1 ^^^ target.1) ((sys.input context).2 ^^^ target.2) first second
      have win : (execute (HProgramming.updated plain (sys.first context)
          (sys.second context target.1) ((sys.input context).1 ^^^ target.1) ((sys.input context).2 ^^^ target.2))
          (adversary seed.1)).1=env.1 := of_decide_eq_true won
      rw [same] at win
      exact Or.inl win
    simp only [won,larger,if_true,le_refl]
  · simp only [Bool.eq_false_iff.mpr won,Bool.false_eq_true,if_false,zero_le]

/-- Transfer for a re-sampling identity supplied with its exact distribution instances. -/
theorem transferred (seeds : PMF (State × HTable)) (original : PMF (Observation Password))
    (same : seeds.map (programmed selected source env) = original) :
    (original.map (score g adversary)) true ≤
      (seeds.map (winOrBad selected source env g adversary)) true := by
  rw [← same,← MomentTools.bool,probability]
  simp only [moment_map,Function.comp_def]
  apply mono
  intro seed
  exact pointwise selected source env g adversary seed

/-- Actual K1 source-game transfer, retaining precisely the sampler instances in its checked joint law. -/
def fixed :=
  transferred selected source env g adversary _ _ (K1.fixed selected source env)

end KnownPairTransfer

/-! Exact equality between K1's programmed H inputs and K4's actual chain points. -/
namespace KnownPairCoordinates
open Gamma2Model K1 TwoChainModel CrossModel
set_option maxHeartbeats 800000
attribute [local irreducible] forward finalize
variable {Password Entropy Result : Type}

variable (selected : Fin 11) (source container : State) (password : Password)

/-- K1's prefix ignores the two replaced rounds exactly. -/
theorem changed_first
    (a : TableFactors.ATable Password) (b : TableFactors.BTable)
    (h : TableFactors.HTable) :
    (KnownPairTransfer.changed selected source (password,a,b) (container,h)).1 =
      let right := (Lemma1.encrypt (KnownPairModel.beforeMasks selected password a b h) source).2
      (a (password,b (selected.castSucc,right)),selected.castSucc,right) := by
  simp only [KnownPairTransfer.changed,K1System.system,
    K1System.prefixState,KnownPairModel.before_fill]

/-- K1's inverse suffix uses exactly rounds 11 down to j+2 of the unprogrammed H. -/
theorem changed_second
    (a : TableFactors.ATable Password) (b : TableFactors.BTable)
    (h : TableFactors.HTable) :
    (KnownPairTransfer.changed selected source (password,a,b) (container,h)).2 =
      let right := (Lemma1.decrypt (KnownPairModel.afterMasks selected password a b h) container).1
      (a (password,b (selected.succ,right)),selected.succ,right) := by
  simp only [KnownPairTransfer.changed,K1System.system,
    KnownPairModel.after_fill,KnownPairModel.roundsEquiv]
  rfl

/-- Finite expansion of each of the eleven actual programming positions; no probabilistic premise. -/
theorem first (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    HProgramming.point
      (KnownPairTransfer.changed selected source (password,tables.a,tables.b) (container,tables.h)).1 =
      (run (enrich source (outcome password container tables adversary)) true).point
        (bIndex true selected.castSucc+2) := by
  rw [changed_first,run_point]
  fin_cases selected <;>
    simp only [chainProgram,bIndex,if_true,RoundBlocks.forward_step,
      List.cons_append,List.nil_append,List.getD_cons_succ] <;> rfl

/-- The inverse suffix gives the left half used by the backward chain's round j+1. -/
theorem second (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    HProgramming.point
      (KnownPairTransfer.changed selected source (password,tables.a,tables.b) (container,tables.h)).2 =
      (run (enrich source (outcome password container tables adversary)) false).point
        (bIndex false selected.succ+2) := by
  rw [changed_second,run_point]
  fin_cases selected <;>
    simp (disch := decide) only [chainProgram,bIndex,Bool.false_eq_true,if_false,FinalCut.finalize_step,
      List.cons_append,List.nil_append,List.getD_cons_succ] <;> rfl

end KnownPairCoordinates

/-! The two changed inputs are exactly the Bad_j events counted in K4. -/
namespace KnownPairEventCoordinates
open Gamma2Model TwoChainModel CrossModel
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]

/-- This holds without a no-Early condition: both sides describe the same actual queried points. -/
theorem event (selected : Fin 11) (source container : State) (password : Password)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Password) :
    KnownPairTransfer.winOrBad selected source (password,tables.a,tables.b) tables.g adversary (container,tables.h) =
      decide ((execute tables (adversary container)).1=password ∨
        selected ∈ K4Order.bad (enrich source (outcome password container tables adversary))) := by
  classical
  have coordinates :
      (HProgramming.point
        (KnownPairTransfer.changed selected source (password,tables.a,tables.b) (container,tables.h)).1 ∈
          (execute tables (adversary container)).2 ∨
       HProgramming.point
        (KnownPairTransfer.changed selected source (password,tables.a,tables.b) (container,tables.h)).2 ∈
          (execute tables (adversary container)).2) ↔
      selected ∈ K4Order.bad (enrich source (outcome password container tables adversary)) := by
    rw [KnownPairCoordinates.first selected source container password tables adversary,
      KnownPairCoordinates.second selected source container password tables adversary]
    let out := enrich source (outcome password container tables adversary)
    change ((run out true).point (bIndex true selected.castSucc+2) ∈ out.base.adversaryQueries ∨
      (run out false).point (bIndex false selected.succ+2) ∈ out.base.adversaryQueries) ↔ selected ∈ K4Order.bad out
    rw [← K4Order.queried_member out true (bIndex true selected.castSucc+2),
      ← K4Order.queried_member out false (bIndex false selected.succ+2)]
    simp only [K4Order.bad,Finset.mem_filter,Finset.mem_univ,true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [KnownPairTransfer.winOrBad,decide_eq_true_eq]
  exact or_congr Iff.rfl coordinates

end KnownPairEventCoordinates

/-! Actual Delta0-to-common-Delta2 bounds for each of the eleven programming positions. -/
namespace KnownPairSource
open Gamma2Model TableFactors TwoChainModel
open GameExpectation MomentTools
variable {Password Entropy : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]

/-- H is sampled inside the checked K1 real game, preserving its exact distribution instance. -/
def original (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Password) : PMF Bool :=
  (DeltaInputs.environments passwords).bind fun env =>
    (K1.realGame source (PMF.pure (env.1,env.2.1,env.2.2.1))).map
      (KnownPairTransfer.score env.2.2.2 adversary)

def winOrBad (selected : Fin 11) (out : Outcome2 Password Entropy Password) : Bool :=
  decide (out.base.result=out.base.password ∨ selected ∈ K4Order.bad out)

/-- All eleven bounds use precisely the same unprogrammed Delta2 game. -/
theorem per_position (selected : Fin 11) (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Password) :
    original source passwords adversary true ≤
      ((TwoChainModel.game source passwords adversary).map (winOrBad selected)) true := by
  rw [original,PMF.bind_apply,probability,DeltaInputs.game,MomentTools.bind]
  apply mono
  intro env
  rw [moment_map]
  have estimate := KnownPairTransfer.fixed selected source (env.1,env.2.1,env.2.2.1) env.2.2.2 adversary
  have events : KnownPairTransfer.winOrBad selected source (env.1,env.2.1,env.2.2.1) env.2.2.2 adversary =
      fun seed => winOrBad selected (enrich source (outcome env.1 seed.1 (DeltaInputs.tables env.2 seed.2) adversary)) := by
    funext seed
    exact KnownPairEventCoordinates.event selected source seed.1 env.1
      (DeltaInputs.tables env.2 seed.2) adversary
  rw [events] at estimate
  simpa only [K1.realGame,PMF.pure_bind,probability,DeltaInputs.seeds,Function.comp_def] using estimate

end KnownPairSource

/-! Actual Delta0-to-common-Delta2 eleven-position averaging, equation (2). -/
namespace KnownPairAveragedSource
open Gamma2Model GameExpectation MomentTools
variable {Password Entropy : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]

/-- The original game has no selected index; its bound averages eleven events in one Delta2 space. -/
theorem bound (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Password) :
    KnownPairSource.original source passwords adversary true ≤
      moment (TwoChainModel.game source passwords adversary) (fun out =>
        KnownPairAverageENN.average (decide (out.base.result=out.base.password)) (K4Order.bad out)) := by
  have estimate : KnownPairSource.original source passwords adversary true ≤
      moment (PMF.uniformOfFintype (Fin 11)) (fun selected =>
        ((TwoChainModel.game source passwords adversary).map (KnownPairSource.winOrBad selected)) true) := by
    calc
      _ = moment (PMF.uniformOfFintype (Fin 11)) (fun _ => KnownPairSource.original source passwords adversary true) :=
        (constant _ _).symm
      _ ≤ _ := mono _ _ _ (fun selected => KnownPairSource.per_position selected source passwords adversary)
  simp_rw [probability] at estimate
  rw [MomentCommute.commute] at estimate
  simpa only [KnownPairAverageENN.average,KnownPairSource.winOrBad,decide_eq_true_eq] using estimate

end KnownPairAveragedSource

/-! The stated coarse top bound for Theorem 4's fractional allowance. -/
namespace FractionalTopBounds
variable {N : Nat}

theorem leading_succ (p : Fin N → ℝ) (cut : Fin N) :
    FractionalMass.leadingMass p (cut.val+1) =
      FractionalMass.leadingMass p cut.val+p cut := by
  classical
  have sets : Finset.univ.filter (fun i : Fin N => i.val < cut.val+1) =
      insert cut (Finset.univ.filter (fun i : Fin N => i.val < cut.val)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Fin.ext_iff]
    omega
  have missing : cut ∉ Finset.univ.filter (fun i : Fin N => i.val < cut.val) := by simp
  unfold FractionalMass.leadingMass
  rw [sets,Finset.sum_insert missing]
  exact add_comm _ _

theorem upper (p : Fin N → ℝ) (nonnegative : ∀ i,0 ≤ p i) (whole : Nat) (part : ℝ)
    (fraction : part ≤ 1) :
    FractionalTop.value p whole part ≤ FractionalMass.leadingMass p (whole+1) := by
  classical
  by_cases available : whole < N
  · rw [FractionalTop.value,dif_pos available,leading_succ p ⟨whole,available⟩]
    apply add_le_add le_rfl
    simpa only [one_mul] using mul_le_mul_of_nonneg_right fraction (nonnegative ⟨whole,available⟩)
  · rw [FractionalTop.value,dif_neg available]
    have full : Finset.univ.filter (fun i : Fin N => i.val < whole+1) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
      have := i.isLt
      omega
    unfold FractionalMass.leadingMass
    rw [full]

theorem leading_mass (passwords : PMF (Fin N)) (count : Nat) :
    ENNReal.ofReal (FractionalMass.leadingMass (fun i => (passwords i).toReal) count) =
      RankedMass.top passwords count := by
  unfold FractionalMass.leadingMass RankedMass.top
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  apply Finset.sum_congr rfl
  intro i _
  exact ENNReal.ofReal_toReal (passwords.apply_ne_top i)

/-- Fractional credit never exceeds credit for one additional whole password. -/
theorem known_pair (passwords : PMF (Fin N)) (kA : Nat) :
    KnownPairMass.value passwords kA ≤ RankedMass.top passwords (kA/11+2) := by
  have remaining : (((kA%11:Nat):ℝ)/11) ≤ 1 := by
    have small : ((kA%11:Nat):ℝ) ≤ 11 := by exact_mod_cast Nat.le_of_lt (Nat.mod_lt kA (by decide))
    exact (div_le_one (by norm_num)).mpr small
  have estimate := ENNReal.ofReal_le_ofReal (upper (fun i => (passwords i).toReal)
    (fun _ => ENNReal.toReal_nonneg) (kA/11+1) _ remaining)
  exact estimate.trans_eq (leading_mass passwords (kA/11+2))

end FractionalTopBounds

/-! The full original-game known-pair bound, with fractional credit and epsilon_K. -/
namespace Theorem4
open Gamma2Model MomentTools
variable {N : Nat} {Entropy : Type} [Fintype Entropy] [DecidableEq Entropy]

/-- All source-game transfers, eleven-position averaging and the K2/K3/K4 assembly are discharged. -/
theorem bound (source : State) (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH) :
    KnownPairSource.original source passwords adversary true ≤
      KnownPairMass.value passwords kA +
      (24*p1*kA+2*qB+419)/(2^128:ENNReal)+(2*qH+12)/(2^256:ENNReal) :=
  (KnownPairAveragedSource.bound source passwords adversary).trans
    (KnownPairAssembly.bound source passwords sorted adversary p1 largest kA qB qH budgetA budgetB budgetH)

/-- Independent private coins preserve the same hard-budget bound. -/
theorem randomized {Strategy : Type} (coins : PMF Strategy) (source : State)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : Strategy → State → OracleComp (spec (Fin N) Entropy) (Fin N)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ strategy container tables,(execute tables (adversary strategy container)).2.countP QueryCounts.isH ≤ qH) :
    (coins.bind fun strategy => KnownPairSource.original source passwords (adversary strategy)) true ≤
      KnownPairMass.value passwords kA +
      (24*p1*kA+2*qB+419)/(2^128:ENNReal)+(2*qH+12)/(2^256:ENNReal) := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact bound source passwords sorted (adversary strategy) p1 largest kA qB qH
    (budgetA strategy) (budgetB strategy) (budgetH strategy)

/-- The source's coarser whole-password consequence of the fractional bound. -/
theorem coarse (source : State) (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH) :
    KnownPairSource.original source passwords adversary true ≤
      RankedMass.top passwords (kA/11+2) +
      (24*p1*kA+2*qB+419)/(2^128:ENNReal)+(2*qH+12)/(2^256:ENNReal) :=
  (bound source passwords sorted adversary p1 largest kA qB qH budgetA budgetB budgetH).trans
    (add_le_add (add_le_add (FractionalTopBounds.known_pair passwords kA) le_rfl) le_rfl)

end Theorem4

end
end MhfeLean
