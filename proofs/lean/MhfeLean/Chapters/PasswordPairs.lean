import Mathlib.Data.Fintype.Fin
import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.KnownPairBound
import MhfeLean.Chapters.Probability
import MhfeLean.Chapters.ShortSources

namespace MhfeLean
noncomputable section

/-! # Pair probability mass and conditional redraws
-/

/-! Exact adaptive pair-mass accounting with independent password and passphrase. -/
namespace PairMass
open ProbabilityTools GameExpectation MomentTools

/-- A finite candidate set has precisely the sum of its point masses, even in an infinite alphabet. -/
theorem finite_membership {Value : Type} [DecidableEq Value]
    (distribution : PMF Value) (chosen : Finset Value) :
    moment distribution (fun value => if value ∈ chosen then 1 else 0) =
      ∑ value ∈ chosen,distribution value := by
  simp only [moment,mul_ite,mul_one,mul_zero]
  rw [tsum_eq_sum (s := chosen) (fun item outside => if_neg outside)]
  apply Finset.sum_congr rfl
  intro item member
  exact if_pos member

variable {N : Nat} {Passphrase View : Type} [DecidableEq Passphrase]

variable (passwords : PMF (Fin N)) (passphrases : PMF Passphrase)

theorem membership
    (chosen : Finset (Fin N × Passphrase)) :
    moment (independentPair passwords passphrases) (fun pair => if pair ∈ chosen then 1 else 0) =
      W1.mass passwords passphrases chosen := by
  rw [finite_membership]
  unfold W1.mass
  apply Finset.sum_congr rfl
  rintro ⟨password,passphrase⟩ _
  exact independentPair_apply passwords passphrases password passphrase

/-- All adaptivity is in the public run, sampled independently of both secrets. -/
theorem exact_adaptive (views : PMF View)
    (chosen : View → Finset (Fin N × Passphrase)) :
    moment (independentPair (independentPair passwords passphrases) views)
      (fun world => if world.1 ∈ chosen world.2 then 1 else 0) =
      moment views (fun view => W1.mass passwords passphrases (chosen view)) := by
  classical
  have reverse : independentPair (independentPair passwords passphrases) views =
      views.bind fun view => (independentPair passwords passphrases).map fun pair => (pair,view) :=
    PMF.bind_comm _ _ _
  rw [reverse,MomentTools.bind]
  apply congrArg (moment views)
  funext view
  rw [moment_map]
  exact membership passwords passphrases (chosen view)

/-- The counts may depend on the complete run; the inequality is an expectation over those runs. -/
theorem adaptive (sorted : Antitone passwords)
    (views : PMF View) (chosen : View → Finset (Fin N × Passphrase)) :
    moment (independentPair (independentPair passwords passphrases) views)
      (fun world => if world.1 ∈ chosen world.2 then 1 else 0) ≤
      moment views (fun view => W1.top2 passwords passphrases
        ((chosen view).image Prod.fst).card (chosen view).card) := by
  classical
  rw [exact_adaptive]
  apply mono
  intro view
  exact W1.lemma_w1 passwords passphrases sorted (chosen view) _ _ le_rfl le_rfl

/-- Fixed budgets restrict rows and tested pairs separately. -/
theorem bounded (sorted : Antitone passwords)
    (views : PMF View) (chosen : View → Finset (Fin N × Passphrase)) (rows pairs : Nat)
    (rowBound : ∀ view,((chosen view).image Prod.fst).card ≤ rows)
    (pairBound : ∀ view,(chosen view).card ≤ pairs) :
    moment (independentPair (independentPair passwords passphrases) views)
      (fun world => if world.1 ∈ chosen world.2 then 1 else 0) ≤
      W1.top2 passwords passphrases rows pairs := by
  classical
  rw [exact_adaptive]
  apply MomentTools.bounded
  intro view
  exact W1.lemma_w1 passwords passphrases sorted (chosen view) rows pairs (rowBound view) (pairBound view)

end PairMass

/-! Exact top2 for two independent uniform finite dictionaries. -/
namespace UniformTop2
variable {N M : Nat}

/-- With constant pair mass, a candidate set's mass depends only on its cardinality. -/
theorem mass (first second : ENNReal) (pairs : Finset (Fin N × Fin M)) :
    W1.mass (fun _ => first) (fun _ => second) pairs = pairs.card*(first*second) := by
  simp only [W1.mass,Finset.sum_const,nsmul_eq_mul]

/-- Both row and pair caps matter; rows beyond the first dictionary's size are unavailable. -/
theorem exact_top (first second : ENNReal) (rows pairs : Nat) : W1.top2 (N := N) (Passphrase := Fin M) (fun _ => first) (fun _ => second) rows pairs =
      (min pairs (min N rows*M) : Nat)*(first*second) := by
  classical
  let family : Finset (Fin N × Fin M) :=
    (Finset.univ.filter (fun row : Fin N => row.val < rows)).product Finset.univ
  have size : family.card = min N rows*M := by
    dsimp only [family]
    rw [Finset.product_eq_sprod,Finset.card_product]
    simp only [Fin.card_filter_val_lt,Finset.card_univ,Fintype.card_fin]
  have included (chosen : Finset (Fin N × Fin M)) (restricted : ∀ pair ∈ chosen,pair.1.val < rows) :
      chosen ⊆ family := by
    intro pair member
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,restricted pair member⟩,Finset.mem_univ _⟩
  apply le_antisymm
  · apply iSup_le
    intro chosen
    apply iSup_le
    intro count
    apply iSup_le
    intro restricted
    rw [mass]
    apply mul_le_mul_left
    exact_mod_cast Nat.le_min.mpr ⟨count,(Finset.card_le_card (included chosen restricted)).trans_eq size⟩
  · have enough : min pairs (min N rows*M) ≤ family.card := by rw [size]; exact Nat.min_le_right _ _
    obtain ⟨chosen,subset,count⟩ := Finset.exists_subset_card_eq enough
    have restricted : ∀ pair ∈ chosen,pair.1.val < rows := by
      intro pair member
      exact (Finset.mem_filter.mp (Finset.mem_product.mp (subset member)).1).2
    have allowed : chosen.card ≤ pairs := by rw [count]; exact Nat.min_le_left _ _
    have lower : W1.mass (fun _ : Fin N => first) (fun _ : Fin M => second) chosen ≤
        W1.top2 (fun _ => first) (fun _ => second) rows pairs := le_iSup_of_le chosen (le_iSup_of_le allowed (le_iSup_of_le restricted (le_refl (W1.mass (fun _ => first) (fun _ => second) chosen))))
    simpa only [mass,count] using lower

end UniformTop2

/-! The uniform-secret one-cost-budget calculation uses reused decrypted phrases. -/
namespace PairCost

/-- Row work is paid once, then seed work is paid separately for each pair. -/
theorem paid (rows pairs choices costA costS budget : ℝ) (nonnegativeA : 0 ≤ costA)
    (nonnegativeS : 0 ≤ costS) (nonnegativeChoices : 0 ≤ choices)
    (limit : 12*costA*rows+costS*pairs ≤ budget) :
    min pairs (rows*choices)*(12*costA+choices*costS) ≤ budget*choices := by
  calc
    _ = 12*costA*min pairs (rows*choices)+(choices*costS)*min pairs (rows*choices) := by ring
    _ ≤ 12*costA*(rows*choices)+(choices*costS)*pairs :=
      add_le_add
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg nonnegativeChoices nonnegativeS))
    _ = (12*costA*rows+costS*pairs)*choices := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right limit nonnegativeChoices

/-- Divide by the size of the pair dictionary; this is a bound at a fixed budget, not expected stopping cost. -/
theorem probability (rows pairs passwords phrases costA costS budget : ℝ)
    (positivePasswords : 0 < passwords) (positivePhrases : 0 < phrases) (positiveA : 0 < costA)
    (nonnegativeS : 0 ≤ costS) (limit : 12*costA*rows+costS*pairs ≤ budget) :
    min pairs (rows*phrases)/(passwords*phrases) ≤
      budget/(passwords*(12*costA+phrases*costS)) := by
  have weighted := paid rows pairs phrases costA costS budget positiveA.le nonnegativeS positivePhrases.le limit
  apply (div_le_div_iff₀ (mul_pos positivePasswords positivePhrases)
    (mul_pos positivePasswords (by positivity))).2
  have scaled := mul_le_mul_of_nonneg_left weighted positivePasswords.le
  nlinarith

end PairCost

/-! The passphrase-weighted hidden-half hit probability in Theorem 5. -/
namespace WeightedPairHit
open ProbabilityTools GameExpectation MomentTools
variable {Answer Passphrase : Type} [Fintype Answer] [Nonempty Answer]
  [DecidableEq Answer] [DecidableEq Passphrase]

/-- A hit must guess both the uniform hidden value and the independent secret passphrase. -/
theorem bound (passphrases : PMF Passphrase) (s1 : ENNReal)
    (largest : ∀ phrase,passphrases phrase ≤ s1) (matching : Finset (Answer × Passphrase))
    (limit : Nat) (size : matching.card ≤ limit) :
    moment (independentPair (PMF.uniformOfFintype Answer) passphrases)
      (fun pair => if pair ∈ matching then 1 else 0) ≤
      s1*limit/(Fintype.card Answer:ENNReal) := by
  classical
  rw [PairMass.finite_membership]
  calc
    _ ≤ ∑ _ ∈ matching,(Fintype.card Answer:ENNReal)⁻¹*s1 := by
      apply Finset.sum_le_sum
      rintro ⟨answer,phrase⟩ _
      rw [independentPair_apply,PMF.uniformOfFintype_apply]
      exact mul_le_mul_right (largest phrase) _
    _ = (matching.card:ENNReal)*((Fintype.card Answer:ENNReal)⁻¹*s1) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (limit:ENNReal)*((Fintype.card Answer:ENNReal)⁻¹*s1) := by
      apply mul_le_mul_left
      exact_mod_cast size
    _ = _ := by rw [div_eq_mul_inv]; ac_rfl

end WeightedPairHit

/-! Adaptive fresh-answer sampling retains the independent secret-passphrase factor. -/
namespace FreshPairHit
open ProbabilityTools FreshSampling OracleTree
open GameExpectation MomentTools
variable {Domain Answer Context Passphrase : Type} [DecidableEq Domain]
  [Fintype Domain] [Fintype Answer] [Nonempty Answer] [DecidableEq Answer] [DecidableEq Passphrase]

def hit (matching : Context → Finset (Answer × Passphrase)) (phrase : Passphrase) :
    Option ((Domain × Context) × Answer) → Bool
  | none => false
  | some ((_,context),answer) => decide ((answer,phrase) ∈ matching context)

omit [DecidableEq Answer] [DecidableEq Passphrase] in
/-- Q is sampled independently and is never supplied to the adaptive stopping program. -/
theorem law (program : Program Domain Answer (Domain × Context)) (phrases : PMF Passphrase) :
    independentPair phrases ((PMF.uniformOfFintype (Domain → Answer)).map (observedTable program)) =
      (PMF.uniformOfFintype (Domain → Answer)).bind fun table =>
        (independentPair (PMF.uniformOfFintype Answer) phrases).map fun pair =>
          (pair.2,(selectFresh program table).map (fun chosen => (chosen,pair.1))) := by
  rw [fresh_query_distribution]
  unfold independentPair
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  rw [PMF.bind_comm phrases (PMF.uniformOfFintype (Domain → Answer))]
  apply congrArg (fun continuation => (PMF.uniformOfFintype (Domain → Answer)).bind continuation)
  funext table
  exact PMF.bind_comm _ _ _

/-- Even with adaptively selected context, every tested pair must match the same independent Q. -/
theorem bound (program : Program Domain Answer (Domain × Context)) (phrases : PMF Passphrase)
    (matching : Context → Finset (Answer × Passphrase)) (s1 : ENNReal)
    (largest : ∀ phrase,phrases phrase ≤ s1) (limit : Nat)
    (size : ∀ context,(matching context).card ≤ limit) :
    ((independentPair phrases ((PMF.uniformOfFintype (Domain → Answer)).map (observedTable program))).map
      (fun pair => hit matching pair.1 pair.2)) true ≤ s1*limit/(Fintype.card Answer:ENNReal) := by
  rw [law,PMF.map_bind,PMF.bind_apply]
  change moment (PMF.uniformOfFintype (Domain → Answer)) _ ≤ _
  apply MomentTools.bounded
  intro table
  rw [PMF.map_comp,probability]
  cases selected : selectFresh program table with
  | none =>
    simp only [Option.map_none,Function.comp_def,hit,Bool.false_eq_true,if_false]
    rw [constant]
    exact zero_le
  | some chosen =>
    simpa only [selected,Option.map_some,Function.comp_def,hit,decide_eq_true_eq] using
      WeightedPairHit.bound phrases s1 largest (matching chosen.2) limit (size chosen.2)

end FreshPairHit

/-!
Discrete statistical closeness is expressed by both event-probability
inequalities for every Boolean test. Coupling with identical outcomes off Bad
bounds this advantage without assuming an oracle-programming axiom.
-/
namespace StatisticalClose
open GameExpectation MomentTools
variable {Output Seed : Type}

def Close (first second : PMF Output) (error : ENNReal) : Prop :=
  ∀ test : Output → Bool,
    (first.map test) true ≤ (second.map test) true + error ∧
    (second.map test) true ≤ (first.map test) true + error

private theorem indicator (first second bad : Bool) (same : bad = false → first = second) :
    (if first then (1 : ENNReal) else 0) ≤
      (if second then 1 else 0) + (if bad then 1 else 0) := by
  cases first <;> cases second <;> cases bad <;> simp_all

/-- The bound is on the entire output distribution, not only a preselected success event. -/
theorem coupling (distribution : PMF Seed) (first second : Seed → Output) (bad : Seed → Bool)
    (same : ∀ seed, bad seed = false → first seed = second seed) :
    Close (distribution.map first) (distribution.map second) ((distribution.map bad) true) := by
  intro test
  have bound (f g : Seed → Output) (agree : ∀ seed, bad seed = false → f seed = g seed) :
      ((distribution.map f).map test) true ≤ ((distribution.map g).map test) true + (distribution.map bad) true := by
    rw [PMF.map_comp, PMF.map_comp, probability, probability, probability]
    rw [← MomentTools.add]
    apply mono
    intro seed
    exact indicator _ _ _ (fun clean => congrArg test (agree seed clean))
  exact ⟨bound first second same, bound second first (fun seed clean => (same seed clean).symm)⟩

/-- Exact game identities preserve statistical closeness. -/
theorem of_eq (first second : PMF Output) (same : first = second) : Close first second 0 := by
  subst second
  intro test
  simp only [add_zero, le_refl, and_self]

theorem mono (first second : PMF Output) (old new : ENNReal) (close : Close first second old)
    (larger : old ≤ new) : Close first second new := by
  intro test
  obtain ⟨forward, backward⟩ := close test
  exact ⟨forward.trans (add_le_add le_rfl larger), backward.trans (add_le_add le_rfl larger)⟩

end StatisticalClose

/-! Composition of whole-output statistical bounds, including external independent context. -/
namespace CloseComposition
open StatisticalClose GameExpectation MomentTools
variable {Context Output : Type}

theorem trans (first middle last : PMF Output) (left right : ENNReal) (a : Close first middle left)
    (b : Close middle last right) : Close first last (left+right) := by
  intro test
  obtain ⟨af,ab⟩ := a test
  obtain ⟨bf,bb⟩ := b test
  constructor
  · calc
      _ ≤ (middle.map test) true+left := af
      _ ≤ ((last.map test) true+right)+left := add_le_add bf le_rfl
      _ = _ := by rw [add_assoc, add_comm right left]
  · calc
      _ ≤ (middle.map test) true+right := bb
      _ ≤ ((first.map test) true+left)+right := add_le_add ab le_rfl
      _ = _ := by rw [add_assoc]

/-- A context is drawn once from the same prior in both experiments. -/
theorem bind (prior : PMF Context) (first second : Context → PMF Output) (error : Context → ENNReal)
    (bound : ∀ context, Close (first context) (second context) (error context)) :
    Close (prior.bind first) (prior.bind second) (moment prior error) := by
  intro test
  have score (distribution : Context → PMF Output) :
      (((prior.bind distribution).map test) true) = moment prior (fun context => ((distribution context).map test) true) := by
    simp only [PMF.map_bind, PMF.bind_apply, moment]
  rw [score, score]
  rw [← MomentTools.add, ← MomentTools.add]
  exact ⟨mono prior _ _ (fun context => (bound context test).1),
    mono prior _ _ (fun context => (bound context test).2)⟩

/-- Deterministic postprocessing of the entire view cannot increase statistical advantage. -/
theorem map {Other : Type} (first second : PMF Output) (error : ENNReal)
    (close : Close first second error) (project : Output → Other) :
    Close (first.map project) (second.map project) error := by
  intro test
  simpa only [PMF.map_comp] using close (test ∘ project)

end CloseComposition

/-! A refused first attempt may be replaced by any later procedure, including failure. -/
namespace RefusalCoupling
open StatisticalClose GameExpectation MomentTools
variable {Output : Type}

def replace (law : PMF Output) (bad : Output → Bool) (later : Output → PMF Output) : PMF Output :=
  law.bind fun output => if bad output then later output else PMF.pure output

/-- No conditional success assumption is made about the later procedure. -/
theorem close (law : PMF Output) (bad : Output → Bool) (later : Output → PMF Output) :
    Close law (replace law bad later) ((law.map bad) true) := by
  have pointwise (output : Output) :
      Close (PMF.pure output) (if bad output then later output else PMF.pure output)
        (if bad output then 1 else 0) := by
    cases hit : bad output with
    | false => exact of_eq _ _ rfl
    | true =>
      intro test
      constructor
      · exact ((PMF.pure output).map test).coe_le_one true |>.trans (le_add_of_nonneg_left (zero_le))
      · exact ((later output).map test).coe_le_one true |>.trans (le_add_of_nonneg_left (zero_le))
  have mixed := CloseComposition.bind law (fun output => PMF.pure output)
    (fun output => if bad output then later output else PMF.pure output) (fun output => if bad output then 1 else 0) pointwise
  simpa only [PMF.bind_pure,replace,← probability] using mixed

/-- Every success bound transfers after adding only the probability of the first refusal. -/
theorem success_bound (law : PMF Output) (bad test : Output → Bool) (later : Output → PMF Output)
    (bound : ENNReal) (original : (law.map test) true ≤ bound) :
    ((replace law bad later).map test) true ≤ bound + (law.map bad) true :=
  ((close law bad later test).2).trans (add_le_add original le_rfl)

end RefusalCoupling

/-! Coupling a conditional redraw to the first unconditional sample. -/
namespace ConditionalRedraw
open RefusalCoupling GameExpectation MomentTools
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition
variable {Value : Type}

def mass (law : PMF Value) (allowed : Value → Prop) : ENNReal := by
  classical
  exact ∑' value,if allowed value then law value else 0

/-- The accepted and rejected masses partition one unconditional draw. -/
theorem partition (law : PMF Value) (allowed : Value → Prop) :
    mass law allowed + mass law (fun value => ¬ allowed value) = 1 := by
  classical
  unfold mass
  rw [← ENNReal.tsum_add]
  calc
    _ = ∑' value,law value := tsum_congr (fun value => by
      by_cases accepts : allowed value <;> simp [accepts])
    _ = 1 := PMF.tsum_coe law

/-- A nonempty accepted support gives positive, finite normalizing mass. -/
theorem positive (law : PMF Value) (allowed : Value → Prop)
    (possible : ∃ value,allowed value ∧ value ∈ law.support) :
    mass law allowed ≠ 0 ∧ mass law allowed ≠ ⊤ := by
  classical
  obtain ⟨value,accepts,support⟩ := possible
  have below : law value ≤ mass law allowed := by
    have bound := ENNReal.le_tsum (f := fun value => if allowed value then law value else 0) value
    (try simp only [if_pos accepts] at bound ⊢)
    exact bound
  constructor
  · intro zero
    rw [zero] at below
    change law value ≠ 0 at support
    exact support (le_antisymm below (zero_le))
  · have bound : mass law allowed ≤ 1 := by
      unfold mass
      rw [← PMF.tsum_coe law]
      apply ENNReal.tsum_le_tsum
      intro value
      split_ifs <;> simp only [le_refl,zero_le]
    exact ne_top_of_le_ne_top (by simp) bound

/-- Keep an allowed first draw; replace a rejected draw with the chosen conditional law. -/
def trial (law : PMF Value) (allowed : Value → Prop) (replacement : PMF Value) : PMF Value := by
  classical
  exact law.bind fun value => if allowed value then PMF.pure value else replacement

/-- The first accepted contribution and redraw contribution are counted separately. -/
theorem trial_apply [DecidableEq Value] (law : PMF Value) (allowed : Value → Prop)
    (replacement : PMF Value) (output : Value) :
    trial law allowed replacement output =
      (if allowed output then law output else 0)+replacement output*mass law (fun value => ¬allowed value) := by
  classical
  rw [trial,PMF.bind_apply]
  have summand (value : Value) :
      law value*(if allowed value then PMF.pure value else replacement) output =
      (if value=output then (if allowed output then law output else 0) else 0)+
        (if ¬allowed value then law value else 0)*replacement output := by
    by_cases same : value=output
    · subst value
      by_cases accepts : allowed output <;> simp [accepts,PMF.pure_apply]
    · have reverse : output ≠ value := Ne.symm same
      by_cases accepts : allowed value <;> simp [accepts,same,reverse,PMF.pure_apply]
  simp_rw [summand]
  rw [ENNReal.tsum_add,tsum_ite_eq,ENNReal.tsum_mul_right]
  rw [mul_comm]
  unfold mass
  congr 2
  apply tsum_congr
  intro value
  by_cases accepts : allowed value <;> simp [accepts]

/-- The kept-first-draw coupling has exactly the intended normalized conditional marginal. -/
theorem conditional [DecidableEq Value] (law : PMF Value) (allowed : Value → Prop)
    (possible : ∃ value,allowed value ∧ value ∈ law.support) :
    trial law allowed (law.filter {value | allowed value} possible) =
      law.filter {value | allowed value} possible := by
  classical
  have normalizer := positive law allowed possible
  ext output
  rw [trial_apply]
  have scaled : (law.filter {value | allowed value} possible) output*mass law allowed =
      (if allowed output then law output else 0) := by
    rw [PMF.filter_apply]
    change ((if allowed output then law output else 0)*(mass law allowed)⁻¹)*mass law allowed = _
    rw [mul_assoc,ENNReal.inv_mul_cancel normalizer.1 normalizer.2,mul_one]
  rw [← scaled,← mul_add,partition,mul_one]

def rejected (allowed : Value → Prop) : Value → Bool := by
  classical
  exact fun value => decide (¬allowed value)

/-- Event notation and subdistribution mass express the same rejected first sample. -/
theorem rejected_probability (law : PMF Value) (allowed : Value → Prop) :
    (law.map (rejected allowed)) true = mass law (fun value => ¬allowed value) := by
  classical
  rw [probability]
  unfold moment mass
  apply tsum_congr
  intro value
  by_cases accepts : allowed value <;> simp [rejected,accepts]

/-- Conditioning changes every event by at most the probability that the first draw was rejected. -/
theorem close [DecidableEq Value] (law : PMF Value) (allowed : Value → Prop)
    (possible : ∃ value,allowed value ∧ value ∈ law.support) :
    StatisticalClose.Close law (law.filter {value | allowed value} possible)
      (mass law (fun value => ¬allowed value)) := by
  classical
  let filtered := law.filter {value | allowed value} possible
  have description : RefusalCoupling.replace law (rejected allowed) (fun _ => filtered) =
      trial law allowed filtered := by
    unfold RefusalCoupling.replace trial
    congr 1
    funext value
    by_cases accepts : allowed value <;> simp [rejected,accepts]
  have estimate := RefusalCoupling.close law (rejected allowed) (fun _ => filtered)
  rw [description,conditional,rejected_probability] at estimate
  exact estimate

end ConditionalRedraw

end
end MhfeLean
