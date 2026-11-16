import MhfeLean.Chapters.WalletRecovery

namespace MhfeLean
noncomputable section

/-! # The number of trials (DESIGN-NOTES A.6, "The number of trials")

A generation under the wallet-check profile may reveal the pass/fail outcomes of its trials, their
number, and a duration that depends only on these and on independent coins. For the sequential rule
the outcomes are given by the number of failures before the first pass. Below, the adversary and the
response after a refusal are families indexed by that number; the randomized forms add private
coins, which give the duration. Every bound of Theorem 5 and of Corollary W5 then holds with
`2^-120` added:

- on fixed tables the number of failures is geometric with the pass rate `p_U` of the tables and
  independent of the selected value (`WalletCount.real`, the law of the actual loop by
  `WalletCount.completed_loop` and `WalletCount.capped_close`);
- replacing `p_U` by the ideal rate `2^-16` changes every test of the whole game by at most
  `2^16·|p_U - 2^-16|` on each table (`WalletCount.close`, `TrialLaws.kernel`), which is at most
  `2^-120` on average over uniform tables (`TrialDeviation.gap_bound`);
- with the ideal rate the number is independent of everything else and is a private coin of the
  adversary (`TrialEnvironment.ideal_eq`, `Theorem5Randomized`, `W5Randomized`).

Not stated here: other selection rules, such as `w` workers with `(w - 1)·2^-136` more.
-/

namespace TrialLaws
open StatisticalClose GameExpectation MomentTools

/-- The number of failed trials before the first pass, each trial passing with probability `p`. -/
def failures (p : ENNReal) (positive : 0 < p) (atMost : p ≤ 1) : PMF ℕ :=
  ⟨fun n => (1 - p) ^ n * p, by
    rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
      ENNReal.sub_sub_cancel ENNReal.one_ne_top atMost]
    exact ENNReal.inv_mul_cancel positive.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top atMost)⟩

theorem failures_apply (p : ENNReal) (positive : 0 < p) (atMost : p ≤ 1) (n : ℕ) :
    failures p positive atMost n = (1 - p) ^ n * p := rfl

/-- One trial first: a pass with probability `p`, otherwise one more failure. -/
theorem renewal (p : ENNReal) (positive : 0 < p) (atMost : p ≤ 1) (test : ℕ → Bool) :
    ((failures p positive atMost).map test) true =
      (if test 0 then p else 0) + (1 - p) * ((failures p positive atMost).map (fun n => test (n+1))) true := by
  simp only [PMF.map_apply, failures_apply]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, one_mul, pow_succ]
  congr 1
  · by_cases h : test 0 <;> simp [h]
  · rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases h : test (n+1) <;> simp [h, mul_comm, mul_left_comm]

/-- A bounded quantity that is at most `c + r` times itself after a shift is at most `c/(1 - r)`. -/
theorem fixed_point {Index : Type} [Nonempty Index] (D : Index → ℝ) (shift : Index → Index) (c r : ℝ)
    (nonneg : 0 ≤ r) (below : r < 1) (bounded : ∀ i, D i ≤ 1) (step : ∀ i, D i ≤ c + r * D (shift i)) :
    ∀ i, D i ≤ c / (1 - r) := by
  have above : BddAbove (Set.range D) := ⟨1, by rintro _ ⟨i, rfl⟩; exact bounded i⟩
  have top : (⨆ i, D i) ≤ c + r * ⨆ i, D i :=
    ciSup_le fun i => (step i).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_ciSup above (shift i)) nonneg))
  intro i
  have here := le_ciSup above i
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The probability of a test as a real number. -/
def chance {Output : Type} (law : PMF Output) (test : Output → Bool) : ℝ := ((law.map test) true).toReal

theorem chance_le_one {Output : Type} (law : PMF Output) (test : Output → Bool) : chance law test ≤ 1 := by
  unfold chance
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one (law.map test) true)

theorem chance_nonneg {Output : Type} (law : PMF Output) (test : Output → Bool) : 0 ≤ chance law test :=
  ENNReal.toReal_nonneg

theorem renewal_real (p : ENNReal) (positive : 0 < p) (atMost : p ≤ 1) (test : ℕ → Bool) :
    chance (failures p positive atMost) test =
      p.toReal * (if test 0 then 1 else 0) + (1 - p.toReal) * chance (failures p positive atMost) (fun n => test (n+1)) := by
  have finite : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top atMost
  unfold chance
  rw [renewal p positive atMost test, ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le atMost ENNReal.one_ne_top]
  · by_cases h : test 0 <;> simp [h]
  · by_cases h : test 0 <;> simp [h, finite]
  · exact ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top) (PMF.apply_ne_top _ _)

/-- The numbers of failures with pass probabilities `p` and `q` differ on every test by at most
`|p - q| / q`. -/
theorem close (p q : ENNReal) (positiveP : 0 < p) (atMostP : p ≤ 1) (positiveQ : 0 < q) (atMostQ : q ≤ 1) :
    Close (failures p positiveP atMostP) (failures q positiveQ atMostQ) ((p - q + (q - p)) / q) := by
  have finiteP : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top atMostP
  have finiteQ : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top atMostQ
  set a := p.toReal
  set b := q.toReal
  have a1 : a ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using atMostP)
  have b0 : 0 < b := ENNReal.toReal_pos positiveQ.ne' finiteQ
  have b1 : b ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using atMostQ)
  have a0 : 0 ≤ a := ENNReal.toReal_nonneg
  let P := failures p positiveP atMostP
  let Q := failures q positiveQ atMostQ
  have gapReal : ((p - q + (q - p)) / q).toReal = |a - b| / b := by
    rw [ENNReal.toReal_div]
    congr 1
    rcases le_total p q with h | h
    · rw [tsub_eq_zero_of_le h, zero_add, ENNReal.toReal_sub_of_le h finiteQ, abs_sub_comm, abs_of_nonneg]
      exact sub_nonneg.mpr ((ENNReal.toReal_le_toReal finiteP finiteQ).mpr h)
    · rw [tsub_eq_zero_of_le h, add_zero, ENNReal.toReal_sub_of_le h finiteP, abs_of_nonneg]
      exact sub_nonneg.mpr ((ENNReal.toReal_le_toReal finiteQ finiteP).mpr h)
  -- Both differences are bounded by the fixed point of the one-step recursion.
  have shiftStep (first second : PMF ℕ) (x y : ℝ) (rf : ∀ t, chance first t = x * (if t 0 then 1 else 0) +
      (1 - x) * chance first (fun n => t (n+1)))
      (rs : ∀ t, chance second t = y * (if t 0 then 1 else 0) + (1 - y) * chance second (fun n => t (n+1)))
      (x0 : 0 ≤ x) (x1 : x ≤ 1) (y0 : 0 ≤ y) (y1 : y ≤ 1) :
      ∀ t, chance first t - chance second t ≤ |x - y| + (1 - y) *
        (chance first (fun n => t (n+1)) - chance second (fun n => t (n+1))) := by
    intro t
    rw [rf t, rs t]
    have hb : |(if t 0 then (1:ℝ) else 0) - chance first (fun n => t (n+1))| ≤ 1 := by
      have := chance_le_one first (fun n => t (n+1))
      have := chance_nonneg first (fun n => t (n+1))
      rw [abs_le]; constructor <;> split_ifs <;> linarith
    have key : (x - y) * ((if t 0 then (1:ℝ) else 0) - chance first (fun n => t (n+1))) ≤ |x - y| := by
      calc _ ≤ |(x - y) * ((if t 0 then (1:ℝ) else 0) - chance first (fun n => t (n+1)))| := le_abs_self _
        _ = |x - y| * |(if t 0 then (1:ℝ) else 0) - chance first (fun n => t (n+1))| := abs_mul _ _
        _ ≤ |x - y| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = |x - y| := mul_one _
    nlinarith
  have rP := renewal_real p positiveP atMostP
  have rQ := renewal_real q positiveQ atMostQ
  have forward := fixed_point (fun t => chance P t - chance Q t) (fun t n => t (n+1)) |a - b| (1 - b)
    (by linarith) (by linarith) (fun t => by have := chance_le_one P t; have := chance_nonneg Q t; linarith)
    (shiftStep P Q a b rP rQ a0 a1 b0.le b1)
  have backward := fixed_point (fun t => chance Q t - chance P t) (fun t n => t (n+1)) |b - a| (1 - b)
    (by linarith) (by linarith) (fun t => by have := chance_le_one Q t; have := chance_nonneg P t; linarith)
    (fun t => by
      have := shiftStep Q P b a rQ rP b0.le b1 a0 a1 t
      -- the same recursion read with the roles of the two laws exchanged keeps the factor 1 - b
      rw [rQ t, rP t]
      have hb : |(if t 0 then (1:ℝ) else 0) - chance P (fun n => t (n+1))| ≤ 1 := by
        have := chance_le_one P (fun n => t (n+1))
        have := chance_nonneg P (fun n => t (n+1))
        rw [abs_le]; constructor <;> split_ifs <;> linarith
      have key : (b - a) * ((if t 0 then (1:ℝ) else 0) - chance P (fun n => t (n+1))) ≤ |b - a| := by
        calc _ ≤ |(b - a) * ((if t 0 then (1:ℝ) else 0) - chance P (fun n => t (n+1)))| := le_abs_self _
          _ = |b - a| * |(if t 0 then (1:ℝ) else 0) - chance P (fun n => t (n+1))| := abs_mul _ _
          _ ≤ |b - a| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ = |b - a| := mul_one _
      nlinarith)
  intro test
  have f := forward test
  have g := backward test
  rw [show (1:ℝ) - (1 - b) = b by ring] at f g
  rw [abs_sub_comm b a] at g
  have toE (first second : PMF ℕ) (bound : chance first test - chance second test ≤ |a - b| / b) :
      (first.map test) true ≤ (second.map test) true + (p - q + (q - p)) / q := by
    have fin1 := PMF.apply_ne_top (first.map test) true
    have fin2 := PMF.apply_ne_top (second.map test) true
    have finG : (p - q + (q - p)) / q ≠ ⊤ := by
      apply ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.sub_ne_top finiteP, ENNReal.sub_ne_top finiteQ⟩)
      exact positiveQ.ne'
    rw [← ENNReal.toReal_le_toReal fin1 (ENNReal.add_ne_top.mpr ⟨fin2, finG⟩), ENNReal.toReal_add fin2 finG, gapReal]
    unfold chance at bound
    linarith
  exact ⟨toE P Q f, toE Q P g⟩

/-- Closeness on every test survives the same randomized continuation. -/
theorem kernel {Input Output : Type} (first second : PMF Input) (error : ENNReal)
    (near : Close first second error) (continuation : Input → PMF Output) :
    Close (first.bind continuation) (second.bind continuation) error := by
  classical
  have oneWay (P Q : PMF Input) (pq : ∀ test : Input → Bool, (P.map test) true ≤ (Q.map test) true + error)
      (test : Output → Bool) :
      ((P.bind continuation).map test) true ≤ ((Q.bind continuation).map test) true + error := by
    let f : Input → ENNReal := fun a => ((continuation a).map test) true
    have f1 : ∀ a, f a ≤ 1 := fun a => PMF.coe_le_one _ _
    let excess : Input → Bool := fun a => decide (Q a < P a)
    have total (R : PMF Input) : ((R.bind continuation).map test) true = ∑' a, R a * f a := by
      rw [PMF.map_bind, PMF.bind_apply]
    have mass (R : PMF Input) : (R.map excess) true = ∑' a, if Q a < P a then R a else 0 := by
      rw [PMF.map_apply]
      apply tsum_congr
      intro a
      by_cases h : Q a < P a <;> simp [excess, h, eq_comm]
    have pointwise : ∀ a, P a * f a ≤ Q a * f a + (if Q a < P a then P a - Q a else 0) := by
      intro a
      by_cases h : Q a < P a
      · simp only [h, ↓reduceIte]
        calc P a * f a = (Q a + (P a - Q a)) * f a := by rw [add_tsub_cancel_of_le h.le]
          _ = Q a * f a + (P a - Q a) * f a := add_mul _ _ _
          _ ≤ Q a * f a + (P a - Q a) * 1 := add_le_add le_rfl (mul_le_mul_right (f1 a) _)
          _ = Q a * f a + (P a - Q a) := by rw [mul_one]
      · simp only [h, ↓reduceIte, add_zero]
        exact mul_le_mul_left (not_lt.mp h) _
    have split : (∑' a, if Q a < P a then P a else 0) =
        (∑' a, if Q a < P a then Q a else 0) + ∑' a, if Q a < P a then P a - Q a else 0 := by
      rw [← ENNReal.tsum_add]
      apply tsum_congr
      intro a
      by_cases h : Q a < P a
      · simp only [h, ↓reduceIte]; exact (add_tsub_cancel_of_le h.le).symm
      · simp only [h, ↓reduceIte, add_zero]
    have excessBound : (∑' a, if Q a < P a then P a - Q a else 0) ≤ error := by
      have pa := pq excess
      rw [mass P, mass Q, split] at pa
      have finite : (∑' a, if Q a < P a then Q a else 0) ≠ ⊤ := by
        apply ne_top_of_le_ne_top (PMF.tsum_coe_ne_top Q)
        apply ENNReal.tsum_le_tsum
        intro a; split_ifs <;> simp
      exact (ENNReal.add_le_add_iff_left finite).mp pa
    rw [total P, total Q]
    calc ∑' a, P a * f a ≤ ∑' a, (Q a * f a + (if Q a < P a then P a - Q a else 0)) :=
          ENNReal.tsum_le_tsum pointwise
      _ = ∑' a, Q a * f a + ∑' a, (if Q a < P a then P a - Q a else 0) := ENNReal.tsum_add
      _ ≤ ∑' a, Q a * f a + error := add_le_add le_rfl excessBound
  intro test
  exact ⟨oneWay first second (fun t => (near t).1) test, oneWay second first (fun t => (near t).2) test⟩

end TrialLaws

/-! The number of failures together with the first passing value: a finite prefix of actual
trials followed by an independent copy of a stationary joint law gives exactly that law. -/
namespace FirstSuccessCount
open ProbabilityTools
variable {Entropy Result : Type} [Fintype Entropy] [Nonempty Entropy] [DecidableEq Entropy]

/-- One more failure before the ones counted by the law. -/
def later (law : PMF (ℕ × Result)) : PMF (ℕ × Result) := law.map fun x => (x.1 + 1, x.2)

/-- The failures and the first passing value of a finite trial list; after a list with no pass,
the continuation supplies the remaining failures and the value. -/
def finish (accepted : Finset Entropy) (make : Entropy → Result) (continuation : PMF (ℕ × Result)) :
    List Entropy → PMF (ℕ × Result)
  | [] => continuation
  | e :: rest => if e ∈ accepted then PMF.pure (0, make e) else later (finish accepted make continuation rest)

def completed (count : Nat) (accepted : Finset Entropy) (make : Entropy → Result)
    (continuation : PMF (ℕ × Result)) : PMF (ℕ × Result) :=
  (RandomTrialLists.law (Entropy := Entropy) count).bind (finish accepted make continuation)

/-- A stationary joint law stays exact after every finite prefix, not just in a limit. -/
theorem completion (count : Nat) (accepted : Finset Entropy) (make : Entropy → Result)
    (law : PMF (ℕ × Result))
    (stationary : (PMF.uniformOfFintype Entropy).bind
      (fun e => if e ∈ accepted then PMF.pure (0, make e) else later law) = law) :
    completed count accepted make law = law := by
  induction count with
  | zero =>
    simp only [completed, RandomTrialLists.law, PMF.bind_map, Function.comp_def, List.ofFn_zero, finish,
      PMF.bind_const]
  | succ count ih =>
    rw [completed, FirstSuccess.front_law]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, finish]
    have reduced (e : Entropy) :
        ((RandomTrialLists.law (Entropy := Entropy) count).bind
          (fun rest => if e ∈ accepted then PMF.pure (0, make e) else later (finish accepted make law rest))) =
            if e ∈ accepted then PMF.pure (0, make e) else later law := by
      split_ifs
      · exact PMF.bind_const _ _
      · unfold later
        rw [← PMF.map_bind]
        exact congrArg (fun distribution : PMF (ℕ × Result) => distribution.map fun x => (x.1 + 1, x.2)) ih
    simp_rw [reduced]
    exact stationary

end FirstSuccessCount

/-! The joint law of the number of failures and the selected value of the sequential loop on a
fixed table: geometric with the pass rate of the table, and independent of the value. -/
namespace WalletCount
open WalletGeneration WalletFinite TranscriptErasure WalletCompletion StatisticalClose ProbabilityTools
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Nonempty Entropy] [Fintype Seed] [Fintype Tail] [Nonempty Seed] [Nonempty Tail]

local notation "WalletTables" => WalletCompletion.Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

/-- The probability that one uniform trial passes on this table. -/
def rate (table : WalletTables) (q : Passphrase) (target : Check) : ENNReal :=
  ((passing table q target).card : ENNReal) / (Fintype.card Entropy : ENNReal)

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [Nonempty Entropy] [Fintype Seed]
  [Fintype Tail] [Nonempty Seed] [Nonempty Tail] in
theorem rate_le_one (table : WalletTables) (q : Passphrase) (target : Check) : rate table q target ≤ 1 := by
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  exact_mod_cast Finset.card_le_univ _

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [Nonempty Entropy] [Fintype Seed]
  [Fintype Tail] [Nonempty Seed] [Nonempty Tail] in
theorem rate_pos (table : WalletTables) (q : Passphrase) (target : Check)
    (nonempty : (passing table q target).Nonempty) : 0 < rate table q target := by
  apply ENNReal.div_pos_iff.mpr
  exact ⟨by exact_mod_cast nonempty.card_pos.ne', ENNReal.natCast_ne_top _⟩

/-- The number of failures and the selected value. If no value passes, the loop does not stop; an
arbitrary fallback is defined there, as for the selected value alone. -/
def real (table : WalletTables) (q : Passphrase) (target : Check) : PMF (ℕ × Selected Entropy Seed Tail) :=
  if nonempty : (passing table q target).Nonempty then
    independentPair (TrialLaws.failures (rate table q target) (rate_pos table q target nonempty)
      (rate_le_one table q target)) (WalletCompletion.real table q target)
  else (WalletCompletion.real table q target).map fun chosen => (0, chosen)

omit [DecidableEq Passphrase] [DecidableEq Seed] [Fintype Seed] [Fintype Tail] [Nonempty Seed]
  [Nonempty Tail] in
/-- The probability that one uniform trial fails. -/
theorem complement_mass (table : WalletTables) (q : Passphrase) (target : Check) :
    ((Finset.univ.filter fun e => e ∉ passing table q target).card : ENNReal) *
      (Fintype.card Entropy : ENNReal)⁻¹ = 1 - rate table q target := by
  have cardE : (Fintype.card Entropy : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have finE : (Fintype.card Entropy : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have count : (Finset.univ.filter fun e => e ∉ passing table q target).card =
      Fintype.card Entropy - (passing table q target).card := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ]
    congr 1
    congr 1
    ext e
    simp
  rw [count, ENNReal.natCast_sub, ENNReal.sub_mul (fun _ _ => ENNReal.inv_ne_top.mpr cardE),
    ENNReal.mul_inv_cancel cardE finE, rate, div_eq_mul_inv]

omit [DecidableEq Passphrase] [DecidableEq Seed] in
/-- One uniform trial first: a pass gives no failure and its value, a failure adds one. -/
theorem stationary (table : WalletTables) (q : Passphrase) (target : Check)
    (nonempty : (passing table q target).Nonempty) :
    (PMF.uniformOfFintype Entropy).bind (fun e => if e ∈ passing table q target then PMF.pure (0, make table q e)
      else FirstSuccessCount.later (real table q target)) = real table q target := by
  classical
  set p := rate table q target with hp
  have cardU : ((passing table q target).card : ENNReal) ≠ 0 := by exact_mod_cast nonempty.card_pos.ne'
  have cardE : (Fintype.card Entropy : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have finU : ((passing table q target).card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have finE : (Fintype.card Entropy : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have realEq : real table q target = independentPair (TrialLaws.failures p (rate_pos table q target nonempty)
      (rate_le_one table q target)) (WalletCompletion.real table q target) := by
    rw [real, dite_eq_left_of_eq_true (eq_true nonempty)]
  have completionEq : WalletCompletion.real table q target =
      (PMF.uniformOfFinset (passing table q target) nonempty).map (make table q) := by
    rw [WalletCompletion.real, dite_eq_left_of_eq_true (eq_true nonempty)]
  -- the mass of the selected value: the passing values that give it, over the size of the set
  have valueMass (chosen : Selected Entropy Seed Tail) : WalletCompletion.real table q target chosen =
      (((passing table q target).filter fun e => chosen = make table q e).card : ENNReal) * ((passing table q target).card : ENNReal)⁻¹ := by
    rw [completionEq, PMF.map_apply, tsum_fintype]
    have each (e : Entropy) : (if chosen = make table q e then PMF.uniformOfFinset (passing table q target) nonempty e else 0) =
        if e ∈ (passing table q target).filter (fun e => chosen = make table q e) then ((passing table q target).card : ENNReal)⁻¹ else 0 := by
      by_cases h : chosen = make table q e
      · by_cases m : e ∈ (passing table q target)
        · simp [h, m, PMF.uniformOfFinset_apply_of_mem nonempty m]
        · simp [h, m, PMF.uniformOfFinset_apply_of_notMem nonempty m]
      · simp [h]
    simp_rw [each]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have laterEq (n : ℕ) (chosen : Selected Entropy Seed Tail) :
      FirstSuccessCount.later (real table q target) (n, chosen) =
        if n = 0 then 0 else real table q target (n - 1, chosen) := by
    unfold FirstSuccessCount.later
    rw [PMF.map_apply]
    rcases n with _ | k
    · simp only [Prod.mk.injEq, ↓reduceIte]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      simp only [show ¬ (0 = x.1 + 1) from by omega, false_and, ↓reduceIte]
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [tsum_eq_single (k, chosen)]
      · simp only [↓reduceIte]
      · intro x different
        have : ¬ ((k + 1, chosen) = (x.1 + 1, x.2)) := by
          intro same
          apply different
          obtain ⟨a, b⟩ := x
          simp only [Prod.mk.injEq] at same ⊢
          exact ⟨by omega, same.2.symm⟩
        simp only [this, ↓reduceIte]
  have complement : ((Finset.univ.filter fun e => e ∉ (passing table q target)).card : ENNReal) *
      (Fintype.card Entropy : ENNReal)⁻¹ = 1 - p := complement_mass table q target
  ext ⟨n, chosen⟩
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  have pointwise (e : Entropy) :
      (if e ∈ passing table q target then PMF.pure (0, make table q e)
        else FirstSuccessCount.later (real table q target)) (n, chosen) =
      if e ∈ passing table q target then (PMF.pure (0, make table q e)) (n, chosen)
        else FirstSuccessCount.later (real table q target) (n, chosen) := by
    split_ifs <;> rfl
  rw [← Finset.mul_sum, Finset.sum_congr rfl (fun e _ => pointwise e)]
  rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, realEq,
    independentPair_apply, TrialLaws.failures_apply]
  rw [← realEq]
  rcases n with _ | k
  · -- no failure: exactly the passing values that give the selected value
    have none : FirstSuccessCount.later (real table q target) (0, chosen) = 0 := by
      rw [laterEq]; simp
    rw [none, mul_zero, add_zero]
    have passes : (∑ e ∈ Finset.univ.filter (fun e => e ∈ (passing table q target)), (PMF.pure (0, make table q e)) (0, chosen)) =
        (((passing table q target).filter fun e => chosen = make table q e).card : ENNReal) := by
      have filterU : Finset.univ.filter (fun e => e ∈ (passing table q target)) = (passing table q target) := by ext e; simp
      rw [filterU]
      simp only [PMF.pure_apply, Prod.mk.injEq, true_and]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [passes, valueMass, pow_zero, one_mul, hp, rate, div_eq_mul_inv]
    calc (Fintype.card Entropy : ENNReal)⁻¹ * (((passing table q target).filter fun e => chosen = make table q e).card : ENNReal)
        = ((passing table q target).card : ENNReal) * ((passing table q target).card : ENNReal)⁻¹ * ((Fintype.card Entropy : ENNReal)⁻¹ *
            (((passing table q target).filter fun e => chosen = make table q e).card : ENNReal)) := by
          rw [ENNReal.mul_inv_cancel cardU finU, one_mul]
      _ = _ := by ring
  · -- at least one failure: the remaining law after one failed trial
    have nopass : (∑ e ∈ Finset.univ.filter (fun e => e ∈ (passing table q target)), (PMF.pure (0, make table q e)) (k + 1, chosen)) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      simp [PMF.pure_apply]
    rw [nopass, zero_add, laterEq]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [realEq, independentPair_apply, TrialLaws.failures_apply]
    calc (Fintype.card Entropy : ENNReal)⁻¹ * (((Finset.univ.filter fun e => e ∉ (passing table q target)).card : ENNReal) *
          ((1 - p) ^ k * p * WalletCompletion.real table q target chosen))
        = (((Finset.univ.filter fun e => e ∉ (passing table q target)).card : ENNReal) * (Fintype.card Entropy : ENNReal)⁻¹) *
          ((1 - p) ^ k * p * WalletCompletion.real table q target chosen) := by ring
      _ = _ := by rw [complement, pow_succ]; ring

omit [DecidableEq Entropy] [Fintype Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [Nonempty Entropy]
  [Fintype Seed] [Fintype Tail] [Nonempty Seed] [Nonempty Tail] in
/-- A successful loop has read at least the two values of its passing trial. -/
theorem reads_on_success (table : WalletTables) (q : Passphrase) (target : Check) (trials : List Entropy)
    (chosen : Selected Entropy Seed Tail) (success : (execute table (loop q target trials)).1 = some chosen) :
    2 ≤ (execute table (loop q target trials)).2.length := by
  induction trials with
  | nil => cases success
  | cons e rest ih =>
    rw [execution_cons] at success ⊢
    dsimp only at success ⊢
    by_cases passes : (table (Point.t (table (Point.s e q)))).1 = target
    · simp only [passes, ↓reduceIte, List.length_cons, List.length_nil, le_refl]
    · simp only [passes, ↓reduceIte] at success ⊢
      simp only [List.length_append, List.length_cons, List.length_nil]
      have := ih success
      omega

omit [DecidableEq Passphrase] [DecidableEq Seed] [Nonempty Entropy] [Fintype Seed] [Fintype Tail]
  [Nonempty Seed] [Nonempty Tail] in
/-- The recursive count is exactly what the actual stopping loop does: it reads two values per trial,
so the failures are half its reads less the passing trial. -/
theorem finish_loop (table : WalletTables) (q : Passphrase) (target : Check)
    (continuation : PMF (ℕ × Selected Entropy Seed Tail)) (trials : List Entropy) :
    FirstSuccessCount.finish (passing table q target) (make table q) continuation trials =
      match execute table (loop q target trials) with
      | (none, reads) => continuation.map fun x => (x.1 + reads.length / 2, x.2)
      | (some chosen, reads) => PMF.pure (reads.length / 2 - 1, chosen) := by
  induction trials with
  | nil =>
    rw [FirstSuccessCount.finish]
    have run : execute table (loop q target ([] : List Entropy)) = (none, []) := rfl
    rw [run]
    simp only [List.length_nil, Nat.zero_div, Nat.add_zero]
    exact (PMF.map_id continuation).symm
  | cons e rest ih =>
    rw [FirstSuccessCount.finish, execution_cons]
    dsimp only
    have member : e ∈ passing table q target ↔ (table (Point.t (table (Point.s e q)))).1 = target := by
      simp only [passing, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases passes : (table (Point.t (table (Point.s e q)))).1 = target
    · simp only [member, passes, ↓reduceIte, List.length_cons, List.length_nil]
      rfl
    · simp only [member, passes, ↓reduceIte]
      rw [ih]
      unfold FirstSuccessCount.later
      have successReads := reads_on_success table q target rest
      revert successReads
      rcases execute table (loop q target rest) with ⟨_ | chosen, reads⟩
      · intro _
        rw [PMF.map_comp]
        congr 1
        funext x
        simp only [Function.comp_apply, List.length_append, List.length_cons, List.length_nil, Prod.mk.injEq,
          and_true]
        omega
      · intro successReads
        have two : 2 ≤ reads.length := successReads chosen rfl
        simp only [PMF.pure_map, List.length_append, List.length_cons, List.length_nil]
        congr 2
        omega

omit [DecidableEq Passphrase] [DecidableEq Seed] in
/-- A finite prefix of actual trials, then an independent copy of the joint law shifted by the
failures already made, has exactly the joint law. -/
theorem completed_loop (count : Nat) (table : WalletTables) (q : Passphrase) (target : Check)
    (nonempty : (passing table q target).Nonempty) :
    (RandomTrialLists.law (Entropy := Entropy) count).bind (fun trials =>
      match execute table (loop q target trials) with
      | (none, reads) => (real table q target).map fun x => (x.1 + reads.length / 2, x.2)
      | (some chosen, reads) => PMF.pure (reads.length / 2 - 1, chosen)) =
      real table q target := by
  have completed := FirstSuccessCount.completion count (passing table q target) (make table q)
    (real table q target) (stationary table q target nonempty)
  unfold FirstSuccessCount.completed at completed
  have same : FirstSuccessCount.finish (passing table q target) (make table q) (real table q target) =
      fun trials => match execute table (loop q target trials) with
        | (none, reads) => (real table q target).map fun x => (x.1 + reads.length / 2, x.2)
        | (some chosen, reads) => PMF.pure (reads.length / 2 - 1, chosen) := by
    funext trials
    exact finish_loop table q target (real table q target) trials
  rw [same] at completed
  exact completed

omit [DecidableEq Passphrase] [DecidableEq Seed] [Nonempty Entropy] [Fintype Seed] [Fintype Tail]
  [Nonempty Seed] [Nonempty Tail] in
/-- A trial list fails as a whole when its first value fails and the rest fails. -/
theorem none_cons (table : WalletTables) (q : Passphrase) (target : Check) (e : Entropy)
    (rest : List Entropy) :
    (execute table (loop q target (e :: rest))).1.isNone =
      if e ∈ passing table q target then false else (execute table (loop q target rest)).1.isNone := by
  rw [execution_cons]
  dsimp only
  by_cases passes : (table (Point.t (table (Point.s e q)))).1 = target
  · have member : e ∈ passing table q target := by
      simp only [passing, Finset.mem_filter, Finset.mem_univ, true_and, passes]
    simp only [passes, member, ↓reduceIte, Option.isNone_some]
  · have member : e ∉ passing table q target := by
      simp only [passing, Finset.mem_filter, Finset.mem_univ, true_and, passes, not_false_eq_true]
    simp only [passes, member, ↓reduceIte]

omit [DecidableEq Passphrase] [DecidableEq Seed] [Fintype Seed] [Fintype Tail] [Nonempty Seed]
  [Nonempty Tail] in
/-- The probability that `count` uniform trials all fail is `(1 - p_U)^count`. -/
theorem survival (count : Nat) (table : WalletTables) (q : Passphrase) (target : Check) :
    ((RandomTrialLists.law (Entropy := Entropy) count).map
      (fun trials => (execute table (loop q target trials)).1.isNone)) true =
      (1 - rate table q target) ^ count := by
  induction count with
  | zero =>
    have run : (execute table (loop q target ([] : List Entropy))).1.isNone = true := rfl
    simp only [RandomTrialLists.law, PMF.map_comp, Function.comp_def, List.ofFn_zero, run, pow_zero]
    simp [PMF.map_apply]
  | succ count ih =>
    rw [FirstSuccess.front_law, PMF.map_bind, PMF.bind_apply, tsum_fintype]
    simp only [PMF.map_comp, Function.comp_def, none_cons, PMF.uniformOfFintype_apply]
    have each (e : Entropy) : ((RandomTrialLists.law (Entropy := Entropy) count).map (fun rest =>
        if e ∈ passing table q target then false else (execute table (loop q target rest)).1.isNone)) true =
        if e ∈ passing table q target then 0 else (1 - rate table q target) ^ count := by
      by_cases member : e ∈ passing table q target
      · simp only [member, ↓reduceIte]
        simp [PMF.map_apply]
      · simp only [member, ↓reduceIte]
        exact ih
    simp_rw [each]
    rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
      pow_succ, ← complement_mass table q target]
    ring

omit [DecidableEq Passphrase] [DecidableEq Seed] in
/-- The actual loop cut off after `count` trials, followed by any behaviour after the cut-off, has a
joint law within `(1 - p_U)^count` of `real` on every test. So `real` is the only joint law that
every cut-off approaches: it is the law of the loop that runs until a pass. -/
theorem capped_close (count : Nat) (table : WalletTables) (q : Passphrase) (target : Check)
    (nonempty : (passing table q target).Nonempty)
    (afterCut : List Entropy → PMF (ℕ × Selected Entropy Seed Tail)) :
    Close ((RandomTrialLists.law (Entropy := Entropy) count).bind (fun trials =>
        match execute table (loop q target trials) with
        | (none, _) => afterCut trials
        | (some chosen, reads) => PMF.pure (reads.length / 2 - 1, chosen)))
      (real table q target) ((1 - rate table q target) ^ count) := by
  rw [← survival count table q target]
  conv => arg 2; rw [← completed_loop count table q target nonempty]
  rw [MomentTools.probability]
  apply CloseComposition.bind
  intro trials
  rcases execute table (loop q target trials) with ⟨_ | chosen, reads⟩
  · exact CompletionCoupling.universal _ _
  · exact StatisticalClose.of_eq _ _ rfl

variable [Fintype Check] [Nonempty Check]

/-- The ideal pass rate: one check value out of all, `2^-16` for a 16-bit check. -/
def idealRate : ENNReal := (Fintype.card Check : ENNReal)⁻¹

omit [DecidableEq Check] [Nonempty Check] in
theorem idealRate_pos : 0 < idealRate (Check := Check) :=
  ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)

omit [DecidableEq Check] in
theorem idealRate_le_one : idealRate (Check := Check) ≤ 1 := by
  apply ENNReal.inv_le_one.mpr
  exact_mod_cast Fintype.card_pos

omit [DecidableEq Check] in
theorem idealRate_ne_top : idealRate (Check := Check) ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)

/-- The number of failures drawn with the ideal pass rate, independent of the selected value. -/
def ideal (table : WalletTables) (q : Passphrase) (target : Check) : PMF (ℕ × Selected Entropy Seed Tail) :=
  independentPair (TrialLaws.failures (idealRate (Check := Check)) idealRate_pos idealRate_le_one)
    (WalletCompletion.real table q target)

/-- The distance of the pass rate of the table from the ideal one, relative to the ideal one. -/
def gap (table : WalletTables) (q : Passphrase) (target : Check) : ENNReal :=
  (rate table q target - idealRate (Check := Check) + (idealRate (Check := Check) - rate table q target)) /
    idealRate (Check := Check)

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] in
/-- On each table the joint law is within the gap of the ideal one, on every test. An empty passing
set has gap one, which every two laws satisfy. -/
theorem close (table : WalletTables) (q : Passphrase) (target : Check) :
    Close (real table q target) (ideal table q target) (gap table q target) := by
  by_cases nonempty : (passing table q target).Nonempty
  · rw [real, dite_eq_left_of_eq_true (eq_true nonempty)]
    unfold ideal independentPair
    exact TrialLaws.kernel _ _ _ (TrialLaws.close _ _ _ _ _ _) _
  · have zero : rate table q target = 0 := by
      simp [rate, Finset.not_nonempty_iff_eq_empty.mp nonempty]
    have one : gap table q target = 1 := by
      rw [gap, zero, zero_tsub, zero_add, tsub_zero]
      exact ENNReal.div_self idealRate_pos.ne' idealRate_ne_top
    rw [one]
    exact CompletionCoupling.universal _ _

end WalletCount


/-! Uniform tables give a pass rate close to the ideal one: the number of passing values has mean
`|E|/|C|`, and two different values pass together with the product of the ideal probabilities plus
at most the probability that their seeds coincide. -/
namespace TrialDeviation
open WalletGeneration WalletFinite TranscriptErasure WalletCompletion GameExpectation MomentTools
  ProbabilityTools
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

local notation "WalletTables" => WalletCompletion.Tables (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail)

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- The expectation of the indicator of one value is the mass of that value. -/
theorem point_moment {Value : Type} [DecidableEq Value] (law : PMF Value) (value : Value) :
    moment law (fun x => if x = value then 1 else 0) = law value := by
  rw [moment, tsum_eq_single value]
  · simp
  · intro x different
    simp [different]

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- Two different values of a uniform function are independent and uniform. -/
theorem uniform_two {Domain Answer : Type} [DecidableEq Domain] [Fintype Domain] [Fintype Answer]
    [Nonempty Answer] (a b : Domain) (distinct : a ≠ b) :
    (PMF.uniformOfFintype (Domain → Answer)).map (fun f => (f a, f b)) =
      PMF.uniformOfFintype (Answer × Answer) := by
  let split := Equiv.funSplitAt a Answer
  have moved := PMF.uniformOfFintype_map_of_bijective split split.bijective
  have : Nonempty {x // x ≠ a} := ⟨⟨b, distinct.symm⟩⟩
  calc (PMF.uniformOfFintype (Domain → Answer)).map (fun f => (f a, f b))
      = ((PMF.uniformOfFintype (Domain → Answer)).map split).map
          (fun g => (g.1, g.2 ⟨b, distinct.symm⟩)) := by
        rw [PMF.map_comp]
        rfl
    _ = (PMF.uniformOfFintype (Answer × ({x // x ≠ a} → Answer))).map
          (fun g => (g.1, g.2 ⟨b, distinct.symm⟩)) := by rw [moved]
    _ = independentPair (PMF.uniformOfFintype Answer)
          ((PMF.uniformOfFintype ({x // x ≠ a} → Answer)).map (fun rest => rest ⟨b, distinct.symm⟩)) := by
        rw [uniform_product]
        simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
    _ = independentPair (PMF.uniformOfFintype Answer) (PMF.uniformOfFintype Answer) := by
        rw [uniform_eval]
    _ = _ := uniform_product.symm

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- Independent laws average a product as the product of the averages. -/
theorem product_moment {First Second : Type} (first : PMF First) (second : PMF Second)
    (f : First → ENNReal) (g : Second → ENNReal) :
    moment (independentPair first second) (fun z => f z.1 * g z.2) = moment first f * moment second g := by
  rw [independentPair, MomentTools.bind]
  simp only [moment_map, Function.comp_def]
  have inner (a : First) : moment second (fun b => f a * g b) = f a * moment second g := by
    rw [mul_comm (f a), ← MomentTools.mul_const]
    congr 1
    funext b
    ring
  simp_rw [inner]
  rw [MomentTools.mul_const]

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed]
  [Nonempty Entropy] [Nonempty Seed] in
/-- The mass of one check value under a uniform check and tail. -/
theorem check_mass (target : Check) :
    moment (PMF.uniformOfFintype (Check × Tail)) (fun z => if z.1 = target then 1 else 0) =
      (Fintype.card Check : ENNReal)⁻¹ := by
  rw [uniform_product, independentPair, MomentTools.bind]
  simp only [moment_map, Function.comp_def]
  have inner (a : Check) : moment (PMF.uniformOfFintype Tail) (fun _ => if a = target then (1 : ENNReal) else 0) =
      if a = target then 1 else 0 := MomentTools.constant _ _
  simp_rw [inner]
  rw [point_moment, PMF.uniformOfFintype_apply]

/-- One value passes when the check stored for its seed is the target. -/
def hit (table : WalletTables) (q : Passphrase) (target : Check) (e : Entropy) : ENNReal :=
  if (table (Point.t (table (Point.s e q)))).1 = target then 1 else 0

omit [DecidableEq Check] [Nonempty Entropy] in
/-- The table prior is a pair of independent uniform `S` and `T` functions. -/
theorem factored (f : WalletTables → ENNReal) :
    moment (PMF.uniformOfFintype WalletTables) f =
      moment (PMF.uniformOfFintype (Entropy × Passphrase → Seed)) (fun S =>
        moment (PMF.uniformOfFintype (Seed → Check × Tail))
          (fun T => f (WalletTableFactors.split.symm (S, T)))) := by
  rw [WalletTableFactors.sampling, moment_map, uniform_product, independentPair, MomentTools.bind]
  congr 1
  funext S
  rw [moment_map]
  rfl

omit [Nonempty Entropy] in
/-- One value passes with the ideal probability. -/
theorem single (q : Passphrase) (target : Check) (e : Entropy) :
    moment (PMF.uniformOfFintype WalletTables) (fun table => hit table q target e) =
      (Fintype.card Check : ENNReal)⁻¹ := by
  rw [factored]
  have inner (S : Entropy × Passphrase → Seed) :
      moment (PMF.uniformOfFintype (Seed → Check × Tail))
        (fun T => hit (WalletTableFactors.split.symm (S, T)) q target e) = (Fintype.card Check : ENNReal)⁻¹ := by
    calc _ = moment ((PMF.uniformOfFintype (Seed → Check × Tail)).map (fun T => T (S (e, q))))
          (fun z => if z.1 = target then 1 else 0) := by rw [moment_map]; rfl
      _ = _ := by rw [uniform_eval, check_mass]
  simp_rw [inner]
  exact MomentTools.constant _ _

omit [Nonempty Entropy] in
/-- Two different values pass together with the product of the ideal probabilities, plus at most
the ideal probability times that of a common seed. -/
theorem pair (q : Passphrase) (target : Check) (e e' : Entropy) (distinct : e ≠ e') :
    moment (PMF.uniformOfFintype WalletTables) (fun table => hit table q target e * hit table q target e') ≤
      (Fintype.card Check : ENNReal)⁻¹ * (Fintype.card Check : ENNReal)⁻¹ +
        (Fintype.card Check : ENNReal)⁻¹ * (Fintype.card Seed : ENNReal)⁻¹ := by
  rw [factored]
  have inner (S : Entropy × Passphrase → Seed) :
      moment (PMF.uniformOfFintype (Seed → Check × Tail))
        (fun T => hit (WalletTableFactors.split.symm (S, T)) q target e *
          hit (WalletTableFactors.split.symm (S, T)) q target e') ≤
        (Fintype.card Check : ENNReal)⁻¹ * (Fintype.card Check : ENNReal)⁻¹ +
          (if S (e, q) = S (e', q) then 1 else 0) * (Fintype.card Check : ENNReal)⁻¹ := by
    by_cases same : S (e, q) = S (e', q)
    · have square : (fun T : Seed → Check × Tail => hit (WalletTableFactors.split.symm (S, T)) q target e *
            hit (WalletTableFactors.split.symm (S, T)) q target e') =
          (fun z : Check × Tail => if z.1 = target then (1 : ENNReal) else 0) ∘ (fun T => T (S (e, q))) := by
        funext T
        change (if (T (S (e, q))).1 = target then (1 : ENNReal) else 0) *
          (if (T (S (e', q))).1 = target then 1 else 0) = if (T (S (e, q))).1 = target then 1 else 0
        rw [← same]
        split_ifs <;> simp
      rw [square, ← moment_map, uniform_eval, check_mass]
      simp only [same, ↓reduceIte, one_mul]
      exact le_add_self
    · have law := uniform_two (Answer := Check × Tail) (S (e, q)) (S (e', q)) same
      have shape : (fun T : Seed → Check × Tail => hit (WalletTableFactors.split.symm (S, T)) q target e *
            hit (WalletTableFactors.split.symm (S, T)) q target e') =
          (fun z : (Check × Tail) × (Check × Tail) => (if z.1.1 = target then (1 : ENNReal) else 0) *
            (if z.2.1 = target then 1 else 0)) ∘ (fun T => (T (S (e, q)), T (S (e', q)))) := rfl
      rw [shape, ← moment_map, law, uniform_product,
        product_moment _ _ (fun z : Check × Tail => if z.1 = target then (1 : ENNReal) else 0)
          (fun z : Check × Tail => if z.1 = target then (1 : ENNReal) else 0), check_mass]
      simp only [same, ↓reduceIte, zero_mul, add_zero, le_refl]
  have coincide : moment (PMF.uniformOfFintype (Entropy × Passphrase → Seed))
      (fun S => if S (e, q) = S (e', q) then (1 : ENNReal) else 0) = (Fintype.card Seed : ENNReal)⁻¹ := by
    have law := uniform_two (Answer := Seed) (e, q) (e', q) (fun same => distinct (Prod.ext_iff.mp same).1)
    calc _ = moment ((PMF.uniformOfFintype (Entropy × Passphrase → Seed)).map (fun S => (S (e, q), S (e', q))))
          (fun z => if z.1 = z.2 then 1 else 0) := by rw [moment_map]; rfl
      _ = moment (PMF.uniformOfFintype Seed) (fun d =>
            moment (PMF.uniformOfFintype Seed) (fun d' => if d = d' then 1 else 0)) := by
          rw [law, uniform_product, independentPair, MomentTools.bind]
          simp only [moment_map, Function.comp_def]
      _ = moment (PMF.uniformOfFintype Seed) (fun _ => (Fintype.card Seed : ENNReal)⁻¹) := by
          congr 1
          funext d
          have flip : (fun d' : Seed => if d = d' then (1 : ENNReal) else 0) = fun d' => if d' = d then 1 else 0 := by
            funext d'
            by_cases h : d' = d
            · simp [h]
            · simp [h, Ne.symm h]
          rw [flip, point_moment, PMF.uniformOfFintype_apply]
      _ = _ := MomentTools.constant _ _
  calc _ ≤ moment (PMF.uniformOfFintype (Entropy × Passphrase → Seed))
        (fun S => (Fintype.card Check : ENNReal)⁻¹ * (Fintype.card Check : ENNReal)⁻¹ +
          (if S (e, q) = S (e', q) then 1 else 0) * (Fintype.card Check : ENNReal)⁻¹) :=
        MomentTools.mono _ _ _ inner
    _ = _ := by
      rw [MomentTools.add, MomentTools.constant, MomentTools.mul_const, coincide, mul_comm (Fintype.card Seed : ENNReal)⁻¹]

/-- The number of passing values. -/
def count (table : WalletTables) (q : Passphrase) (target : Check) : ENNReal := ∑ e, hit table q target e

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [Fintype Passphrase] [Fintype Seed]
  [Fintype Check] [Fintype Tail] [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
theorem count_eq (table : WalletTables) (q : Passphrase) (target : Check) :
    count table q target = ((passing table q target).card : ENNReal) := by
  rw [count, passing, Finset.card_filter]
  push_cast
  rfl

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [Fintype Passphrase] [Fintype Seed]
  [Fintype Check] [Fintype Tail] [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
theorem count_le (table : WalletTables) (q : Passphrase) (target : Check) :
    count table q target ≤ Fintype.card Entropy := by
  rw [count_eq]
  exact_mod_cast Finset.card_le_univ _

omit [Nonempty Entropy] in
/-- The mean number of passing values. -/
theorem mean (q : Passphrase) (target : Check) :
    moment (PMF.uniformOfFintype WalletTables) (fun table => count table q target) =
      (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ := by
  unfold count
  rw [MomentTools.finite_sum _ (fun e table => hit table q target e)]
  simp only [single, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Nonempty Entropy] in
/-- The second moment: the diagonal gives the mean, every ordered pair of different values at most
the pair bound. -/
theorem second (q : Passphrase) (target : Check) :
    moment (PMF.uniformOfFintype WalletTables) (fun table => count table q target * count table q target) ≤
      (Fintype.card Entropy : ENNReal) * ((Fintype.card Check : ENNReal)⁻¹ +
        ((Fintype.card Entropy : ENNReal) - 1) * ((Fintype.card Check : ENNReal)⁻¹ * (Fintype.card Check : ENNReal)⁻¹ +
          (Fintype.card Check : ENNReal)⁻¹ * (Fintype.card Seed : ENNReal)⁻¹)) := by
  have expand : (fun table : WalletTables => count table q target * count table q target) =
      fun table : WalletTables => ∑ e, ∑ e', hit table q target e * hit table q target e' := by
    funext table
    rw [count, Finset.sum_mul_sum]
  rw [expand, MomentTools.finite_sum _ (fun e (table : WalletTables) => ∑ e', hit table q target e * hit table q target e')]
  simp only [MomentTools.finite_sum]
  rw [← nsmul_eq_mul, ← Finset.card_univ (α := Entropy)]
  apply Finset.sum_le_card_nsmul
  intro e _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
  apply add_le_add
  · have diagonal : (fun table : WalletTables => hit table q target e * hit table q target e) =
        fun table : WalletTables => hit table q target e := by
      funext table
      unfold hit
      split_ifs <;> simp
    rw [diagonal, single]
  · calc _ ≤ ∑ e' ∈ Finset.univ.erase e, ((Fintype.card Check : ENNReal)⁻¹ * (Fintype.card Check : ENNReal)⁻¹ +
          (Fintype.card Check : ENNReal)⁻¹ * (Fintype.card Seed : ENNReal)⁻¹) :=
          Finset.sum_le_sum fun e' member => pair q target e e' (Finset.ne_of_mem_erase member).symm
      _ = _ := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ, nsmul_eq_mul,
          ENNReal.natCast_sub, Nat.cast_one]

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- The distance of two finite values, read as a real number. -/
theorem distance_toReal (a b : ENNReal) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a - b + (b - a)).toReal = |a.toReal - b.toReal| := by
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, zero_add, ENNReal.toReal_sub_of_le h hb, abs_sub_comm, abs_of_nonneg]
    exact sub_nonneg.mpr ((ENNReal.toReal_le_toReal ha hb).mpr h)
  · rw [tsub_eq_zero_of_le h, add_zero, ENNReal.toReal_sub_of_le h ha, abs_of_nonneg]
    exact sub_nonneg.mpr ((ENNReal.toReal_le_toReal hb ha).mpr h)

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- Pointwise `2t|x - m| ≤ (x - m)^2 + t^2`, written without subtraction. -/
theorem spread (x m t : ENNReal) (hx : x ≠ ⊤) (hm : m ≠ ⊤) (ht : t ≠ ⊤) :
    (x - m + (m - x)) * (2 * t) + x * (2 * m) ≤ x * x + (m * m + t * t) := by
  have two : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  have dfin : x - m + (m - x) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.sub_ne_top hx, ENNReal.sub_ne_top hm⟩
  have lfin : (x - m + (m - x)) * (2 * t) + x * (2 * m) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top dfin (ENNReal.mul_ne_top two ht),
      ENNReal.mul_ne_top hx (ENNReal.mul_ne_top two hm)⟩
  have rfin : x * x + (m * m + t * t) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hx hx,
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hm hm, ENNReal.mul_ne_top ht ht⟩⟩
  have left : ((x - m + (m - x)) * (2 * t) + x * (2 * m)).toReal =
      |x.toReal - m.toReal| * (2 * t.toReal) + x.toReal * (2 * m.toReal) := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top dfin (ENNReal.mul_ne_top two ht))
      (ENNReal.mul_ne_top hx (ENNReal.mul_ne_top two hm))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, distance_toReal x m hx hm]
  have right : (x * x + (m * m + t * t)).toReal =
      x.toReal * x.toReal + (m.toReal * m.toReal + t.toReal * t.toReal) := by
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top hx hx)
        (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hm hm, ENNReal.mul_ne_top ht ht⟩),
      ENNReal.toReal_add (ENNReal.mul_ne_top hm hm) (ENNReal.mul_ne_top ht ht)]
    simp only [ENNReal.toReal_mul]
  rw [← ENNReal.toReal_le_toReal lfin rfin, left, right]
  nlinarith [sq_nonneg (|x.toReal - m.toReal| - t.toReal), sq_abs (x.toReal - m.toReal),
    ENNReal.toReal_nonneg (a := t)]

/-- The distance of the number of passing values from its mean `|E|/|C|`. -/
def deviation (table : WalletTables) (q : Passphrase) (target : Check) : ENNReal :=
  count table q target - (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ +
    ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ - count table q target)

omit [Nonempty Entropy] in
/-- The mean distance is at most `t` when the second moment exceeds the squared mean by at most
`t^2`: average `2t|x - m| ≤ (x - m)^2 + t^2`. -/
theorem deviation_bound (q : Passphrase) (target : Check) (t : ENNReal) (positive : 0 < t) (finite : t ≠ ⊤)
    (secondBound : moment (PMF.uniformOfFintype WalletTables)
      (fun table => count table q target * count table q target) ≤
      (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ *
        ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹) + t * t) :
    moment (PMF.uniformOfFintype WalletTables) (fun table => deviation table q target) ≤ t := by
  have mFinite : (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero))
  have pointwise (table : WalletTables) :
      deviation table q target * (2 * t) +
          count table q target * (2 * ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹)) ≤
        count table q target * count table q target +
          ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ *
            ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹) + t * t) :=
    spread _ _ _ (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (count_le table q target)) mFinite finite
  have averaged := MomentTools.mono (PMF.uniformOfFintype WalletTables) _ _ pointwise
  rw [MomentTools.add, MomentTools.mul_const, MomentTools.mul_const, mean, MomentTools.add,
    MomentTools.constant] at averaged
  have total := averaged.trans (add_le_add secondBound le_rfl)
  have rearranged : (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ *
        ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹) + t * t +
      ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ *
        ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹) + t * t) =
      t * (2 * t) + (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ *
        (2 * ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹)) := by ring
  rw [rearranged] at total
  have cancel := (ENNReal.add_le_add_iff_right
    (ENNReal.mul_ne_top mFinite (ENNReal.mul_ne_top ENNReal.ofNat_ne_top mFinite))).mp total
  exact (ENNReal.mul_le_mul_iff_left (mul_ne_zero two_ne_zero positive.ne')
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top finite)).mp cancel

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [Fintype Passphrase] [Fintype Seed]
  [Fintype Tail] [Nonempty Seed] [Nonempty Tail] in
/-- The gap of a table is its deviation relative to the mean `|E|/|C|`. -/
theorem gap_eq (table : WalletTables) (q : Passphrase) (target : Check) :
    WalletCount.gap table q target =
      deviation table q target / ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹) := by
  have cardE : (0 : ℝ) < Fintype.card Entropy := by exact_mod_cast Fintype.card_pos
  have cardC : (0 : ℝ) < Fintype.card Check := by exact_mod_cast Fintype.card_pos
  have countFinite : count table q target ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (count_le table q target)
  have mFinite : (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero))
  have mPos : (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
  have rateFinite : WalletCount.rate table q target ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (WalletCount.rate_le_one table q target)
  have idealFinite := WalletCount.idealRate_ne_top (Check := Check)
  have gapFinite : WalletCount.gap table q target ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.sub_ne_top rateFinite, ENNReal.sub_ne_top idealFinite⟩)
      (WalletCount.idealRate_pos (Check := Check)).ne'
  have devFinite : deviation table q target /
      ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.sub_ne_top countFinite, ENNReal.sub_ne_top mFinite⟩) mPos
  apply (ENNReal.toReal_eq_toReal_iff' gapFinite devFinite).mp
  rw [WalletCount.gap, ENNReal.toReal_div, distance_toReal _ _ rateFinite idealFinite,
    deviation, ENNReal.toReal_div, distance_toReal _ _ countFinite mFinite]
  rw [WalletCount.rate, ← count_eq, WalletCount.idealRate]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have split : (count table q target).toReal / (Fintype.card Entropy : ℝ) - (Fintype.card Check : ℝ)⁻¹ =
      ((count table q target).toReal - (Fintype.card Entropy : ℝ) * (Fintype.card Check : ℝ)⁻¹) /
        (Fintype.card Entropy : ℝ) := by
    field_simp
  rw [split, abs_div, abs_of_pos cardE, div_div]

set_option exponentiation.threshold 1024 in
/-- The concrete widths: the bound of the second moment is below the squared mean plus `2^240`. -/
theorem second_numbers :
    (2 ^ 256 : ENNReal) * ((2 ^ 16 : ENNReal)⁻¹ + ((2 ^ 256 : ENNReal) - 1) *
      ((2 ^ 16 : ENNReal)⁻¹ * (2 ^ 16 : ENNReal)⁻¹ + (2 ^ 16 : ENNReal)⁻¹ * (2 ^ 512 : ENNReal)⁻¹)) ≤
    (2 ^ 256 : ENNReal) * (2 ^ 16 : ENNReal)⁻¹ * ((2 ^ 256 : ENNReal) * (2 ^ 16 : ENNReal)⁻¹) +
      (2 ^ 120 : ENNReal) * (2 ^ 120 : ENNReal) := by
  have one : (1 : ENNReal) ≤ 2 ^ 256 := one_le_pow₀ one_le_two
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_sub_of_le one (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

set_option exponentiation.threshold 1024 in
/-- The concrete widths: `2^120` relative to the mean `2^240` is `2^-120`. -/
theorem ratio_numbers :
    (2 ^ 120 : ENNReal) / ((2 ^ 256 : ENNReal) * (2 ^ 16 : ENNReal)⁻¹) = (2 ^ 120 : ENNReal)⁻¹ := by
  have denominator : (2 ^ 256 : ENNReal) * (2 ^ 16 : ENNReal)⁻¹ ≠ 0 :=
    mul_ne_zero (by positivity) (ENNReal.inv_ne_zero.mpr (by finiteness))
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.div_ne_top (by finiteness) denominator) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  norm_num

/-- With a 256-bit entropy, a 512-bit seed and a 16-bit check, the mean gap over uniform tables is at
most `2^-120`: the variance of the number of passing values is below its mean `2^240`. -/
theorem gap_bound (q : Passphrase) (target : Check) (entropyWidth : Fintype.card Entropy = 2 ^ 256)
    (seedWidth : Fintype.card Seed = 2 ^ 512) (checkWidth : Fintype.card Check = 2 ^ 16) :
    moment (PMF.uniformOfFintype WalletTables) (fun table => WalletCount.gap table q target) ≤
      (2 ^ 120 : ENNReal)⁻¹ := by
  have hE : (Fintype.card Entropy : ENNReal) = 2 ^ 256 := by rw [entropyWidth, Nat.cast_pow, Nat.cast_ofNat]
  have hD : (Fintype.card Seed : ENNReal) = 2 ^ 512 := by rw [seedWidth, Nat.cast_pow, Nat.cast_ofNat]
  have hC : (Fintype.card Check : ENNReal) = 2 ^ 16 := by rw [checkWidth, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [gap_eq]
  rw [MomentTools.div_const]
  have secondBound : moment (PMF.uniformOfFintype WalletTables)
      (fun table => count table q target * count table q target) ≤
      (Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹ *
        ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹) + 2 ^ 120 * 2 ^ 120 := by
    apply (second q target).trans
    rw [hE, hD, hC]
    exact second_numbers
  have bound := deviation_bound q target (2 ^ 120) (by positivity) (by finiteness) secondBound
  calc _ ≤ (2 ^ 120 : ENNReal) / ((Fintype.card Entropy : ENNReal) * (Fintype.card Check : ENNReal)⁻¹) :=
        ENNReal.div_le_div_right bound _
    _ = (2 ^ 120 : ENNReal)⁻¹ := by
      rw [hE, hC]
      exact ratio_numbers

end TrialDeviation


/-! The game with the number of trials: Theorem 5's environment together with the number of failures
of the same generation, which the success test and the response after a refusal may read. -/
namespace TrialEnvironment
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment GameExpectation MomentTools StatisticalClose
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- Theorem 5's context, drawn together with the number of failures of the same generation. -/
def contexts (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check) :
    PMF (Context N Entropy Passphrase Seed Check Tail Data × ℕ) :=
  passwords.bind fun password => phrases.bind fun phrase =>
    (PMF.uniformOfFintype (Other (N := N) (Entropy := Entropy))).bind fun other =>
      (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
        (PMF.uniformOfFintype (GenerationTable (Entropy := Entropy) (Passphrase := Passphrase)
          (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
          (WalletCount.real table phrase target).map fun pair =>
            (⟨password, phrase, other, omega, table, pair.2⟩, pair.1)

/-- The first creation attempt; `H` is drawn last, as in Theorem 5. -/
def initial (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check) :
    PMF ((Context N Entropy Passphrase Seed Check Tail Data × ℕ) × HTable) :=
  ExactRefusalLift.initial (contexts passwords phrases target) CryptoUniform.h

/-- The success test and the response after a refusal read the number of failures; whether the first
attempt is refused depends on that attempt only. -/
def game (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check)
    (success : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → Bool)
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool) : PMF Bool :=
  RefusalResponse.game (initial passwords phrases target)
    (fun sample => FullSourceRefusal.refused coordinates (sample.1.1, sample.2))
    (fun sample => success sample.1.2 (sample.1.1, sample.2))
    (fun sample => later sample.1.2 (sample.1.1, sample.2))

/-- Everything after the generation: draw `H`, then refuse or test success. -/
def respond (coordinates : Entropy ≃ State)
    (success : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → Bool)
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (password : Fin N) (phrase : Passphrase) (other : Other (N := N) (Entropy := Entropy)) (omega : Seed → Data)
    (table : GenerationTable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check)
      (Tail := Tail))
    (pair : ℕ × WalletGeneration.Selected Entropy Seed Tail) : PMF Bool :=
  CryptoUniform.h.bind fun h =>
    if FullSourceRefusal.refused coordinates (⟨password, phrase, other, omega, table, pair.2⟩, h) then
      later pair.1 (⟨password, phrase, other, omega, table, pair.2⟩, h)
    else PMF.pure (success pair.1 (⟨password, phrase, other, omega, table, pair.2⟩, h))

/-- The trials game samples the same prior as Theorem 5 and then the joint law of the generation. -/
theorem game_eq (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (target : Check) (success : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → Bool)
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool) :
    game coordinates passwords phrases target success later =
      passwords.bind fun password => phrases.bind fun phrase =>
        (PMF.uniformOfFintype (Other (N := N) (Entropy := Entropy))).bind fun other =>
          (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
            (PMF.uniformOfFintype (GenerationTable (Entropy := Entropy) (Passphrase := Passphrase)
              (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
              (WalletCount.real table phrase target).bind
                (respond coordinates success later password phrase other omega table) := by
  unfold game RefusalResponse.game initial ExactRefusalLift.initial contexts respond
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- With an independent number of failures of the ideal rate (`2^-16` for a 16-bit check), the game is
Theorem 5's game with that number as a private coin of the adversary. -/
theorem ideal_eq (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (target : Check) (success : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → Bool)
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool) :
    ((TrialLaws.failures (WalletCount.idealRate (Check := Check)) WalletCount.idealRate_pos
      WalletCount.idealRate_le_one).bind fun n =>
        FullSourceRefusal.game coordinates passwords phrases target (success n) (later n)) =
      passwords.bind fun password => phrases.bind fun phrase =>
        (PMF.uniformOfFintype (Other (N := N) (Entropy := Entropy))).bind fun other =>
          (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
            (PMF.uniformOfFintype (GenerationTable (Entropy := Entropy) (Passphrase := Passphrase)
              (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
              (WalletCount.ideal table phrase target).bind
                (respond coordinates success later password phrase other omega table) := by
  unfold FullSourceRefusal.game RefusalResponse.game FullSourceRefusal.initial ExactRefusalLift.initial
    FullSourceEnvironment.contexts WalletCount.ideal ProbabilityTools.independentPair respond
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext password
  rw [PMF.bind_comm]
  congr 1
  funext phrase
  rw [PMF.bind_comm]
  congr 1
  funext other
  rw [PMF.bind_comm]
  congr 1
  funext omega
  rw [PMF.bind_comm]

omit [Fintype Data] [Nonempty Data] in
/-- On the tables, the joint law of the generation is replaced by the ideal one; the cost is the mean
gap, at most `2^-120`. -/
theorem table_step (coordinates : Entropy ≃ State)
    (success : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → Bool)
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (password : Fin N) (phrase : Passphrase) (other : Other (N := N) (Entropy := Entropy)) (omega : Seed → Data)
    (target : Check) (entropyWidth : Fintype.card Entropy = 2 ^ 256) (seedWidth : Fintype.card Seed = 2 ^ 512)
    (checkWidth : Fintype.card Check = 2 ^ 16) :
    ((PMF.uniformOfFintype (GenerationTable (Entropy := Entropy) (Passphrase := Passphrase)
        (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
      (WalletCount.real table phrase target).bind
        (respond coordinates success later password phrase other omega table)) true ≤
    ((PMF.uniformOfFintype (GenerationTable (Entropy := Entropy) (Passphrase := Passphrase)
        (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
      (WalletCount.ideal table phrase target).bind
        (respond coordinates success later password phrase other omega table)) true + (2 ^ 120 : ENNReal)⁻¹ := by
  rw [PMF.bind_apply, PMF.bind_apply]
  change moment _ _ ≤ moment _ _ + _
  calc _ ≤ moment (PMF.uniformOfFintype (GenerationTable (Entropy := Entropy) (Passphrase := Passphrase)
          (Seed := Seed) (Check := Check) (Tail := Tail))) (fun table =>
          ((WalletCount.ideal table phrase target).bind
            (respond coordinates success later password phrase other omega table)) true +
          WalletCount.gap table phrase target) := by
        apply MomentTools.mono
        intro table
        have near := TrialLaws.kernel _ _ _ (WalletCount.close table phrase target)
          (respond coordinates success later password phrase other omega table)
        have first := (near id).1
        simpa only [PMF.map_id] using first
    _ = _ := MomentTools.add _ _ _
    _ ≤ _ := add_le_add le_rfl (TrialDeviation.gap_bound phrase target entropyWidth seedWidth checkWidth)

/-- Revealing the number of failures adds at most `2^-120` to every success probability of the game
with an independent number of failures. -/
theorem transfer (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (target : Check) (success : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → Bool)
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (entropyWidth : Fintype.card Entropy = 2 ^ 256) (seedWidth : Fintype.card Seed = 2 ^ 512)
    (checkWidth : Fintype.card Check = 2 ^ 16) :
    (game coordinates passwords phrases target success later) true ≤
      ((TrialLaws.failures (WalletCount.idealRate (Check := Check)) WalletCount.idealRate_pos
        WalletCount.idealRate_le_one).bind fun n =>
          FullSourceRefusal.game coordinates passwords phrases target (success n) (later n)) true +
        (2 ^ 120 : ENNReal)⁻¹ := by
  rw [game_eq, ideal_eq]
  apply FullSourceTransfer.bind_probability
  intro password
  apply FullSourceTransfer.bind_probability
  intro phrase
  apply FullSourceTransfer.bind_probability
  intro other
  apply FullSourceTransfer.bind_probability
  intro omega
  exact table_step coordinates success later password phrase other omega target entropyWidth seedWidth checkWidth

end TrialEnvironment

/-! Theorem 5 when a generation reveals the number of its trials (sequential rule): both bounds hold
with `2^-120` added, for an adversary and a refusal response that read that number. -/
namespace Theorem5Trials
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

/-- Theorem 5(a) with the number of trials revealed. -/
theorem seed_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Seed)
    (adversary : ℕ → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password, passwords password ≤ p1) (largestQ : ∀ phrase, phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy = 2 ^ 256)
    (seedWidth : Fintype.card Seed = 2 ^ 512) (checkWidth : Fintype.card Check = 2 ^ 16)
    (budget : ∀ n, Budgets (adversary n) kA kS qB qH qT qOmega) :
    (TrialEnvironment.game coordinates passwords phrases target
      (fun n => score coordinates (adversary n) (fun _ _ seed result => decide (output result = seed))) later) true ≤
      W1.top2 passwords phrases (kA/12) kS + Theorem5.error p1 s1 kA kS qB qH qT qOmega + (2 ^ 512 : ENNReal)⁻¹ +
        (2 ^ 120 : ENNReal)⁻¹ := by
  apply (TrialEnvironment.transfer coordinates passwords phrases target _ later entropyWidth seedWidth checkWidth).trans
  exact add_le_add (Theorem5Randomized.seed_bound _ coordinates passwords phrases sorted target output adversary
    later p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget) le_rfl

/-- Theorem 5(b) with the number of trials revealed. -/
theorem pair_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Fin N × Passphrase)
    (adversary : ℕ → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password, passwords password ≤ p1) (largestQ : ∀ phrase, phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy = 2 ^ 256)
    (seedWidth : Fintype.card Seed = 2 ^ 512) (checkWidth : Fintype.card Check = 2 ^ 16)
    (budget : ∀ n, Budgets (adversary n) kA kS qB qH qT qOmega) :
    (TrialEnvironment.game coordinates passwords phrases target
      (fun n => score coordinates (adversary n) (fun password phrase _ result => decide (output result = (password, phrase))))
      later) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS + p1*s1) + Theorem5.error p1 s1 kA kS qB qH qT qOmega +
        (2 ^ 120 : ENNReal)⁻¹ := by
  apply (TrialEnvironment.transfer coordinates passwords phrases target _ later entropyWidth seedWidth checkWidth).trans
  exact add_le_add (Theorem5Randomized.pair_bound _ coordinates passwords phrases sorted target output adversary
    later p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget) le_rfl

end Theorem5Trials

/-! Corollary W5 when a generation reveals the number of its trials (sequential rule). -/
namespace W5Trials
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

/-- Corollary W5 with the number of trials revealed. -/
theorem bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : ℕ → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password, passwords password ≤ p1) (largestQ : ∀ phrase, phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy = 2 ^ 256)
    (seedWidth : Fintype.card Seed = 2 ^ 512) (checkWidth : Fintype.card Check = 2 ^ 16)
    (budget : ∀ n, Budgets (adversary n) kA kS qB qH qT qOmega) :
    (TrialEnvironment.game coordinates passwords phrases target
      (fun n => W5Source.score coordinates output (adversary n)) later) true ≤
      W1.top2 passwords phrases (kA/12) (kS+1) + W5.error p1 s1 kA kS qB qH qT qOmega + (2 ^ 120 : ENNReal)⁻¹ := by
  apply (TrialEnvironment.transfer coordinates passwords phrases target _ later entropyWidth seedWidth checkWidth).trans
  exact add_le_add (W5Randomized.bound _ coordinates passwords phrases sorted target output adversary
    later p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget) le_rfl

end W5Trials


/-! Private coins of the adversary, which may also give a duration that depends only on the number of
trials and on these coins, keep the three bounds. -/
namespace Theorem5TrialsRandomized
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result Strategy : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

theorem seed_bound (coins : PMF Strategy) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (sorted : Antitone passwords) (target : Check) (output : Result → Seed)
    (adversary : Strategy → ℕ → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password, passwords password ≤ p1) (largestQ : ∀ phrase, phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy = 2 ^ 256)
    (seedWidth : Fintype.card Seed = 2 ^ 512) (checkWidth : Fintype.card Check = 2 ^ 16)
    (budget : ∀ strategy n, Budgets (adversary strategy n) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => TrialEnvironment.game coordinates passwords phrases target
      (fun n => score coordinates (adversary strategy n) (fun _ _ seed result => decide (output result = seed)))
      (later strategy)) true ≤
      W1.top2 passwords phrases (kA/12) kS + Theorem5.error p1 s1 kA kS qB qH qT qOmega + (2 ^ 512 : ENNReal)⁻¹ +
        (2 ^ 120 : ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact Theorem5Trials.seed_bound coordinates passwords phrases sorted target output (adversary strategy)
    (later strategy) p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth (budget strategy)

theorem pair_bound (coins : PMF Strategy) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (sorted : Antitone passwords) (target : Check) (output : Result → Fin N × Passphrase)
    (adversary : Strategy → ℕ → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password, passwords password ≤ p1) (largestQ : ∀ phrase, phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy = 2 ^ 256)
    (seedWidth : Fintype.card Seed = 2 ^ 512) (checkWidth : Fintype.card Check = 2 ^ 16)
    (budget : ∀ strategy n, Budgets (adversary strategy n) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => TrialEnvironment.game coordinates passwords phrases target
      (fun n => score coordinates (adversary strategy n)
        (fun password phrase _ result => decide (output result = (password, phrase)))) (later strategy)) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS + p1*s1) + Theorem5.error p1 s1 kA kS qB qH qT qOmega +
        (2 ^ 120 : ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact Theorem5Trials.pair_bound coordinates passwords phrases sorted target output (adversary strategy)
    (later strategy) p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth (budget strategy)

end Theorem5TrialsRandomized

namespace W5TrialsRandomized
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result Strategy : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

theorem bound (coins : PMF Strategy) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (sorted : Antitone passwords) (target : Check)
    (output : Result → Entropy × Passphrase)
    (adversary : Strategy → ℕ → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → ℕ → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password, passwords password ≤ p1) (largestQ : ∀ phrase, phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy = 2 ^ 256)
    (seedWidth : Fintype.card Seed = 2 ^ 512) (checkWidth : Fintype.card Check = 2 ^ 16)
    (budget : ∀ strategy n, Budgets (adversary strategy n) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => TrialEnvironment.game coordinates passwords phrases target
      (fun n => W5Source.score coordinates output (adversary strategy n)) (later strategy)) true ≤
      W1.top2 passwords phrases (kA/12) (kS+1) + W5.error p1 s1 kA kS qB qH qT qOmega + (2 ^ 120 : ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact W5Trials.bound coordinates passwords phrases sorted target output (adversary strategy) (later strategy)
    p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth (budget strategy)

end W5TrialsRandomized

end
end MhfeLean
