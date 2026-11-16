import Mathlib.Logic.Function.Basic
import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.OracleModel

namespace MhfeLean
noncomputable section

/-! # Probability, oracle projection and fresh sampling
-/

/-!
Transfer the password-count expectation to the Gamma2 game.
This supplies the p1*k_A term used in the full first-Early bound in ChainEarly.
-/

namespace GameExpectation

open Gamma2Model ProbabilityTools QueryCounts

/-- Nonnegative expectation for a discrete distribution. -/
def moment (distribution : PMF Domain) (value : Domain → ENNReal) : ENNReal :=
  ∑' item, distribution item * value item

/-- Deterministic postprocessing can be moved from the law into the observed value. -/
theorem moment_map (distribution : PMF Domain) (transform : Domain → Output)
    (value : Output → ENNReal) :
    moment (distribution.map transform) value = moment distribution (value ∘ transform) := by
  classical
  letI : DecidableEq Output := Classical.decEq Output
  simp only [moment, PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1
  funext item
  have distribute (output : Output) :
      (if output = transform item then distribution item else 0) * value output =
        if output = transform item then distribution item * value output else 0 := by
    by_cases equal : output = transform item
    · simp only [if_pos equal]
    · simp only [if_neg equal, zero_mul]
  simp_rw [distribute]
  rw [tsum_ite_eq]
  rfl

variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]

local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

/-- A derived marginal of the existing adversary view; it adds no new sampling rule. -/
def inputsLaw (adversary : State → OracleComp (spec Password Entropy) Result) :
    PMF (State × Tables Password Entropy) :=
  (adversaryView adversary).map fun view => (view.1, view.2.1)

/-- The existing game can be regrouped as independent password and public oracle inputs. -/
theorem game_as_input_map (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    game passwords adversary =
      (independentPair passwords (inputsLaw adversary)).map
        (fun selected => outcome selected.1 selected.2.1 selected.2.2 adversary) := by
  simp only [game, independentPair, inputsLaw, adversaryView,
    PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- G3's expectation bound now applies to the actual typed Gamma2 execution. -/
theorem gamma2_password_count (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) (p1 : ENNReal)
    (largest : ∀ password, passwords password ≤ p1) (kA : Nat)
    (budget : ∀ (container : State) (tables : Tables Password Entropy), (execute tables (adversary container)).2.countP isA ≤ kA) :
    moment (game passwords adversary)
      (fun result => (result.adversaryQueries.countP (aFor result.password) : ENNReal)) ≤
        p1 * (kA : ENNReal) := by
  rw [game_as_input_map, moment_map]
  change (∑' selected : Password × (State × Tables Password Entropy),
      independentPair passwords (inputsLaw adversary) selected *
        ((execute selected.2.2 (adversary selected.2.1)).2.countP (aFor selected.1) : ENNReal)) ≤ _
  exact independent_expected_count passwords (inputsLaw adversary)
    (fun inputs => (execute inputs.2 (adversary inputs.1)).2)
    p1 largest kA (fun inputs => budget inputs.1 inputs.2)

end GameExpectation

/-! Discrete nonnegative expectations used to average the stopped-program bounds. -/
namespace MomentTools
open GameExpectation
variable {α β : Type}

theorem bind (p : PMF α) (q : α → PMF β) (f : β → ENNReal) :
    moment (p.bind q) f = moment p (fun a => moment (q a) f) := by
  simp only [moment, PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  simp only [mul_assoc, ENNReal.tsum_mul_left]

theorem mono (p : PMF α) (f g : α → ENNReal) (bounded : ∀ x, f x ≤ g x) : moment p f ≤ moment p g := by
  apply ENNReal.tsum_le_tsum
  intro x
  exact mul_le_mul_right (bounded x) _

theorem constant (p : PMF α) (c : ENNReal) : moment p (fun _ => c) = c := by
  rw [moment, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

theorem add (p : PMF α) (f g : α → ENNReal) :
    moment p (fun x => f x + g x) = moment p f + moment p g := by
  simp only [moment, mul_add, ENNReal.tsum_add]

theorem mul_const (p : PMF α) (f : α → ENNReal) (c : ENNReal) :
    moment p (fun x => f x * c) = moment p f * c := by
  simp only [moment, ← mul_assoc, ENNReal.tsum_mul_right]

theorem div_const (p : PMF α) (f : α → ENNReal) (c : ENNReal) :
    moment p (fun x => f x / c) = moment p f / c := by
  simp only [div_eq_mul_inv, mul_const]

theorem finite_sum {ι : Type} [Fintype ι] (p : PMF α) (f : ι → α → ENNReal) :
    moment p (fun x => ∑ i, f i x) = ∑ i, moment p (f i) := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  have auxiliary (indices : Finset ι) :
      moment p (fun x => ∑ i ∈ indices, f i x) = ∑ i ∈ indices, moment p (f i) := by
    induction indices using Finset.induction_on with
    | empty => simp [moment]
    | @insert i indices absent ih =>
      simp only [Finset.sum_insert absent]
      rw [add, ih]
  exact auxiliary Finset.univ

theorem bool (p : PMF Bool) : moment p (fun b => if b then 1 else 0) = p true := by
  rw [moment, tsum_fintype]
  simp

theorem probability (p : PMF α) (test : α → Bool) :
    (p.map test) true = moment p (fun x => if test x then 1 else 0) := by
  rw [← bool (p.map test), moment_map]
  rfl

theorem bounded (p : PMF α) (f : α → ENNReal) (c : ENNReal) (bound : ∀ x, f x ≤ c) : moment p f ≤ c := by
  calc
    _ ≤ moment p (fun _ => c) := mono p _ _ bound
    _ = c := constant p c

end MomentTools

section

/-!
Transcript erasure for consistent dependent random-function tables. Exchanging
unread values between two complete independent uniform tables is an involution:
the adaptive generation transcript is unchanged. Consequently, resampling all
read points leaves an independent fresh table. Selected points can subsequently
be restored by any postprocessing function of the retained transcript.
-/
namespace TranscriptErasure
open OracleComp
variable {Point Result Output : Type} [DecidableEq Point] {spec : OracleSpec Point}
abbrev Table (spec : OracleSpec Point) := (point : Point) → spec point

def implementation (table : Table spec) : QueryImpl spec (Writer (List Point)) :=
  fun point => WriterT.mk (table point, [point])

def execute (table : Table spec) (program : OracleComp spec Result) : Result × List Point :=
  (simulateQ (implementation table) program).run

def ask (point : Point) : OracleComp spec (spec point) :=
  OracleComp.lift (OracleSpec.query (spec := spec) point)

omit [DecidableEq Point] in
@[simp] theorem execute_pure (table : Table spec) (result : Result) :
    execute table (pure result) = (result, []) := rfl

omit [DecidableEq Point] in
@[simp] theorem execute_bind (table : Table spec) (program : OracleComp spec Result)
    (next : Result → OracleComp spec Output) :
    execute table (program >>= next) =
      let first := execute table program
      let second := execute table (next first.1)
      (second.1, first.2 ++ second.2) := by
  simp only [execute, simulateQ_bind]
  rfl

omit [DecidableEq Point] in
@[simp] theorem execute_ask (table : Table spec) (point : Point) :
    execute table (ask point) = (table point, [point]) := by
  simp [execute, ask, OracleComp.lift, simulateQ_query, implementation]

omit [DecidableEq Point] in
/-- An adaptive computation is unchanged when all values it actually read agree. -/
theorem execute_agree (program : OracleComp spec Result) (first second : Table spec)
    (agree : ∀ point ∈ (execute first program).2, second point = first point) :
    execute second program = execute first program := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih =>
    change (∀ q ∈ (execute first (ask point >>= next)).2, second q = first q) at agree
    change execute second (ask point >>= next) = execute first (ask point >>= next)
    simp only [execute_bind, execute_ask, List.singleton_append] at agree
    have head : second point = first point := agree point (by simp only [List.mem_cons, true_or])
    have rest : ∀ q ∈ (execute first (next (first point))).2, second q = first q := by
      intro q member
      exact agree q (List.mem_cons_of_mem point member)
    simp only [execute_bind, execute_ask, head, List.singleton_append]
    rw [ih (first point) rest]

def exchanged (program : OracleComp spec Result) (seed : Table spec × Table spec) :
    Table spec × Table spec :=
  (fun point => if point ∈ (execute seed.1 program).2 then seed.1 point else seed.2 point,
   fun point => if point ∈ (execute seed.1 program).2 then seed.2 point else seed.1 point)

theorem stable (program : OracleComp spec Result) (seed : Table spec × Table spec) :
    execute (exchanged program seed).1 program = execute seed.1 program := by
  apply execute_agree
  intro point member
  simp only [exchanged, member, if_true]

theorem involutive (program : OracleComp spec Result) : Function.Involutive (exchanged program) := by
  intro seed
  have same := stable program seed
  apply Prod.ext
  · funext point
    change (if point ∈ (execute (exchanged program seed).1 program).2 then
      (exchanged program seed).1 point else (exchanged program seed).2 point) = seed.1 point
    rw [same]
    simp only [exchanged]
    split_ifs <;> rfl
  · funext point
    change (if point ∈ (execute (exchanged program seed).1 program).2 then
      (exchanged program seed).2 point else (exchanged program seed).1 point) = seed.2 point
    rw [same]
    simp only [exchanged]
    split_ifs <;> rfl

def exchangeEquiv (program : OracleComp spec Result) : Equiv.Perm (Table spec × Table spec) :=
  { toFun := exchanged program
    invFun := exchanged program
    left_inv := involutive program
    right_inv := involutive program }

noncomputable section
variable [Fintype Point] [∀ point, Fintype (spec point)] [∀ point, Nonempty (spec point)]

/-- Exact full-transcript law after erasing every generation-read table value. -/
theorem erased_distribution (program : OracleComp spec Result)
    (postprocess : (Result × List Point) → Table spec → Output) :
    (PMF.uniformOfFintype (Table spec × Table spec)).map
      (fun seed => postprocess (execute seed.1 program) (exchanged program seed).2) =
    (PMF.uniformOfFintype (Table spec × Table spec)).map
      (fun seed => postprocess (execute seed.1 program) seed.2) := by
  have preserved := PMF.uniformOfFintype_map_of_bijective
    (exchangeEquiv program) (exchangeEquiv program).bijective
  calc
    _ = (PMF.uniformOfFintype (Table spec × Table spec)).map
        ((fun seed => postprocess (execute seed.1 program) seed.2) ∘ exchangeEquiv program) := by
      congr 1
      funext seed
      change postprocess (execute seed.1 program) (exchanged program seed).2 =
        postprocess (execute (exchanged program seed).1 program) (exchanged program seed).2
      rw [stable]
    _ = ((PMF.uniformOfFintype (Table spec × Table spec)).map (exchangeEquiv program)).map
        (fun seed => postprocess (execute seed.1 program) seed.2) := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [preserved]

end
end TranscriptErasure

/-! One unread-point argument for arbitrary finite dependent oracle tables. -/
namespace TypedFresh
open TranscriptErasure GameExpectation MomentTools
open ProbabilityTools
variable {Point Result : Type} [DecidableEq Point] {spec : OracleSpec Point}
variable [Fintype Point] [∀ point, Fintype (spec point)] [∀ point, Nonempty (spec point)]

/-- Evaluation at any fixed point of a uniform dependent function is uniform. -/
theorem uniform_eval (point : Point) :
    (PMF.uniformOfFintype (Table spec)).map (fun table => table point) =
      PMF.uniformOfFintype (spec point) := by
  let split := Equiv.piSplitAt point (fun point => spec point)
  have moved := PMF.uniformOfFintype_map_of_bijective split split.bijective
  calc
    _ = ((PMF.uniformOfFintype (Table spec)).map split).map Prod.fst :=
      (PMF.map_comp _ _ _).symm
    _ = _ := by rw [moved, ProbabilityTools.uniform_fst]

/-- The exact matching-set mass uses the response type of the selected oracle. -/
theorem fixed_hit [∀ point, DecidableEq (spec point)] (point : Point) (matching : Finset (spec point)) :
    moment (PMF.uniformOfFintype (Table spec))
      (fun table => if table point ∈ matching then 1 else 0) =
        (matching.card : ENNReal) / Fintype.card (spec point) := by
  have law := congrArg (fun distribution : PMF (spec point) =>
    moment distribution (fun answer => if answer ∈ matching then 1 else 0)) (uniform_eval point)
  try dsimp only at law
  rw [moment_map] at law
  dsimp only [Function.comp_def] at law
  rw [law]
  simp [moment, PMF.uniformOfFintype_apply, ENNReal.div_eq_inv_mul, mul_comm]

/-- The whole selected observation can be coupled to an independent table, including its history. -/
theorem observation_law {Output : Type} (program : OracleComp spec Result)
    (selected : Result × List Point → Point) (enabled : Result × List Point → Bool)
    (fresh : ∀ table, enabled (execute table program) = true →
      selected (execute table program) ∉ (execute table program).2)
    (active : (view : Result × List Point) → spec (selected view) → Output)
    (inactive : Result × List Point → Output) :
    (PMF.uniformOfFintype (Table spec)).map (fun table =>
      if enabled (execute table program) = true then
        active (execute table program) (table (selected (execute table program)))
      else inactive (execute table program)) =
    (PMF.uniformOfFintype (Table spec)).bind (fun table =>
      (PMF.uniformOfFintype (Table spec)).map (fun independent =>
        if enabled (execute table program) = true then
          active (execute table program) (independent (selected (execute table program)))
        else inactive (execute table program))) := by
  let observe := fun (view : Result × List Point) (table : Table spec) =>
    if enabled view = true then active view (table (selected view)) else inactive view
  have law := erased_distribution program observe
  have unchanged (seed : Table spec × Table spec) :
      observe (execute seed.1 program) (exchanged program seed).2 = observe (execute seed.1 program) seed.1 := by
    by_cases on : enabled (execute seed.1 program) = true
    · simp only [observe, if_pos on, exchanged, fresh seed.1 on, if_false]
    · simp only [observe, Bool.eq_false_iff.mpr on, Bool.false_eq_true, if_false]
  simp_rw [unchanged] at law
  rw [uniform_product] at law
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def] at law
  change ((PMF.uniformOfFintype (Table spec)).bind fun table =>
    (PMF.uniformOfFintype (Table spec)).map
      (Function.const (Table spec) (observe (execute table program) table))) = _ at law
  simp only [PMF.map_const] at law
  exact law

/-- No independence is assumed: erasing the transcript proves it for an unqueried point. -/
theorem hit_bound [∀ point, DecidableEq (spec point)]
    (program : OracleComp spec Result) (selected : Result × List Point → Point)
    (enabled : Result × List Point → Bool)
    (matching : (view : Result × List Point) → Finset (spec (selected view)))
    (fresh : ∀ table, enabled (execute table program) = true →
      selected (execute table program) ∉ (execute table program).2)
    (upper : Result × List Point → ENNReal)
    (size : ∀ view, enabled view = true →
      (matching view).card / (Fintype.card (spec (selected view)) : ENNReal) ≤ upper view) :
    moment (PMF.uniformOfFintype (Table spec)) (fun table =>
      if enabled (execute table program) = true ∧
        table (selected (execute table program)) ∈ matching (execute table program) then 1 else 0) ≤
      moment (PMF.uniformOfFintype (Table spec)) (fun table => upper (execute table program)) := by
  have law := observation_law program selected enabled fresh
    (fun view answer => if answer ∈ matching view then (1 : ENNReal) else 0) (fun _ => 0)
  have swap := congrArg (fun distribution : PMF ENNReal => moment distribution id) law
  simp only [moment_map, MomentTools.bind, Function.comp_def, id_eq] at swap
  simp only [ite_and]
  rw [swap]
  apply mono
  intro table
  by_cases on : enabled (execute table program) = true
  · simp only [if_pos on]
    rw [fixed_hit]
    exact size _ on
  · simp only [Bool.eq_false_iff.mpr on, Bool.false_eq_true, if_false,
      MomentTools.constant, zero_le]

end TypedFresh

/-! The existing four-table MHFE sampler is a presentation of the dependent table law. -/
namespace CryptoTablePresentation
open Gamma2Model TableFactors ProbabilityTools
variable {Password Entropy : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype

def points : Point Password Entropy ≃
    (Password × Half) ⊕ (Fin 12 × Half) ⊕ (Key × Fin 12 × Half) ⊕ Entropy where
  toFun point := match point with
    | .a p s => .inl (p,s)
    | .b i r => .inr (.inl (i,r))
    | .h k i r => .inr (.inr (.inl (k,i,r)))
    | .g e => .inr (.inr (.inr e))
  invFun point := match point with
    | .inl (p,s) => .a p s
    | .inr (.inl (i,r)) => .b i r
    | .inr (.inr (.inl (k,i,r))) => .h k i r
    | .inr (.inr (.inr e)) => .g e
  left_inv := by intro point; cases point <;> rfl
  right_inv := by
    intro point
    rcases point with point | point
    · cases point; rfl
    · rcases point with point | point
      · cases point; rfl
      · rcases point with point | point
        · rcases point with ⟨k,i,r⟩; rfl
        · rfl

local instance : Fintype (Point Password Entropy) := Fintype.ofEquiv _ points.symm
local instance (point : Point Password Entropy) : Fintype (spec Password Entropy point) := by
  cases point <;> dsimp only [spec] <;> infer_instance
local instance (point : Point Password Entropy) : Nonempty (spec Password Entropy point) := by
  cases point <;> dsimp only [spec] <;> infer_instance
local instance (point : Point Password Entropy) : DecidableEq (spec Password Entropy point) := by
  cases point <;> dsimp only [spec] <;> infer_instance

/-- This merely repackages the actual A,B,H,G functions; it does not change an oracle. -/
def tables : TranscriptErasure.Table (spec Password Entropy) ≃ Tables Password Entropy where
  toFun family := ⟨fun point => family (.a point.1 point.2), fun point => family (.b point.1 point.2),
    fun point => family (.h point.1 point.2.1 point.2.2), fun e => family (.g e)⟩
  invFun := answer
  left_inv := by intro family; funext point; cases point <;> rfl
  right_inv := by intro family; cases family; rfl

local instance : Fintype (Tables Password Entropy) := Fintype.ofEquiv (Quad Password Entropy) tableEquiv.symm
local instance : Nonempty (Tables Password Entropy) := ⟨⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩⟩

/-- The exact original joint prior, not just separate table marginals. -/
theorem sampling :
    (PMF.uniformOfFintype (TranscriptErasure.Table (spec Password Entropy))).map tables =
      sampleTables := by
  rw [sample_uniform]
  exact PMF.uniformOfFintype_map_of_bijective tables tables.bijective

omit [Fintype Password] [DecidableEq Password] [Fintype Entropy] [DecidableEq Entropy] in
/-- Execution and every repeated query agree under the table correspondence. -/
theorem execution (family : TranscriptErasure.Table (spec Password Entropy))
    (program : OracleComp (spec Password Entropy) Result) :
    TranscriptErasure.execute family program = execute (tables family) program := by
  have same : answer (tables family) = family := tables.symm_apply_apply family
  change TranscriptErasure.execute family program =
    TranscriptErasure.execute (answer (tables family)) program
  rw [same]

/-- Apply the single freshness argument to the exact original MHFE execution and joint table prior. -/
theorem hit_bound (program : OracleComp (spec Password Entropy) Result)
    (selected : Result × List (Point Password Entropy) → Point Password Entropy)
    (enabled : Result × List (Point Password Entropy) → Bool)
    (matching : (view : Result × List (Point Password Entropy)) → Finset (spec Password Entropy (selected view)))
    (fresh : ∀ table, enabled (execute table program) = true → selected (execute table program) ∉ (execute table program).2)
    (upper : Tables Password Entropy → ENNReal)
    (size : ∀ table, enabled (execute table program) = true → (matching (execute table program)).card / (Fintype.card (spec Password Entropy (selected (execute table program))) : ENNReal) ≤ upper table) :
    GameExpectation.moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun table => if enabled (execute table program) = true ∧
        answer table (selected (execute table program)) ∈ matching (execute table program) then 1 else 0) ≤
    GameExpectation.moment sampleTables upper := by
  rw [← sampling, GameExpectation.moment_map, GameExpectation.moment_map]
  dsimp only [Function.comp_def]
  have lookups (family : TranscriptErasure.Table (spec Password Entropy)) :
      answer (tables family) = family := tables.symm_apply_apply family
  simp_rw [lookups]
  let score := fun (family : TranscriptErasure.Table (spec Password Entropy))
      (view : Result × List (Point Password Entropy)) =>
    if enabled view = true ∧ family (selected view) ∈ matching view then (1 : ENNReal) else 0
  have change_view : (fun family => score family (execute (tables family) program)) =
      (fun family => score family (TranscriptErasure.execute family program)) := by
    funext family
    exact congrArg (score family) (execution family program).symm
  change GameExpectation.moment _
    (fun family => score family (execute (tables family) program)) ≤ _
  rw [change_view]
  let ratio := fun view => if enabled view = true then
    (matching view).card / (Fintype.card (spec Password Entropy (selected view)) : ENNReal) else 0
  have bound := TypedFresh.hit_bound program selected enabled matching
    (fun family on => by rw [execution] at on ⊢; exact fresh (tables family) on) ratio
    (fun view on => by simp only [ratio, on, if_true, le_refl])
  apply bound.trans
  apply MomentTools.mono
  intro family
  rw [execution]
  by_cases on : enabled (execute (tables family) program) = true
  · simpa only [ratio, on, if_true] using size (tables family) on
  · simp only [ratio, Bool.eq_false_iff.mpr on, Bool.false_eq_true, if_false, zero_le]

end CryptoTablePresentation

/-!
A small deterministic oracle-query language for the freshness foundation.
A program can learn a table value only by making a query. Its continuation may
depend on that answer. OracleProjection connects this language to the
MHFE oracle experiment.
-/

namespace OracleTree

/-- Finite adaptive query trees, with one common answer type. -/
inductive Program (Domain Answer Result : Type)
  | done (result : Result)
  | query (point : Domain) (next : Answer → Program Domain Answer Result)

variable {Domain Answer Result Context : Type} [DecidableEq Domain]

/-- Evaluate with a fixed consistent table and retain the entire query transcript. -/
def evaluate (table : Domain → Answer) : Program Domain Answer Result → Result × List Domain
  | .done result => (result, [])
  | .query point next =>
    let result := evaluate table (next (table point))
    (result.1, point :: result.2)

/-- The older focused-tree interface embeds in the common oracle language. -/
def asOracle : Program Domain Answer Result → OracleComp (fun _ : Domain => Answer) Result
  | .done result => pure result
  | .query point next => do
    let answer ← TranscriptErasure.ask point
    asOracle (next answer)

omit [DecidableEq Domain] in
/-- This embedding preserves both the result and every repeated table lookup. -/
theorem asOracle_execution (program : Program Domain Answer Result) (table : Domain → Answer) :
    TranscriptErasure.execute table (asOracle program) = evaluate table program := by
  classical
  induction program <;> aesop (add simp [asOracle, TranscriptErasure.execute_bind,
    TranscriptErasure.execute_ask, List.singleton_append, evaluate])

/-- Return a proposed fresh point and context only if the point was never queried. -/
def selectFresh (program : Program Domain Answer (Domain × Context)) (table : Domain → Answer) :
    Option (Domain × Context) :=
  let result := evaluate table program
  if result.1.1 ∈ result.2 then none else some result.1

end OracleTree

end

/-!
Project a typed MHFE execution onto one random-oracle table while fixing the
other tables. This connects the actual executor to the fresh-sampling language.
The projection preserves the result and the complete typed query transcript.
-/

namespace OracleProjection

open Gamma2Model OracleTree

variable {Password Entropy Domain Answer Result Output : Type}

/-- Change only the terminal result of a uniform-answer query tree. -/
def mapResult (transform : Result → Output) : Program Domain Answer Result →
    Program Domain Answer Output
  | .done result => .done (transform result)
  | .query point next => .query point (fun value => mapResult transform (next value))

/-- Mapping a result preserves all queried points and their order. -/
theorem evaluate_mapResult (table : Domain → Answer) (transform : Result → Output)
    (program : Program Domain Answer Result) :
    evaluate table (mapResult transform program) =
      let result := evaluate table program
      (transform result.1, result.2) := by
  induction program with
  | done result => rfl
  | query point next ih => simp only [mapResult, evaluate, ih]

/-- A query is either answered by fixed other tables or delegated to the selected table. -/
abbrev Handler (Password Entropy Domain Answer : Type) :=
  (point : Point Password Entropy) →
    Sum (spec Password Entropy point) (Domain × (Answer → spec Password Entropy point))

/-- Resolve a projected query using a fixed selected table. -/
def resolve (handler : Handler Password Entropy Domain Answer) (table : Domain → Answer)
    (point : Point Password Entropy) : spec Password Entropy point :=
  match handler point with
  | .inl fixed => fixed
  | .inr (selected, decode) => decode (table selected)

/-- Compile a typed adaptive execution without direct access to the selected table. -/
def project (handler : Handler Password Entropy Domain Answer)
    (program : OracleComp (spec Password Entropy) Result) :
    Program Domain Answer (Result × List (Point Password Entropy)) :=
  OracleComp.construct
    (fun result => .done (result, []))
    (fun point _ recurse =>
      let prepend := fun result : Result × List (Point Password Entropy) =>
        (result.1, point :: result.2)
      match handler point with
      | .inl fixed => mapResult prepend (recurse fixed)
      | .inr (selected, decode) =>
        .query selected (fun value => mapResult prepend (recurse (decode value)))) program

/-- The delegated query identity, if this query belongs to the selected table. -/
def delegatedPoint (handler : Handler Password Entropy Domain Answer)
    (point : Point Password Entropy) : Option Domain :=
  match handler point with
  | .inl _ => none
  | .inr (selected, _) => some selected

variable (handler : Handler Password Entropy Domain Answer) (selectedTable : Domain → Answer)
  (tables : Tables Password Entropy)

/-- One induction preserves both the full typed execution and its selected-table trace. -/
theorem project_execution
    (agrees : ∀ point, resolve handler selectedTable point = answer tables point)
    (program : OracleComp (spec Password Entropy) Result) :
    evaluate selectedTable (project handler program) =
      (execute tables program, (execute tables program).2.filterMap (delegatedPoint handler)) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih =>
    have actual := agrees point
    simp only [project, OracleComp.construct_query_bind]
    cases selected : handler point with
    | inl fixed =>
      simp only [evaluate_mapResult]
      change (((evaluate selectedTable (project handler (next fixed))).1.1,
          point :: (evaluate selectedTable (project handler (next fixed))).1.2),
        (evaluate selectedTable (project handler (next fixed))).2) = _
      rw [ih fixed]
      have value : fixed = answer tables point := by
        simpa only [resolve, selected] using actual
      rw [value]
      change _ = (execute tables (ask point >>= next),
        (execute tables (ask point >>= next)).2.filterMap (delegatedPoint handler))
      simp only [execute_bind, execute_ask, List.singleton_append,
        List.filterMap_cons, delegatedPoint, selected]
    | inr delegated =>
      rcases delegated with ⟨query, decode⟩
      simp only [evaluate, evaluate_mapResult]
      change (((evaluate selectedTable (project handler (next (decode (selectedTable query))))).1.1,
          point :: (evaluate selectedTable (project handler (next (decode (selectedTable query))))).1.2),
        query :: (evaluate selectedTable (project handler (next (decode (selectedTable query))))).2) = _
      rw [ih (decode (selectedTable query))]
      have value : decode (selectedTable query) = answer tables point := by
        simpa only [resolve, selected] using actual
      rw [value]
      change _ = (execute tables (ask point >>= next),
        (execute tables (ask point >>= next)).2.filterMap (delegatedPoint handler))
      simp only [execute_bind, execute_ask, List.singleton_append,
        List.filterMap_cons, delegatedPoint, selected]

/-- The projection preserves the complete typed execution, not only the final result. -/
theorem project_evaluates
    (agrees : ∀ point, resolve handler selectedTable point = answer tables point)
    (program : OracleComp (spec Password Entropy) Result) :
    (evaluate selectedTable (project handler program)).1 = execute tables program :=
  congrArg Prod.fst (project_execution handler selectedTable tables agrees program)

/-- The projection's query log is exactly the selected-table part of the original log. -/
theorem project_delegated_trace
    (agrees : ∀ point, resolve handler selectedTable point = answer tables point)
    (program : OracleComp (spec Password Entropy) Result) :
    (evaluate selectedTable (project handler program)).2 =
      (execute tables program).2.filterMap (delegatedPoint handler) :=
  congrArg Prod.snd (project_execution handler selectedTable tables agrees program)

/-- Typed freshness transfers to the selected-table trace used by selectFresh. -/
theorem projected_fresh
    (agrees : ∀ point, resolve handler selectedTable point = answer tables point)
    (program : OracleComp (spec Password Entropy) Result) (typedPoint : Point Password Entropy)
    (selectedPoint : Domain)
    (identifies : ∀ point, delegatedPoint handler point = some selectedPoint → point = typedPoint)
    (fresh : typedPoint ∉ (execute tables program).2) :
    selectedPoint ∉ (evaluate selectedTable (project handler program)).2 := by
  rw [project_delegated_trace handler selectedTable tables agrees]
  intro present
  obtain ⟨point, queried, selected⟩ := List.mem_filterMap.mp present
  exact fresh ((identifies point selected) ▸ queried)

/-- Freeze B, H and G, leaving only A queries for the uniform-answer program. -/
def focusA (b : Fin 12 × Half → Half) (h : Key × Fin 12 × Half → Half)
    (g : Entropy → Hash) : Handler Password Entropy (Password × Half) Key
  | .a password salt => .inr ((password, salt), id)
  | .b round right => .inl (b (round, right))
  | .h key round right => .inl (h (key, round, right))
  | .g entropy => .inl (g entropy)

/-- Freeze A, H and G, leaving only B queries for the uniform-answer program. -/
def focusB (a : Password × Half → Key) (h : Key × Fin 12 × Half → Half)
    (g : Entropy → Hash) : Handler Password Entropy (Fin 12 × Half) Half
  | .a password salt => .inl (a (password, salt))
  | .b round right => .inr ((round, right), id)
  | .h key round right => .inl (h (key, round, right))
  | .g entropy => .inl (g entropy)

/-- Freeze A, B and G, leaving only H queries for the uniform-answer program. -/
def focusH (a : Password × Half → Key) (b : Fin 12 × Half → Half)
    (g : Entropy → Hash) : Handler Password Entropy (Key × Fin 12 × Half) Half
  | .a password salt => .inl (a (password, salt))
  | .b round right => .inl (b (round, right))
  | .h key round right => .inr ((key, round, right), id)
  | .g entropy => .inl (g entropy)

/-- A-focused execution has exactly the original full execution result and trace. -/
theorem focusA_evaluates (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) :
    (evaluate tables.a (project (focusA tables.b tables.h tables.g) program)).1 =
      execute tables program := by
  apply project_evaluates
  intro point
  cases point <;> rfl

/-- B-focused execution has exactly the original full execution result and trace. -/
theorem focusB_evaluates (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) :
    (evaluate tables.b (project (focusB tables.a tables.h tables.g) program)).1 =
      execute tables program := by
  apply project_evaluates
  intro point
  cases point <;> rfl

/-- H-focused execution has exactly the original full execution result and trace. -/
theorem focusH_evaluates (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) :
    (evaluate tables.h (project (focusH tables.a tables.b tables.g) program)).1 =
      execute tables program := by
  apply project_evaluates
  intro point
  cases point <;> rfl

end OracleProjection

/-! Preserve the selected-table query log while discarding the internally retained full log. -/

namespace FocusedExecution

open Gamma2Model OracleTree OracleProjection

variable {Password Entropy Domain Answer Result : Type}

/-- Execute only the unfrozen table, retaining the original program result. -/
def focused (handler : Handler Password Entropy Domain Answer)
    (program : OracleComp (spec Password Entropy) Result) : Program Domain Answer Result :=
  mapResult Prod.fst (project handler program)

variable (handler : Handler Password Entropy Domain Answer) (selectedTable : Domain → Answer)
  (tables : Tables Password Entropy)

/-- The focused result is exactly the result of the original typed execution. -/
theorem result_eq (agrees : ∀ point, resolve handler selectedTable point = answer tables point)
    (program : OracleComp (spec Password Entropy) Result) :
    (evaluate selectedTable (focused handler program)).1 = (execute tables program).1 := by
  simp only [focused, evaluate_mapResult]
  rw [project_evaluates handler selectedTable tables agrees]

/-- The focused query log contains exactly the selected-table queries of the full log. -/
theorem trace_eq (agrees : ∀ point, resolve handler selectedTable point = answer tables point)
    (program : OracleComp (spec Password Entropy) Result) :
    (evaluate selectedTable (focused handler program)).2 =
      (execute tables program).2.filterMap (delegatedPoint handler) := by
  simp only [focused, evaluate_mapResult]
  exact project_delegated_trace handler selectedTable tables agrees program

/-- An enabled typed selection remains unqueried in the focused program. -/
theorem fresh_of_typed (agrees : ∀ point, resolve handler selectedTable point = answer tables point)
    (program : OracleComp (spec Password Entropy) Result) (typedPoint : Point Password Entropy)
    (selectedPoint : Domain)
    (identifies : ∀ point, delegatedPoint handler point = some selectedPoint → point = typedPoint)
    (fresh : typedPoint ∉ (execute tables program).2) :
    selectedPoint ∉ (evaluate selectedTable (focused handler program)).2 := by
  simpa only [focused, evaluate_mapResult] using
    projected_fresh handler selectedTable tables agrees program typedPoint selectedPoint identifies fresh

end FocusedExecution

/-!
Adaptive fresh-query sampling. A selected point may depend on all earlier
oracle answers. Selection is retained only when the program has not queried
that point. No freshness probability is assumed as an axiom.
This is a foundation for G3, not a completed formalization of that source lemma.
-/

namespace FreshSampling

open OracleTree ProbabilityTools

variable {Domain Answer Context : Type} [DecidableEq Domain]

/-- Observe the selected point/context together with its real table answer. -/
def observedTable (program : Program Domain Answer (Domain × Context)) (table : Domain → Answer) :
    Option ((Domain × Context) × Answer) :=
  (selectFresh program table).map fun chosen => (chosen, table chosen.1)

variable [Fintype Domain] [Fintype Answer] [Nonempty Answer]

/-- The full output law agrees with the law using an independent fresh answer. -/
theorem fresh_query_distribution (program : Program Domain Answer (Domain × Context)) :
    (PMF.uniformOfFintype (Domain → Answer)).map (observedTable program) =
      (PMF.uniformOfFintype (Domain → Answer)).bind fun table =>
        (PMF.uniformOfFintype Answer).map fun value =>
          (selectFresh program table).map (fun chosen => (chosen, value)) := by
  have law := TypedFresh.observation_law (asOracle program)
    (fun view => view.1.1) (fun view => decide (view.1.1 ∉ view.2))
    (fun _ enabled => of_decide_eq_true enabled)
    (fun view answer => some (view.1, answer)) (fun _ => none)
  let observe := fun (view : (Domain × Context) × List Domain) (table : Domain → Answer) =>
    if decide (view.1.1 ∉ view.2) = true then some (view.1,table view.1.1) else none
  change (PMF.uniformOfFintype (Domain → Answer)).map
      (fun table => observe (TranscriptErasure.execute table (asOracle program)) table) =
    (PMF.uniformOfFintype (Domain → Answer)).bind (fun table =>
      (PMF.uniformOfFintype (Domain → Answer)).map (fun independent =>
        observe (TranscriptErasure.execute table (asOracle program)) independent)) at law
  have changed_view (table independent : Domain → Answer) :
      observe (TranscriptErasure.execute table (asOracle program)) independent =
        observe (evaluate table program) independent :=
    congrArg (fun view => observe view independent) (asOracle_execution program table)
  simp_rw [changed_view] at law
  have actual : observedTable program = fun table => observe (evaluate table program) table := by
    funext table
    by_cases cached : (evaluate table program).1.1 ∈ (evaluate table program).2 <;>
      simp [observe, observedTable, selectFresh, cached]
  rw [actual, law]
  apply congrArg (fun next => (PMF.uniformOfFintype (Domain → Answer)).bind next)
  funext table
  dsimp only [observe]
  by_cases cached : (evaluate table program).1.1 ∈ (evaluate table program).2
  · simp only [cached, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
      selectFresh]
    change (PMF.uniformOfFintype (Domain → Answer)).map
        (Function.const (Domain → Answer) (none : Option ((Domain × Context) × Answer))) =
      (PMF.uniformOfFintype Answer).map (Function.const Answer none)
    rw [PMF.map_const, PMF.map_const]
  · have pointLaw := TypedFresh.uniform_eval (spec := fun _ : Domain => Answer)
      (evaluate table program).1.1
    have extracted := congrArg (fun distribution : PMF Answer =>
      distribution.map (fun answer => some ((evaluate table program).1,answer))) pointLaw
    simpa [selectFresh, cached, PMF.map_comp, Function.comp_def] using extracted

/-- A uniform answer lands in a fixed finite matching set with the expected mass. -/
theorem uniform_hit_probability [DecidableEq Answer] (matching : Finset Answer) :
    ((PMF.uniformOfFintype Answer).map (fun value => decide (value ∈ matching))) true =
      (matching.card : ENNReal) / (Fintype.card Answer : ENNReal) := by
  classical
  simp [PMF.map_apply, PMF.uniformOfFintype_apply, ENNReal.div_eq_inv_mul, mul_comm]

/-- Test a matching set determined by the selected pre-query context. -/
def hits [DecidableEq Answer] (matching : Context → Finset Answer) :
    Option ((Domain × Context) × Answer) → Bool
  | none => false
  | some ((_, context), value) => decide (value ∈ matching context)

/-- Matching size may depend on the actual table; no independence of the budget is assumed. -/
theorem fresh_hit_table_bound [DecidableEq Answer]
    (program : Program Domain Answer (Domain × Context)) (matching : Context → Finset Answer)
    (budget : (Domain → Answer) → Nat)
    (sizeBound : ∀ table, (matching (evaluate table program).1.2).card ≤ budget table) :
    (((PMF.uniformOfFintype (Domain → Answer)).map (observedTable program)).map
        (hits matching)) true ≤
      GameExpectation.moment (PMF.uniformOfFintype (Domain → Answer))
        (fun table => (budget table : ENNReal) / Fintype.card Answer) := by
  have bound := TypedFresh.hit_bound (asOracle program)
    (fun view => view.1.1) (fun view => decide (view.1.1 ∉ view.2))
    (fun view => matching view.1.2)
    (fun _ enabled => of_decide_eq_true enabled)
    (fun view => ((matching view.1.2).card : ENNReal) / Fintype.card Answer)
    (fun _ _ => le_rfl)
  have capped := MomentTools.mono (PMF.uniformOfFintype (Domain → Answer))
    (fun table => ((matching (TranscriptErasure.execute table (asOracle program)).1.2).card : ENNReal) /
      Fintype.card Answer) (fun table => (budget table : ENNReal) / Fintype.card Answer)
    (fun table => by
      try dsimp only
      rw [asOracle_execution]
      exact ENNReal.div_le_div_right (by exact_mod_cast sizeBound table) _)
  apply le_trans ?_ (bound.trans capped)
  apply le_of_eq
  rw [PMF.map_comp, MomentTools.probability]
  apply congrArg (GameExpectation.moment (PMF.uniformOfFintype (Domain → Answer)))
  funext table
  simp only [Function.comp_def, asOracle_execution]
  by_cases cached : (evaluate table program).1.1 ∈ (evaluate table program).2 <;>
    simp [observedTable, selectFresh, hits, cached]

/-- A fixed matching-set cap is a specialization of the table-dependent bound. -/
theorem fresh_hit_bound [DecidableEq Answer] (program : Program Domain Answer (Domain × Context))
    (matching : Context → Finset Answer) (limit : Nat)
    (sizeBound : ∀ context, (matching context).card ≤ limit) :
    (((PMF.uniformOfFintype (Domain → Answer)).map (observedTable program)).map
        (hits matching)) true ≤ (limit : ENNReal) / (Fintype.card Answer : ENNReal) := by
  have bound := fresh_hit_table_bound program matching (fun _ => limit)
    (fun table => sizeBound (evaluate table program).1.2)
  simpa only [MomentTools.constant] using bound

end FreshSampling

/-!
A stopped program may decline to select a point. Disabled contexts have an
empty matching set; only enabled contexts need to certify freshness.
-/

namespace OptionalFresh

open OracleTree FreshSampling

variable {Domain Answer Context : Type}

/-- A disabled selection has no values that count as a hit. -/
def optionalSet (matching : Context → Finset Answer) : Option Context → Finset Answer
  | none => ∅
  | some context => matching context

/-- Test the selected table answer directly, with disabled selections counting as false. -/
def rawHit [DecidableEq Answer] (program : Program Domain Answer (Domain × Option Context))
    (matching : Context → Finset Answer) (table : Domain → Answer) : Bool :=
  let result := (evaluate table program).1
  decide (table result.1 ∈ optionalSet matching result.2)

/-- Operational freshness is required precisely when the program enables its context. -/
def EnabledFresh (program : Program Domain Answer (Domain × Option Context)) : Prop :=
  ∀ table, (evaluate table program).1.2 ≠ none →
    (evaluate table program).1.1 ∉ (evaluate table program).2

/-- A selected point already queried by the program necessarily has a disabled context. -/
theorem cached_disabled (program : Program Domain Answer (Domain × Option Context))
    (fresh : EnabledFresh program) (table : Domain → Answer)
    (cached : (evaluate table program).1.1 ∈ (evaluate table program).2) :
    (evaluate table program).1.2 = none := by
  by_cases disabled : (evaluate table program).1.2 = none
  · exact disabled
  · exact False.elim (fresh table disabled cached)

variable [DecidableEq Domain] [DecidableEq Answer]

/-- The freshness gate and the direct enabled-context test are the same event. -/
theorem observed_agrees (program : Program Domain Answer (Domain × Option Context))
    (matching : Context → Finset Answer) (fresh : EnabledFresh program) (table : Domain → Answer) :
    hits (optionalSet matching) (observedTable program table) = rawHit program matching table := by
  by_cases cached : (evaluate table program).1.1 ∈ (evaluate table program).2
  · have disabled := cached_disabled program fresh table cached
    simp [observedTable, selectFresh, cached, hits, rawHit, disabled, optionalSet]
  · simp only [observedTable, selectFresh, if_neg cached, Option.map_some, hits, rawHit]

variable [Fintype Domain] [Fintype Answer] [Nonempty Answer]

/-- Matching-size bounds transfer to probability bounds before averaging other tables. -/
theorem hit_bound (program : Program Domain Answer (Domain × Option Context))
    (matching : Context → Finset Answer) (fresh : EnabledFresh program)
    (budget : (Domain → Answer) → Nat)
    (bounded : ∀ table, (optionalSet matching (evaluate table program).1.2).card ≤ budget table) :
    ((PMF.uniformOfFintype (Domain → Answer)).map (rawHit program matching)) true ≤
      ∑' table, PMF.uniformOfFintype (Domain → Answer) table *
        ((budget table : ENNReal) / (Fintype.card Answer : ENNReal)) := by
  have bound := fresh_hit_table_bound program (optionalSet matching) budget bounded
  rw [PMF.map_comp] at bound
  have same : hits (optionalSet matching) ∘ observedTable program = rawHit program matching := by
    funext table
    exact observed_agrees program matching fresh table
  rw [same] at bound
  exact bound

end OptionalFresh

/-!
Transfer an enabled typed selection's freshness to the focused random-table
program. The handler and program are fixed; only fullTables receives the chosen
table, exclusively for deterministic execution and the certificate proof.
-/

namespace EnabledProjection

open Gamma2Model OracleProjection FocusedExecution

variable {Password Entropy Domain Answer Context : Type}

/-- Enabled typed selections provide the exact operational premise of OptionalFresh. -/
theorem enabled_fresh (handler : Handler Password Entropy Domain Answer)
    (fullTables : (Domain → Answer) → Tables Password Entropy)
    (agrees : ∀ table point, resolve handler table point = answer (fullTables table) point)
    (program : OracleComp (spec Password Entropy) (Domain × Option Context))
    (embed : Domain → Point Password Entropy)
    (identifies : ∀ point selected, delegatedPoint handler point = some selected → point = embed selected)
    (certificate : ∀ table, (execute (fullTables table) program).1.2 ≠ none → embed (execute (fullTables table) program).1.1 ∉ (execute (fullTables table) program).2) :
    OptionalFresh.EnabledFresh (focused handler program) := by
  intro table enabled
  rw [result_eq handler table (fullTables table) (agrees table) program] at enabled ⊢
  exact fresh_of_typed handler table (fullTables table) (agrees table) program
    (embed (execute (fullTables table) program).1.1) (execute (fullTables table) program).1.1
    (fun point selected => identifies point _ selected) (certificate table enabled)

end EnabledProjection

end
end MhfeLean
