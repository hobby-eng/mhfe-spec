/- long: the shared typed oracles and exact execution laws form one mathematical model. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases
import MhfeLean.Chapters.Feistel
import Std
import ToMathlib.Control.WriterT
import VCVio.OracleComp.SimSemantics.SimulateQ

namespace MhfeLean
noncomputable section

/-! # Ideal oracles and chronological chain execution
-/

/-!
# MHFE supplement: Lemma G2 (order)

A finite transcript starts with an empty oracle table. Each query inserts its
point if new and returns its answer before the next query. The adversary's
queries are a prefix; finalization queries follow it. Point identity includes
the oracle type. The chain is numbered from zero in this module.
-/

namespace G2

/-- A complete sequential query transcript and the chain finalized in it. -/
structure Run (Point : Type) where
  queries : List Point
  halt : Nat
  halt_le_length : halt ≤ queries.length
  point : Nat → Point
  count : Nat
  complete : ∀ index, index < count → point index ∈ queries

variable {Point : Type} [DecidableEq Point]

/-- The first query is the first moment at which a point's answer is sampled. -/
def firstTime (run : Run Point) (index : Nat) : Nat :=
  run.queries.idxOf (run.point index)

/-- A point is defined once its predecessor is both defined and answered. -/
def definedTime (run : Run Point) : Nat → Nat
  | 0 => 0
  | index + 1 => max (definedTime run index) (firstTime run index + 1)

/-- An early point is already in the table when it becomes defined. -/
def Early (run : Run Point) : Prop :=
  ∃ index, 0 < index ∧ index < run.count ∧ firstTime run index < definedTime run index

/-- Prefix membership is equivalent to querying the point before the adversary halts. -/
def Queried (run : Run Point) (index : Nat) : Prop := firstTime run index < run.halt

/-- No early point forces every chain query to follow its predecessor strictly. -/
theorem ordered (run : Run Point) (notEarly : ¬ Early run) (index : Nat) (positive : 0 < index)
    (within : index < run.count) : firstTime run (index - 1) < firstTime run index := by
  have fresh : definedTime run index ≤ firstTime run index := by
    by_cases enough : definedTime run index ≤ firstTime run index
    · exact enough
    · have tooEarly : firstTime run index < definedTime run index := by omega
      exact False.elim (notEarly ⟨index, positive, within, tooEarly⟩)
  cases index with
  | zero => omega
  | succ previous =>
    have afterAnswer : firstTime run previous + 1 ≤ definedTime run (previous + 1) :=
      Nat.le_max_right _ _
    simp only [Nat.add_sub_cancel] at *
    omega

/-- Lemma G2's adversary-query conclusion, including the finalization boundary. -/
theorem predecessor_queried (run : Run Point) (notEarly : ¬ Early run) (index : Nat)
    (positive : 0 < index) (within : index < run.count) (queried : Queried run index) :
    Queried run (index - 1) ∧ firstTime run (index - 1) < firstTime run index := by
  have before := ordered run notEarly index positive within
  exact ⟨Nat.lt_trans before queried, before⟩

/-- The order also holds between nonadjacent chain points. -/
theorem all_ordered (run : Run Point) (notEarly : ¬ Early run) (earlier later : Nat)
    (inOrder : earlier < later) (within : later < run.count) :
    firstTime run earlier < firstTime run later := by
  induction later generalizing earlier with
  | zero => omega
  | succ previous ih =>
    have adjacent := ordered run notEarly (previous + 1) (by omega) within
    have earlier_le : earlier ≤ previous := by omega
    by_cases equal : earlier = previous
    · simpa [equal] using adjacent
    · have before : earlier < previous := by omega
      exact Nat.lt_trans (ih earlier before (by omega)) adjacent

/-- If the adversary missed one chain point, it missed every later chain point. -/
theorem missing_later (run : Run Point) (notEarly : ¬ Early run) (earlier later : Nat)
    (inOrder : earlier < later) (within : later < run.count) (missing : ¬ Queried run earlier) :
    ¬ Queried run later := by
  intro queried
  apply missing
  exact Nat.lt_trans (all_ordered run notEarly earlier later inOrder within) queried

end G2

/-!
Eager-table Gamma2 model for the probability bounds.
The ideal tables are sampled independently; real cryptographic implementations
are outside this model. Lemma G3 is proved in the ChainEarly chapter.
-/

namespace Gamma2Model

open OracleComp

abbrev Half := BitVec 128
abbrev Key := BitVec 256
abbrev Hash := BitVec 256
abbrev State := Lemma1.State 128

/-- Oracle identity is part of the query point's type and equality. -/
inductive Point (Password Entropy : Type)
  | a (password : Password) (salt : Half)
  | b (round : Fin 12) (right : Half)
  | h (key : Key) (round : Fin 12) (right : Half)
  | g (entropy : Entropy)
  deriving DecidableEq

/-- The answer width follows Appendix A.1 exactly. -/
@[reducible] def spec (Password Entropy : Type) : OracleSpec (Point Password Entropy)
  | .a _ _ => Key
  | .b _ _ => Half
  | .h _ _ _ => Half
  | .g _ => Hash

/-- Complete ideal oracle tables. -/
structure Tables (Password Entropy : Type) where
  a : Password × Half → Key
  b : Fin 12 × Half → Half
  h : Key × Fin 12 × Half → Half
  g : Entropy → Hash

/-- Look up the correct table and preserve the dependent answer type. -/
def answer (tables : Tables Password Entropy) :
    (point : Point Password Entropy) → spec Password Entropy point
  | .a password salt => tables.a (password, salt)
  | .b round right => tables.b (round, right)
  | .h key round right => tables.h (key, round, right)
  | .g entropy => tables.g entropy

/-- Deterministic query evaluation logs every lookup, including repeated points. -/
def loggingImpl (tables : Tables Password Entropy) :
    QueryImpl (spec Password Entropy) (Writer (List (Point Password Entropy))) :=
  fun point => WriterT.mk (answer tables point, [point])

/-- Evaluate a VCVio adaptive program against the fixed consistent tables. -/
def execute (tables : Tables Password Entropy) (program : OracleComp (spec Password Entropy) Result) :
    Result × List (Point Password Entropy) :=
  (simulateQ (loggingImpl tables) program).run

/-- Make one typed oracle query. -/
def ask (point : Point Password Entropy) :
    OracleComp (spec Password Entropy) (spec Password Entropy point) :=
  OracleComp.lift (OracleSpec.query (spec := spec Password Entropy) point)

@[simp] theorem execute_pure (tables : Tables Password Entropy) (result : Result) :
    execute tables (pure result) = (result, []) := rfl

@[simp] theorem execute_bind (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result)
    (next : Result → OracleComp (spec Password Entropy) Output) :
    execute tables (program >>= next) =
      let first := execute tables program
      let second := execute tables (next first.1)
      (second.1, first.2 ++ second.2) := by
  simp only [execute, simulateQ_bind]
  rfl

@[simp] theorem execute_map (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) (transform : Result → Output) :
    execute tables (transform <$> program) =
      let result := execute tables program
      (transform result.1, result.2) := by
  simp only [execute, simulateQ_map]
  rfl

@[simp] theorem execute_ask (tables : Tables Password Entropy) (point : Point Password Entropy) :
    execute tables (ask point) = (answer tables point, [point]) := by
  simp [execute, ask, OracleComp.lift, simulateQ_query, loggingImpl]

/-! The same law with the answer type already reduced, as it occurs after a typed `do` binding. -/
@[simp] theorem execute_ask_a (tables : Tables Password Entropy) (password : Password) (salt : Half) :
    @execute Password Entropy Key tables (ask (.a password salt)) =
      (tables.a (password, salt), [.a password salt]) := execute_ask tables _
@[simp] theorem execute_ask_b (tables : Tables Password Entropy) (round : Fin 12) (right : Half) :
    @execute Password Entropy Half tables (ask (.b round right)) =
      (tables.b (round, right), [.b round right]) := execute_ask tables _
@[simp] theorem execute_ask_h (tables : Tables Password Entropy) (key : Key) (round : Fin 12)
    (right : Half) :
    @execute Password Entropy Half tables (ask (.h key round right)) =
      (tables.h (key, round, right), [.h key round right]) := execute_ask tables _
@[simp] theorem execute_ask_g (tables : Tables Password Entropy) (entropy : Entropy) :
    @execute Password Entropy Hash tables (ask (.g entropy)) =
      (tables.g entropy, [.g entropy]) := execute_ask tables _

/-- Query the actual inverse rounds 11 down to 0, retaining their chain points. -/
def finalize (password : Password) :
    (fuel : Nat) → State → fuel ≤ 12 →
      OracleComp (spec Password Entropy) (State × List (Point Password Entropy))
  | 0, state, _ => pure (state, [])
  | fuel + 1, state, bounded => do
    let round : Fin 12 := ⟨fuel, by omega⟩
    let salt : Half ← ask (.b round state.1)
    let key : Key ← ask (.a password salt)
    let mask : Half ← ask (.h key round state.1)
    let nextState : State := (state.2 ^^^ mask, state.1)
    let remaining ← finalize password fuel nextState (by omega)
    return (remaining.1,
      [.b round state.1, .a password salt, .h key round state.1] ++ remaining.2)

/-- The finalization log is precisely the list of chain points it returns. -/
theorem finalize_trace (tables : Tables Password Entropy) (password : Password) (fuel : Nat)
    (state : State) (bounded : fuel ≤ 12) :
    (execute tables (finalize password fuel state bounded)).2 =
      (execute tables (finalize password fuel state bounded)).1.2 := by
  classical
  induction fuel generalizing state <;> aesop (add simp [finalize, execute_bind, execute_ask,
    execute_pure, execute_map, answer, List.cons_append, List.nil_append, List.append_nil])

/-- Three typed oracle points are queried for every inverse round. -/
theorem finalize_chain_length (tables : Tables Password Entropy) (password : Password) (fuel : Nat)
    (state : State) (bounded : fuel ≤ 12) :
    (execute tables (finalize password fuel state bounded)).1.2.length = 3 * fuel := by
  classical
  induction fuel generalizing state <;> aesop (add simp [finalize, execute_bind, execute_ask,
    execute_pure, execute_map, answer, List.length_append, List.length_cons, List.length_nil])

/-- Retained data after the adversary and the private finalization have run. -/
structure Outcome (Password Entropy Result : Type) where
  password : Password
  container : State
  tables : Tables Password Entropy
  result : Result
  adversaryQueries : List (Point Password Entropy)
  recovered : State
  chain : List (Point Password Entropy)
  finalQueries : List (Point Password Entropy)

/-- The password is used only for finalization, after the adversary has halted. -/
def outcome (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    Outcome Password Entropy Result :=
  let before := execute tables (adversary container)
  let after := execute tables (finalize password 12 container (by omega))
  { password, container, tables, result := before.1, adversaryQueries := before.2,
    recovered := after.1.1, chain := after.1.2, finalQueries := after.2 }

/-- A fallback outside the 36 chain indices; it is never used by an in-range theorem. -/
def fallbackPoint : Point Password Entropy := .b 0 0

/-- A complete sequential trace, with the final chain appended after the adversary. -/
def fromTrace (before chain : List (Point Password Entropy)) : G2.Run (Point Password Entropy) :=
  { queries := before ++ chain
    halt := before.length
    halt_le_length := by simp
    point := fun index => chain.getD index fallbackPoint
    count := chain.length
    complete := by
      intro index within
      have member : chain.getD index fallbackPoint ∈ chain := by
        rw [← List.getElem_eq_getD (h := within) fallbackPoint]
        exact List.getElem_mem within
      exact List.mem_append_right _ member }

/-- Convert the actual execution into the chronological transcript of Lemma G2. -/
def chronologicalRun (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    G2.Run (Point Password Entropy) :=
  let result := outcome password container tables adversary
  fromTrace result.adversaryQueries result.chain

/-- The adapter's complete query list is exactly the actual execution's query list. -/
theorem chronologicalRun_queries (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (chronologicalRun password container tables adversary).queries =
      (execute tables (adversary container)).2 ++
        (execute tables (finalize password 12 container (by omega))).2 := by
  simp only [chronologicalRun, fromTrace, outcome]
  rw [finalize_trace]

/-- The transcript adapter contains all 36 B/A/H chain points. -/
theorem chronologicalRun_count [DecidableEq Password] [DecidableEq Entropy] (password : Password)
    (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (chronologicalRun password container tables adversary).count = 36 := by
  simp only [chronologicalRun, fromTrace, outcome]
  rw [finalize_chain_length]

/-- G2's strict order now applies to the actual typed Gamma2 execution. -/
theorem chronologicalRun_ordered [DecidableEq Password] [DecidableEq Entropy] (password : Password)
    (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ G2.Early (chronologicalRun password container tables adversary)) (index : Nat)
    (positive : 0 < index) (within : index < 36) :
    G2.firstTime (chronologicalRun password container tables adversary) (index - 1) <
      G2.firstTime (chronologicalRun password container tables adversary) index := by
  apply G2.ordered _ notEarly index positive
  simpa only [chronologicalRun_count] using within

noncomputable section

local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

variable [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]

/-- Sample the four independent uniform tables of Appendix A.1. -/
def sampleTables : PMF (Tables Password Entropy) :=
  (PMF.uniformOfFintype (Password × Half → Key)).bind fun a =>
    (PMF.uniformOfFintype (Fin 12 × Half → Half)).bind fun b =>
      (PMF.uniformOfFintype (Key × Fin 12 × Half → Half)).bind fun h =>
        (PMF.uniformOfFintype (Entropy → Hash)).map fun g => ⟨a, b, h, g⟩

/-- Gamma2's full joint law, with an arbitrary independent password distribution. -/
def game (passwords : PMF Password) (adversary : State → OracleComp (spec Password Entropy) Result) :
    PMF (Outcome Password Entropy Result) :=
  passwords.bind fun password =>
    (PMF.uniformOfFintype State).bind fun container =>
      (sampleTables (Password := Password) (Entropy := Entropy)).map fun tables =>
        outcome password container tables adversary

/-- Retain the oracle tables too, so every answer seen by the adversary is determined. -/
def adversaryView (adversary : State → OracleComp (spec Password Entropy) Result) :
    PMF (State × (Tables Password Entropy × (Result × List (Point Password Entropy)))) :=
  (PMF.uniformOfFintype State).bind fun container =>
    (sampleTables (Password := Password) (Entropy := Entropy)).map fun tables =>
      (container, (tables, execute tables (adversary container)))

/-- Gamma2's actual adversary view is independent of the hidden password. -/
theorem password_view_independent (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (game passwords adversary).map
        (fun result => (result.password,
          (result.container, (result.tables, (result.result, result.adversaryQueries))))) =
      ProbabilityTools.independentPair passwords (adversaryView adversary) := by
  simp only [game, adversaryView, ProbabilityTools.independentPair,
    PMF.map_bind, PMF.map_comp, Function.comp_def, outcome]

end

end Gamma2Model

/-!
Query-accounting facts for G3. Counts include repeated queries, hence they are
upper bounds on the numbers of cached distinct points. No probability bound
for the full Early event is asserted by this module.
-/

namespace QueryCounts

open Gamma2Model

variable {Password Entropy : Type}

/-- Whether this query invokes the expensive password function. -/
def isA : Point Password Entropy → Bool
  | .a _ _ => true
  | _ => false

/-- Whether this expensive query uses the specified password. -/
def aFor [DecidableEq Password] (password : Password) : Point Password Entropy → Bool
  | .a candidate _ => decide (candidate = password)
  | _ => false

/-- Salt-oracle queries are partitioned by their public round index. -/
def bFor (round : Fin 12) : Point Password Entropy → Bool
  | .b candidate _ => decide (candidate = round)
  | _ => false

/-- Mask-oracle queries are partitioned by their public round index. -/
def hFor (round : Fin 12) : Point Password Entropy → Bool
  | .h _ candidate _ => decide (candidate = round)
  | _ => false

/-- All salt queries, regardless of round. -/
def isB : Point Password Entropy → Bool
  | .b _ _ => true
  | _ => false

/-- All mask queries, regardless of round. -/
def isH : Point Password Entropy → Bool
  | .h _ _ _ => true
  | _ => false

/-- Each A query contributes once to exactly one password's count. -/
theorem a_partition [Fintype Password] [DecidableEq Password]
    (trace : List (Point Password Entropy)) :
    ∑ password, trace.countP (aFor password) = trace.countP isA := by
  induction trace with
  | nil => simp
  | cons point rest ih =>
    cases point <;>
      simp [aFor, isA, List.countP_cons, Finset.sum_add_distrib, ih]

/-- Each B query contributes once to exactly one round's count. -/
theorem b_partition (trace : List (Point Password Entropy)) :
    ∑ round, trace.countP (bFor round) = trace.countP isB := by
  induction trace with
  | nil => simp
  | cons point rest ih =>
    cases point <;>
      simp [bFor, isB, List.countP_cons, Finset.sum_add_distrib, ih]

/-- Each H query contributes once to exactly one round's count. -/
theorem h_partition (trace : List (Point Password Entropy)) :
    ∑ round, trace.countP (hFor round) = trace.countP isH := by
  induction trace with
  | nil => simp
  | cons point rest ih =>
    cases point <;>
      simp [hFor, isH, List.countP_cons, Finset.sum_add_distrib, ih]

/-- Charge an A query the probability of its password; other queries have no A charge. -/
def weight (probability : Password → ENNReal) : Point Password Entropy → ENNReal
  | .a password _ => probability password
  | _ => 0

/-- The weighted count can equivalently be summed query by query. -/
theorem weighted_counts [Fintype Password] [DecidableEq Password] (probability : Password → ENNReal)
    (trace : List (Point Password Entropy)) :
    ∑ password, probability password * (trace.countP (aFor password) : ENNReal) =
      (trace.map (weight probability)).sum := by
  induction trace with
  | nil => simp
  | cons point rest ih =>
    cases point <;>
      simp [aFor, weight, List.countP_cons, Nat.cast_add, mul_add,
        Finset.sum_add_distrib, ih, mul_ite, add_comm]

/-- Any independent password distribution with point mass at most p1 charges at most p1 per A query. -/
theorem weighted_count_bound [Fintype Password] [DecidableEq Password]
    (probability : Password → ENNReal) (p1 : ENNReal)
    (largest : ∀ password, probability password ≤ p1) (trace : List (Point Password Entropy)) :
    ∑ password, probability password * (trace.countP (aFor password) : ENNReal) ≤
      p1 * (trace.countP isA : ENNReal) := by
  calc
    _ ≤ ∑ password, p1 * (trace.countP (aFor password) : ENNReal) :=
      Finset.sum_le_sum fun password _ => by
        simpa only [mul_comm] using
          mul_le_mul_right (largest password) (trace.countP (aFor password) : ENNReal)
    _ = _ := by rw [← Finset.mul_sum, ← Nat.cast_sum, a_partition]

/-- The deterministic charge bound respects the adversary's A-query budget. -/
theorem budget_bound [Fintype Password] [DecidableEq Password] (probability : Password → ENNReal)
    (p1 : ENNReal) (largest : ∀ password, probability password ≤ p1)
    (trace : List (Point Password Entropy)) (kA : Nat) (budget : trace.countP isA ≤ kA) :
    ∑ password, probability password * (trace.countP (aFor password) : ENNReal) ≤
      p1 * (kA : ENNReal) := by
  exact (weighted_count_bound probability p1 largest trace).trans
    (mul_le_mul_right (by exact_mod_cast budget) p1)

/-- Independence turns the tracewise charge into the expectation used in G3. -/
theorem independent_expected_count [Fintype Password] [DecidableEq Password]
    (passwords : PMF Password) (views : PMF View) (trace : View → List (Point Password Entropy))
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1) (kA : Nat)
    (budget : ∀ view, (trace view).countP isA ≤ kA) :
    (∑' pair : Password × View,
      ProbabilityTools.independentPair passwords views pair *
        ((trace pair.2).countP (aFor pair.1) : ENNReal)) ≤ p1 * (kA : ENNReal) := by
  rw [ENNReal.tsum_prod']
  simp_rw [ProbabilityTools.independentPair_apply]
  rw [ENNReal.tsum_comm]
  calc
    _ = ∑' view, views view *
        (∑ password, passwords password * ((trace view).countP (aFor password) : ENNReal)) := by
      congr 1
      funext view
      rw [tsum_fintype]
      simp [Finset.mul_sum, mul_left_comm, mul_assoc]
    _ ≤ ∑' view, views view * (p1 * (kA : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro view
      exact mul_le_mul_right (budget_bound passwords p1 largest (trace view) kA (budget view)) _
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Private finalization adds 11 + 10 + ... + 0 potential older A points. -/
theorem older_round_count : (∑ round : Fin 12, (11 - round.val)) = 66 := by decide

end QueryCounts

/-!
Finite matching sets for the three transitions in G3. Every set is built from
past query points alone. Repeated queries are deduplicated in the set but remain
counted in the upper bound.
-/

namespace MatchingSets

open Gamma2Model QueryCounts

variable {Password Entropy Answer : Type}

/-- Collect matching answer values from a query history. -/
def values [DecidableEq Answer] (extract : Point Password Entropy → Option Answer)
    (history : List (Point Password Entropy)) : Finset Answer :=
  (history.filterMap extract).toFinset

/-- Extract a salt only from an A query with the specified password. -/
def saltValue [DecidableEq Password] (password : Password) : Point Password Entropy → Option Half
  | .a candidate salt => if candidate = password then some salt else none
  | _ => none

/-- Extract a key only from an H query with the specified round and right half. -/
def keyValue (round : Fin 12) (right : Half) : Point Password Entropy → Option Key
  | .h key candidate half => if candidate = round ∧ half = right then some key else none
  | _ => none

/-- Extract the mask that makes the next B query equal this cached B query. -/
def maskValue (round : Fin 12) (offset : Half) : Point Password Entropy → Option Half
  | .b candidate right => if candidate = round then some (offset ^^^ right) else none
  | _ => none

/-- Deduplication and filtering bound matching values by the appropriate query count. -/
theorem card_bound [DecidableEq Answer] (extract : Point Password Entropy → Option Answer)
    (predicate : Point Password Entropy → Bool) (history : List (Point Password Entropy))
    (only : ∀ point, (extract point).isSome = true → predicate point = true) :
    (values extract history).card ≤ history.countP predicate := by
  calc
    _ ≤ (history.filterMap extract).length := List.toFinset_card_le (history.filterMap extract)
    _ = history.countP (fun point => (extract point).isSome) := List.length_filterMap_eq_countP
    _ ≤ _ := List.countP_mono_left (fun point _ selected => only point selected)

/-- A salt matching the next A query is exactly a cached A point with that password. -/
theorem salt_membership [DecidableEq Password] (password : Password)
    (history : List (Point Password Entropy)) (salt : Half) :
    salt ∈ values (saltValue password) history ↔ .a password salt ∈ history := by
  have extract (point : Point Password Entropy) :
      saltValue password point = some salt ↔ point = .a password salt := by
    cases point with
    | a candidate value =>
      by_cases same : candidate = password <;> simp [saltValue, same]
    | b round right => simp [saltValue]
    | h key round right => simp [saltValue]
    | g entropy => simp [saltValue]
  simp [values, extract]

/-- Matching salts are charged only to A queries with the real password. -/
theorem salt_card [DecidableEq Password] (password : Password)
    (history : List (Point Password Entropy)) :
    (values (saltValue password) history).card ≤ history.countP (aFor password) := by
  classical
  apply card_bound
  intro point found
  cases point <;> aesop (add simp [saltValue, aFor, Option.isSome_none, Bool.false_eq_true])

/-- A key match is exactly the next H point already present in the cache. -/
theorem key_membership (round : Fin 12) (right : Half) (history : List (Point Password Entropy))
    (key : Key) : key ∈ values (keyValue round right) history ↔ .h key round right ∈ history := by
  have extract (point : Point Password Entropy) :
      keyValue round right point = some key ↔ point = .h key round right := by
    cases point with
    | a password salt => simp [keyValue]
    | b candidate half => simp [keyValue]
    | h candidate selected half =>
      by_cases roundEq : selected = round <;> by_cases rightEq : half = right <;>
        simp [keyValue, roundEq, rightEq]
    | g entropy => simp [keyValue]
  simp [values, extract]

/-- Matching keys are charged only to H queries with the next round's index. -/
theorem key_card (round : Fin 12) (right : Half) (history : List (Point Password Entropy)) :
    (values (keyValue round right) history).card ≤ history.countP (hFor round) := by
  classical
  apply card_bound
  intro point found
  cases point <;> aesop (add simp [keyValue, Option.isSome_none, Bool.false_eq_true, hFor])

/-- XOR with a fixed offset is its own inverse. -/
theorem xor_inverse (offset value candidate : Half) :
    offset ^^^ candidate = value ↔ candidate = offset ^^^ value := by
  classical
  aesop

/-- A mask match is exactly the next B point already present in the cache. -/
theorem mask_membership (round : Fin 12) (offset : Half) (history : List (Point Password Entropy))
    (mask : Half) :
    mask ∈ values (maskValue round offset) history ↔ .b round (offset ^^^ mask) ∈ history := by
  have extract (point : Point Password Entropy) :
      maskValue round offset point = some mask ↔ point = .b round (offset ^^^ mask) := by
    cases point with
    | a password salt => simp [maskValue]
    | b candidate right =>
      by_cases same : candidate = round <;> simp [maskValue, same, xor_inverse]
    | h key candidate right => simp [maskValue]
    | g entropy => simp [maskValue]
  simp [values, extract]

/-- Matching masks are charged only to B queries with the next round's index. -/
theorem mask_card (round : Fin 12) (offset : Half) (history : List (Point Password Entropy)) :
    (values (maskValue round offset) history).card ≤ history.countP (bFor round) := by
  classical
  apply card_bound
  intro point found
  cases point <;> aesop (add simp [maskValue, Option.isSome_none, Bool.false_eq_true, bFor])

end MatchingSets

/-!
A ghost observer of a dependent oracle chain. It uses only answers obtained by
actual queries, stops before the requested chain answer, and stops without a hit
if a later point was already cached. It has no direct access to random tables.
-/

namespace ChainMonitor

open Gamma2Model

variable {Password Entropy Node Result : Type}

/-- A chain state determines its current query and the next state after its answer. -/
structure Machine (Password Entropy Node : Type) where
  point : Node → Point Password Entropy
  next : (node : Node) → spec Password Entropy (point node) → Option Node

variable [DecidableEq Password] [DecidableEq Entropy]

/-- Follow actual queries and stop immediately before a fresh selected chain answer. -/
def monitor (machine : Machine Password Entropy Node) (target : Node → Bool)
    (program : OracleComp (spec Password Entropy) Result) :
    Option Node → List (Point Password Entropy) →
      OracleComp (spec Password Entropy) (Option (Node × List (Point Password Entropy))) :=
  OracleComp.construct
    (fun _ _ _ => pure none)
    (fun queried _ recurse pending past =>
      match pending with
      | none => pure none
      | some node =>
        if machine.point node ∈ past then pure none
        else if target node = true ∧ queried = machine.point node then pure (some (node, past))
        else do
          let value ← ask queried
          let pending' := if equal : queried = machine.point node
            then machine.next node (equal ▸ value) else some node
          recurse value pending' (past ++ [queried])) program

@[simp] theorem monitor_pure (machine : Machine Password Entropy Node) (target : Node → Bool)
    (result : Result) (pending : Option Node) (past : List (Point Password Entropy)) :
    monitor machine target (pure result) pending past = pure none := rfl

/-- Unfold one observed query while leaving its continuation abstract. -/
theorem monitor_query (machine : Machine Password Entropy Node) (target : Node → Bool)
    (queried : Point Password Entropy)
    (next : spec Password Entropy queried → OracleComp (spec Password Entropy) Result)
    (pending : Option Node) (past : List (Point Password Entropy)) :
    monitor machine target (ask queried >>= next) pending past =
      (match pending with
      | none => pure none
      | some node =>
        if machine.point node ∈ past then pure none
        else if target node = true ∧ queried = machine.point node then pure (some (node, past))
        else do
          let value ← ask queried
          let pending' := if equal : queried = machine.point node
            then machine.next node (equal ▸ value) else some node
          monitor machine target (next value) pending' (past ++ [queried])) := rfl

/-- A returned hit retains precisely the prior trace and an unqueried target point. -/
theorem information (machine : Machine Password Entropy Node) (target : Node → Bool)
    (tables : Tables Password Entropy) (program : OracleComp (spec Password Entropy) Result)
    (pending : Option Node) (past : List (Point Password Entropy)) (chosen : Node)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor machine target program pending past)).1 = some (chosen, history)) :
    history = past ++ (execute tables (monitor machine target program pending past)).2 ∧
      machine.point chosen ∉ history ∧ target chosen = true := by
  induction program using OracleComp.inductionOn generalizing pending past with
  | pure result => simp only [monitor_pure, execute_pure] at hit; cases hit
  | query_bind queried next ih =>
    change (execute tables (monitor machine target (ask queried >>= next) pending past)).1 = _ at hit
    rw [monitor_query] at hit
    cases pending with
    | none => simp only [execute_pure] at hit; cases hit
    | some node =>
      dsimp only at hit
      by_cases cached : machine.point node ∈ past
      · rw [if_pos cached] at hit
        cases hit
      · rw [if_neg cached] at hit
        by_cases stop : target node = true ∧ queried = machine.point node
        · rw [if_pos stop] at hit
          have equal := Option.some.inj hit
          cases equal
          refine ⟨?_, cached, stop.1⟩
          change history = history ++ (execute tables
            (monitor machine target (ask queried >>= next) (some chosen) history)).2
          rw [monitor_query]
          dsimp only
          rw [if_neg cached, if_pos stop]
          simp only [execute_pure, List.append_nil]
        · rw [if_neg stop] at hit
          simp only [execute_bind, execute_ask, List.singleton_append] at hit
          let pending' := if equal : queried = machine.point node
            then machine.next node (equal ▸ answer tables queried) else some node
          have remaining := ih (answer tables queried) pending' (past ++ [queried]) hit
          rcases remaining with ⟨same, fresh, selected⟩
          refine ⟨?_, fresh, selected⟩
          change history = past ++ (execute tables
            (monitor machine target (ask queried >>= next) (some node) past)).2
          rw [monitor_query]
          dsimp only
          rw [if_neg cached, if_neg stop]
          simp only [execute_bind, execute_ask, List.singleton_append]
          simpa only [List.append_assoc, List.singleton_append] using same

/-- A hit is at a real query in the original execution, not an extra observer query. -/
theorem trace_prefix (machine : Machine Password Entropy Node) (target : Node → Bool)
    (tables : Tables Password Entropy) (program : OracleComp (spec Password Entropy) Result)
    (pending : Option Node) (past : List (Point Password Entropy)) (chosen : Node)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor machine target program pending past)).1 = some (chosen, history)) :
    ∃ later, (execute tables program).2 =
      (execute tables (monitor machine target program pending past)).2 ++
        machine.point chosen :: later := by
  induction program using OracleComp.inductionOn generalizing pending past with
  | pure result => simp only [monitor_pure, execute_pure] at hit; cases hit
  | query_bind queried next ih =>
    change (execute tables (monitor machine target (ask queried >>= next) pending past)).1 = _ at hit
    rw [monitor_query] at hit
    cases pending with
    | none => simp only [execute_pure] at hit; cases hit
    | some node =>
      dsimp only at hit
      by_cases cached : machine.point node ∈ past
      · rw [if_pos cached] at hit
        cases hit
      · rw [if_neg cached] at hit
        by_cases stop : target node = true ∧ queried = machine.point node
        · rw [if_pos stop] at hit
          have equal := Option.some.inj hit
          cases equal
          refine ⟨(execute tables (next (answer tables queried))).2, ?_⟩
          change (execute tables (ask queried >>= next)).2 =
            (execute tables (monitor machine target (ask queried >>= next) (some chosen) history)).2 ++
              machine.point chosen :: _
          rw [monitor_query]
          dsimp only
          rw [if_neg cached, if_pos stop]
          simp only [execute_pure, execute_bind, execute_ask,
            List.singleton_append, List.nil_append]
          exact congrArg
            (fun point => point :: (execute tables (next (answer tables queried))).2) stop.2
        · rw [if_neg stop] at hit
          simp only [execute_bind, execute_ask, List.singleton_append] at hit
          let pending' := if equal : queried = machine.point node
            then machine.next node (equal ▸ answer tables queried) else some node
          obtain ⟨later, remaining⟩ := ih (answer tables queried) pending' (past ++ [queried]) hit
          refine ⟨later, ?_⟩
          change (execute tables (ask queried >>= next)).2 =
            (execute tables (monitor machine target (ask queried >>= next) (some node) past)).2 ++
              machine.point chosen :: _
          rw [monitor_query]
          dsimp only
          rw [if_neg cached, if_neg stop]
          simp only [execute_bind, execute_ask, List.singleton_append]
          rw [remaining]
          rfl

end ChainMonitor

/-!
Concrete inverse-round chain states for the Gamma2 observer. The next chain
point is obtained only from the current query's answer. There are 36 stages.
-/

namespace MhfeChain

open Gamma2Model ChainMonitor

/-- The three query phases retain exactly the Feistel data needed by the next query. -/
inductive Cursor
  | salt (round : Fin 12) (state : State)
  | key (round : Fin 12) (state : State) (salt : Half)
  | mask (round : Fin 12) (state : State) (key : Key)

/-- The source chain's B, A, H point at the current phase. -/
def point (password : Password) : Cursor → Point Password Entropy
  | .salt round state => .b round state.1
  | .key _ _ salt => .a password salt
  | .mask round state key => .h key round state.1

/-- Advance the current query using its typed answer; round 0's mask ends the chain. -/
def advance (password : Password) :
    (cursor : Cursor) → spec Password Entropy (point password cursor) → Option Cursor
  | .salt round state, salt => some (.key round state salt)
  | .key round state _, key => some (.mask round state key)
  | .mask round state _, mask =>
    if positive : 0 < round.val then
      some (.salt ⟨round.val - 1, by omega⟩ (BitVec.xor state.2 mask, state.1))
    else none

/-- The concrete machine used by the ghost observer. -/
def machine (password : Password) : Machine Password Entropy Cursor :=
  ⟨point password, advance password⟩

/-- Zero-based position among the 36 points of the inverse chain. -/
def stage : Cursor → Nat
  | .salt round _ => 3 * (11 - round.val)
  | .key round _ _ => 3 * (11 - round.val) + 1
  | .mask round _ _ => 3 * (11 - round.val) + 2

/-- Every concrete cursor names one of the source chain's 36 stages. -/
theorem stage_bound (cursor : Cursor) : stage cursor < 36 := by
  cases cursor <;> simp only [stage]
  all_goals have bounded := Fin.isLt ‹Fin 12›; omega

/-- Nonterminal transitions move forward by exactly one source-chain point. -/
theorem advance_stage (password : Password) (cursor next : Cursor)
    (value : spec Password Entropy (point password cursor))
    (stepped : advance password cursor value = some next) : stage next = stage cursor + 1 := by
  cases cursor with
  | salt round state =>
    simp only [advance, Option.some.injEq] at stepped
    subst next
    rfl
  | key round state salt =>
    simp only [advance, Option.some.injEq] at stepped
    subst next
    simp only [stage]
  | mask round state key =>
    simp only [advance] at stepped
    split at stepped
    · have equal := Option.some.inj stepped
      subst next
      simp only [stage]
      have bounded := round.isLt
      omega
    · cases stepped

/-- A chain ends only at the mask of round zero, its stage 35. -/
theorem advance_terminal (password : Password) (cursor : Cursor)
    (value : spec Password Entropy (point password cursor))
    (finished : advance password cursor value = none) : stage cursor = 35 := by
  classical
  aesop (add simp [advance, stage])

/-- Materialize a chain using the same fixed tables as the actual execution. -/
def walk (password : Password) (tables : Tables Password Entropy) : Nat → Cursor → List Cursor
  | 0, _ => []
  | fuel + 1, cursor =>
    cursor :: match advance password cursor (answer tables (point password cursor)) with
      | none => []
      | some next => walk password tables fuel next

/-- The concrete machine's chain is precisely the chain returned by actual inverse rounds. -/
theorem walk_matches_finalize (password : Password) (tables : Tables Password Entropy)
    (round : Nat) (bounded : round < 12) (state : State) :
    (walk password tables (3 * (round + 1)) (.salt ⟨round, bounded⟩ state)).map (point password) =
      (execute tables (finalize password (round + 1) state (by omega))).1.2 := by
  induction round generalizing state with
  | zero => rfl
  | succ round ih =>
    have fuel : 3 * (round + 1 + 1) = 3 * (round + 1) + 3 := by omega
    rw [fuel]
    simp only [walk, advance, answer, point, Nat.succ_pos, dif_pos, Nat.add_sub_cancel,
      List.map_cons, finalize, execute_bind, execute_ask, execute_ask_a, execute_ask_b,
      execute_ask_h, execute_pure, List.cons_append, List.nil_append, List.append_nil]
    rw [ih (by omega)]
    simp only [finalize, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h,
      execute_pure, answer, BitVec.xor_eq, List.cons_append, List.nil_append, List.append_nil]

/-- Starting at round 11 produces exactly the 36 points used in Gamma2Model. -/
theorem full_chain (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (walk password tables 36 (.salt 11 container)).map (point password) =
      (outcome password container tables adversary).chain := by
  have chain := walk_matches_finalize password tables 11 (by omega) container
  rw [show (⟨11, by omega⟩ : Fin 12) = 11 from rfl] at chain
  simp only [Nat.reduceMul, Nat.reduceAdd] at chain
  simp only [outcome]
  rw [chain]

end MhfeChain

/-!
Proof-only replay of an already fixed query transcript. It is not the selection
program used by the fresh-sampling theorem. Equality with the causal observer
lets subsequent deterministic coverage proofs use list induction.
-/

namespace MonitorScan

open Gamma2Model ChainMonitor

variable {Password Entropy Node Result : Type}
  [DecidableEq Password] [DecidableEq Entropy]

/-- Replay the observer from actual queried points and their consistent table answers. -/
def scan (machine : Machine Password Entropy Node) (target : Node → Bool)
    (tables : Tables Password Entropy) :
    List (Point Password Entropy) → Option Node → List (Point Password Entropy) →
      Option (Node × List (Point Password Entropy))
  | [], _, _ => none
  | queried :: remaining, pending, past =>
    match pending with
    | none => none
    | some node =>
      if machine.point node ∈ past then none
      else if target node = true ∧ queried = machine.point node then some (node, past)
      else
        let value := answer tables queried
        let pending' := if equal : queried = machine.point node
          then machine.next node (equal ▸ value) else some node
        scan machine target tables remaining pending' (past ++ [queried])

/-- Replaying the fixed actual log returns exactly the causal observer's selected result. -/
theorem monitor_scans (machine : Machine Password Entropy Node) (target : Node → Bool)
    (tables : Tables Password Entropy) (program : OracleComp (spec Password Entropy) Result)
    (pending : Option Node) (past : List (Point Password Entropy)) :
    (execute tables (monitor machine target program pending past)).1 =
      scan machine target tables (execute tables program).2 pending past := by
  induction program using OracleComp.inductionOn generalizing pending past with
  | pure result => rfl
  | query_bind queried next ih =>
    change (execute tables (monitor machine target (ask queried >>= next) pending past)).1 =
      scan machine target tables (execute tables (ask queried >>= next)).2 pending past
    rw [monitor_query]
    simp only [execute_bind, execute_ask, List.singleton_append, scan]
    cases pending with
    | none => rfl
    | some node =>
      dsimp only
      by_cases cached : machine.point node ∈ past
      · simp only [if_pos cached, execute_pure]
      · simp only [if_neg cached]
        by_cases stop : target node = true ∧ queried = machine.point node
        · simp only [if_pos stop, execute_pure]
        · simp only [if_neg stop, execute_bind, execute_ask, List.singleton_append]
          exact ih (answer tables queried) _ _

end MonitorScan

/-!
Coverage of a target whose chain prefix has ordered first queries. These are
pure list facts about the proof-only scan. Their application to the original
program uses monitor_scans; the scan is never passed to fresh sampling.
-/

namespace ScanCoverage

open Gamma2Model ChainMonitor MonitorScan

variable {Password Entropy Node : Type} [DecidableEq Password] [DecidableEq Entropy]

/-- Adjacent cursors follow the machine's actual table answer. -/
def Follows (machine : Machine Password Entropy Node) (tables : Tables Password Entropy) :
    List Node → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
    machine.next first (answer tables (machine.point first)) = some second ∧
      Follows machine tables (second :: remaining)

/-- Removing a query unrelated to all remaining nodes preserves their coverage invariants. -/
theorem skip_data (machine : Machine Password Entropy Node) (queried : Point Password Entropy)
    (remaining past : List (Point Password Entropy)) (nodes : List Node)
    (different : ∀ node ∈ nodes, queried ≠ machine.point node)
    (present : ∀ node ∈ nodes, machine.point node ∈ queried :: remaining)
    (ordered : nodes.Pairwise (fun a b => (queried :: remaining).idxOf (machine.point a) < (queried :: remaining).idxOf (machine.point b)))
    (fresh : ∀ node ∈ nodes, machine.point node ∉ past) :
    (∀ node ∈ nodes, machine.point node ∈ remaining) ∧
      nodes.Pairwise (fun a b => remaining.idxOf (machine.point a) <
        remaining.idxOf (machine.point b)) ∧
      (∀ node ∈ nodes, machine.point node ∉ past ++ [queried]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro node member
    have found := present node member
    exact (List.mem_cons.mp found).resolve_left (Ne.symm (different node member))
  · apply ordered.imp_of_mem
    intro a b memberA memberB before
    simpa [List.idxOf_cons, different a memberA, different b memberB] using before
  · intro node member found
    rcases List.mem_append.mp found with old | newest
    · exact fresh node member old
    · have equal : machine.point node = queried := List.mem_singleton.mp newest
      exact different node member equal.symm

/-- A later node cannot be the first query of a strictly ordered prefix. -/
theorem head_query_distinct (machine : Machine Password Entropy Node)
    (queried : Point Password Entropy) (remaining : List (Point Password Entropy)) (first : Node)
    (later : List Node)
    (ordered : (first :: later).Pairwise (fun a b => (queried :: remaining).idxOf (machine.point a) < (queried :: remaining).idxOf (machine.point b))) :
    ∀ node ∈ later, queried ≠ machine.point node := by
  intro node member equal
  have before := List.rel_of_pairwise_cons ordered member
  rw [← equal] at before
  simp only [List.idxOf_cons_self] at before
  omega

/-- An ordered, complete, fresh path forces the scan to select its requested target. -/
theorem target_covered (machine : Machine Password Entropy Node) (target : Node → Bool)
    (tables : Tables Password Entropy) (queries past : List (Point Password Entropy))
    (nodes : List Node) (selected : Node)
    (member : selected ∈ nodes)
    (selectedTarget : target selected = true)
    (onlyTarget : ∀ node ∈ nodes, target node = true → node = selected)
    (follows : Follows machine tables nodes)
    (present : ∀ node ∈ nodes, machine.point node ∈ queries)
    (ordered : nodes.Pairwise (fun a b => queries.idxOf (machine.point a) <
      queries.idxOf (machine.point b)))
    (fresh : ∀ node ∈ nodes, machine.point node ∉ past) :
    ∃ history, scan machine target tables queries (some (nodes.head (by
      intro empty
      rw [empty] at member
      cases member))) past =
      some (selected, history) := by
  induction queries generalizing nodes past with
  | nil =>
    have impossible := present selected member
    cases impossible
  | cons queried remaining ih =>
    cases nodes with
    | nil => cases member
    | cons first later =>
      have uncached := fresh first (List.mem_cons_self ..)
      have tailDifferent := head_query_distinct machine queried remaining first later ordered
      by_cases sameQuery : queried = machine.point first
      · by_cases selectedNow : target first = true
        · have equal := onlyTarget first (List.mem_cons_self ..) selectedNow
          subst selected
          refine ⟨past, ?_⟩
          change scan _ _ _ _ (some first) _ = _
          simp only [scan, if_neg uncached,
            if_pos (And.intro selectedNow sameQuery)]
        · have selectedLater : selected ∈ later :=
            (List.mem_cons.mp member).resolve_left (by
              intro equal; apply selectedNow; simpa only [← equal] using selectedTarget)
          have tailNotEmpty : later ≠ [] := by
            intro empty
            rw [empty] at selectedLater
            cases selectedLater
          obtain ⟨tailPresent, tailOrdered, tailFresh⟩ :=
            skip_data machine queried remaining past later tailDifferent
              (fun node found => present node (List.mem_cons_of_mem first found))
              ordered.of_cons (fun node found => fresh node (List.mem_cons_of_mem first found))
          have step : machine.next first (answer tables (machine.point first)) =
              some (later.head tailNotEmpty) ∧ Follows machine tables later := by
            cases later with
            | nil => exact False.elim (tailNotEmpty rfl)
            | cons second rest => exact follows
          obtain ⟨history, covered⟩ := ih (past ++ [queried]) later selectedLater
            (fun node found => onlyTarget node (List.mem_cons_of_mem first found))
            step.2 tailPresent tailOrdered tailFresh
          refine ⟨history, ?_⟩
          change scan _ _ _ _ (some first) _ = _
          simp only [scan, if_neg uncached,
            if_neg (show ¬ (target first = true ∧ queried = machine.point first) from
              fun both => selectedNow both.1)]
          subst queried
          simp only [dite_true]
          rw [step.1]
          exact covered
      · have allDifferent : ∀ node ∈ first :: later, queried ≠ machine.point node := by
          intro node found
          rcases List.mem_cons.mp found with equal | tailMember
          · simpa only [equal] using sameQuery
          · exact tailDifferent node tailMember
        obtain ⟨remainingPresent, remainingOrdered, remainingFresh⟩ :=
          skip_data machine queried remaining past (first :: later) allDifferent present ordered fresh
        obtain ⟨history, covered⟩ := ih (past ++ [queried]) (first :: later) member onlyTarget
          follows remainingPresent remainingOrdered remainingFresh
        refine ⟨history, ?_⟩
        change scan _ _ _ _ (some first) _ = _
        simp only [scan, if_neg uncached,
          if_neg (show ¬ (target first = true ∧ queried = machine.point first) from
            fun both => sameQuery both.2), dif_neg sameQuery]
        exact covered

end ScanCoverage

/-! Structural facts for instantiating scan coverage on the actual inverse chain. -/

namespace WalkProperties

variable {Password Entropy Node Result : Type}

open Gamma2Model ChainMonitor ScanCoverage MhfeChain

/-- Taking a chain prefix preserves its consecutive machine transitions. -/
theorem follows_take (machine : Machine Password Entropy Node) (tables : Tables Password Entropy)
    (nodes : List Node) (follows : Follows machine tables nodes) (count : Nat) :
    Follows machine tables (nodes.take count) := by
  induction count generalizing nodes with
  | zero => trivial
  | succ count ih =>
    cases nodes with
    | nil => trivial
    | cons first later =>
      cases count with
      | zero => trivial
      | succ previous =>
        cases later with
        | nil => trivial
        | cons second remaining =>
          exact ⟨follows.1, ih (second :: remaining) follows.2⟩

/-- Materialization follows exactly the concrete machine's answer-dependent transitions. -/
theorem walk_follows (password : Password) (tables : Tables Password Entropy) (fuel : Nat)
    (cursor : Cursor) : Follows (machine password) tables (walk password tables fuel cursor) := by
  induction fuel generalizing cursor with
  | zero => trivial
  | succ fuel ih =>
    rw [walk]
    cases stepped : advance password cursor (answer tables (point password cursor)) with
    | none => trivial
    | some next =>
      cases fuel with
      | zero => trivial
      | succ previous =>
        change advance password cursor (answer tables (point password cursor)) = some next ∧
          Follows (machine password) tables (walk password tables (previous + 1) next)
        exact ⟨stepped, ih next⟩

/-- The stage of an in-range materialized cursor is its starting stage plus its list index. -/
theorem walk_stage_at (password : Password) (tables : Tables Password Entropy) (fuel : Nat)
    (cursor : Cursor) (index : Nat) (within : index < (walk password tables fuel cursor).length) :
    stage (walk password tables fuel cursor)[index] = stage cursor + index := by
  induction fuel generalizing cursor index with
  | zero => simp only [walk, List.length_nil] at within; omega
  | succ fuel ih =>
    cases index with
    | zero => rfl
    | succ index =>
      cases stepped : advance password cursor (answer tables (point password cursor)) with
      | none =>
        simp only [walk, stepped, List.length_cons, List.length_nil] at within
        omega
      | some next =>
        simp only [walk, stepped, List.length_cons] at within
        simp only [walk, stepped, List.getElem_cons_succ]
        rw [ih next index (by omega)]
        have oneStep := advance_stage password cursor next
          (answer tables (point password cursor)) stepped
        omega

/-- The full cursor list has the same length 36 as the actual point chain. -/
theorem full_walk_length (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (walk password tables 36 (.salt 11 container)).length = 36 := by
  have same := congrArg List.length (full_chain password container tables adversary)
  simp only [List.length_map] at same
  rw [same]
  simp only [outcome]
  rw [finalize_chain_length]

/-- The full inverse walk starts at stage zero, so each cursor's stage equals its index. -/
theorem full_stage_at (password : Password) (container : State) (tables : Tables Password Entropy)
    (index : Nat) (within : index < (walk password tables 36 (.salt 11 container)).length) :
    stage (walk password tables 36 (.salt 11 container))[index] = index := by
  have initial : stage (.salt 11 container) = 0 := rfl
  simpa only [initial, Nat.zero_add] using
    walk_stage_at password tables 36 (.salt 11 container) index within

end WalkProperties

/-!
The local chronological facts needed at the first Early point. Global no-Early
order (G2.ordered) cannot be assumed on this event. Adjacent point identity must
include the oracle type; a repeated adjacent point would invalidate strictness.
-/

namespace FirstEarly

open G2

variable {Point : Type} [DecidableEq Point]

/-- An Early point with no earlier positive-index Early point. -/
def First (run : Run Point) (index : Nat) : Prop :=
  0 < index ∧ index < run.count ∧ firstTime run index < definedTime run index ∧
    ∀ previous, 0 < previous → previous < index →
      definedTime run previous ≤ firstTime run previous

/-- Every Early execution has a first such point; no total chain order is presumed. -/
theorem exists_first (run : Run Point) (early : Early run) : ∃ index, First run index := by
  classical
  have any : ∃ index, 0 < index ∧ index < run.count ∧
      firstTime run index < definedTime run index := early
  let index := Nat.find any
  have chosen := Nat.find_spec any
  refine ⟨index, chosen.1, chosen.2.1, chosen.2.2, ?_⟩
  intro previous positive before
  have excluded := Nat.find_min any before
  have within : previous < run.count := Nat.lt_trans before chosen.2.1
  change ¬ (0 < previous ∧ previous < run.count ∧
    firstTime run previous < definedTime run previous) at excluded
  omega

/-- Earlier chain points have strict first-query order before the first failure. -/
theorem prefix_ordered (run : Run Point) (index : Nat) (first : First run index) (previous : Nat)
    (positive : 0 < previous) (before : previous < index) :
    firstTime run (previous - 1) < firstTime run previous := by
  have fresh := first.2.2.2 previous positive before
  cases previous with
  | zero => omega
  | succ earlier =>
    have afterAnswer : firstTime run earlier + 1 ≤ definedTime run (earlier + 1) :=
      Nat.le_max_right _ _
    simp only [Nat.add_sub_cancel] at *
    omega

/-- At the first failure, definition occurs immediately after the predecessor's first answer. -/
theorem defined_after_previous (run : Run Point) (index : Nat) (first : First run index) :
    definedTime run index = firstTime run (index - 1) + 1 := by
  cases index with
  | zero => exact False.elim (by have positive := first.1; omega)
  | succ previous =>
    simp only [definedTime, Nat.add_sub_cancel]
    apply Nat.max_eq_right
    by_cases zero : previous = 0
    · subst previous
      simp only [definedTime]
      omega
    · have fresh := first.2.2.2 previous (by omega) (by omega)
      omega

/-- Distinct adjacent typed points make the early query strictly earlier than its predecessor. -/
theorem queried_before_previous (run : Run Point) (index : Nat) (first : First run index)
    (distinct : run.point index ≠ run.point (index - 1)) :
    firstTime run index < firstTime run (index - 1) := by
  have failure := first.2.2.1
  rw [defined_after_previous run index first] at failure
  have different : firstTime run index ≠ firstTime run (index - 1) := by
    intro equal
    apply distinct
    exact (List.idxOf_inj (run.complete index first.2.1)).mp equal
  omega

end FirstEarly

/-!
Instantiate the causal observer on the actual adversary-plus-finalization
program. Only the prefix preceding the first Early is assumed ordered.
-/

namespace MhfeMonitorCoverage

open Gamma2Model MhfeChain WalkProperties
open ChainMonitor MonitorScan ScanCoverage G2

variable {Password Entropy Result : Type}

/-- The actual adversary followed by private inverse-chain finalization. -/
def fullProgram (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Password Entropy) Unit := do
  let _ ← adversary container
  let _ ← finalize password 12 container (by omega)
  pure ()

/-- The observer's program has precisely the chronological run's complete query trace. -/
theorem fullProgram_trace (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (execute tables (fullProgram password container adversary)).2 =
      (chronologicalRun password container tables adversary).queries := by
  rw [chronologicalRun_queries]
  simp only [fullProgram, execute_bind, execute_pure, List.append_nil]

/-- In-range chronological chain points agree with the concrete cursor list. -/
theorem chronological_point (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (index : Nat)
    (within : index < (walk password tables 36 (.salt 11 container)).length) :
    (chronologicalRun password container tables adversary).point index =
      point password (walk password tables 36 (.salt 11 container))[index] := by
  simp only [chronologicalRun, fromTrace]
  rw [← full_chain password container tables adversary]
  rw [← List.getElem_eq_getD (h := by simpa only [List.length_map] using within) fallbackPoint]
  simp only [List.getElem_map]

/-- Cursor stages uniquely identify nodes occurring in the materialized chain. -/
theorem full_stage_injective (password : Password) (container : State)
    (tables : Tables Password Entropy) (left right : Cursor)
    (leftMember : left ∈ walk password tables 36 (.salt 11 container))
    (rightMember : right ∈ walk password tables 36 (.salt 11 container))
    (sameStage : stage left = stage right) : left = right := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem leftMember
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem rightMember
  have hi' := full_stage_at password container tables i hi
  have hj' := full_stage_at password container tables j hj
  obtain rfl : i = j := by omega
  rfl

/-- Strict adjacent order before FirstEarly extends to any two points of that prefix. -/
theorem prefix_all_ordered {TracePoint : Type} [DecidableEq TracePoint] (run : Run TracePoint)
    (index : Nat) (first : FirstEarly.First run index) (earlier later : Nat)
    (before : earlier < later) (within : later < index) :
    firstTime run earlier < firstTime run later := by
  induction later generalizing earlier with
  | zero => omega
  | succ previous ih =>
    have adjacent := FirstEarly.prefix_ordered run index first
      (previous + 1) (by omega) within
    by_cases equal : earlier = previous
    · simpa only [equal, Nat.add_sub_cancel] using adjacent
    · have ordered := ih earlier (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at adjacent
      omega

/-- Before FirstEarly, the actual monitor necessarily selects the predecessor's stage. -/
theorem firstEarly_target_covered [DecidableEq Password] [DecidableEq Entropy] (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (index : Nat)
    (first : FirstEarly.First (chronologicalRun password container tables adversary) index) :
    ∃ history,
      (execute tables (monitor (machine password) (fun cursor => decide (stage cursor = index - 1))
        (fullProgram password container adversary) (some (.salt 11 container)) [])).1 =
          some ((walk password tables 36 (.salt 11 container))[index - 1]'(by
            rw [full_walk_length password container tables adversary]
            have bounded := first.2.1
            rw [chronologicalRun_count] at bounded
            omega), history) := by
  let nodes := walk password tables 36 (.salt 11 container)
  have size : nodes.length = 36 := full_walk_length password container tables adversary
  have positive := first.1
  have indexBound : index < 36 := by
    simpa only [chronologicalRun_count] using first.2.1
  have selectedWithin : index - 1 < nodes.length := by omega
  let selected := nodes[index - 1]'selectedWithin
  let target := fun cursor => decide (stage cursor = index - 1)
  have selectedStage : stage selected = index - 1 :=
    full_stage_at password container tables (index - 1) selectedWithin
  have prefixSize : (nodes.take index).length = index := by
    rw [List.length_take, size]
    omega
  have selectedMember : selected ∈ nodes.take index := by
    have withinPrefix : index - 1 < (nodes.take index).length := by omega
    have found := List.getElem_mem withinPrefix
    simpa only [List.getElem_take] using found
  have targetSelected : target selected = true := by
    simp only [target, selectedStage, decide_true]
  have targetOnly : ∀ cursor ∈ nodes.take index, target cursor = true → cursor = selected := by
    intro cursor found marked
    apply full_stage_injective password container tables cursor selected
      (List.take_subset index nodes found) (List.getElem_mem selectedWithin)
    have cursorStage : stage cursor = index - 1 := of_decide_eq_true marked
    exact cursorStage.trans selectedStage.symm
  have present : ∀ cursor ∈ nodes.take index,
      (machine password).point cursor ∈ (execute tables (fullProgram password container adversary)).2 := by
    intro cursor found
    have inChain : point password cursor ∈ (outcome password container tables adversary).chain := by
      rw [← full_chain password container tables adversary]
      exact List.mem_map.mpr ⟨cursor, List.take_subset index nodes found, rfl⟩
    rw [fullProgram_trace]
    change point password cursor ∈
      (outcome password container tables adversary).adversaryQueries ++
        (outcome password container tables adversary).chain
    exact List.mem_append_right _ inChain
  have ordered : (nodes.take index).Pairwise (fun a b =>
      (execute tables (fullProgram password container adversary)).2.idxOf ((machine password).point a) <
        (execute tables (fullProgram password container adversary)).2.idxOf ((machine password).point b)) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj before
    have hiNodes : i < nodes.length := Nat.lt_of_lt_of_le hi (List.length_take_le' ..)
    have hjNodes : j < nodes.length := Nat.lt_of_lt_of_le hj (List.length_take_le' ..)
    have hjIndex : j < index := by omega
    simp only [List.getElem_take]
    change (execute tables (fullProgram password container adversary)).2.idxOf (point password nodes[i]) <
      (execute tables (fullProgram password container adversary)).2.idxOf (point password nodes[j])
    rw [← chronological_point password container tables adversary i hiNodes,
      ← chronological_point password container tables adversary j hjNodes, fullProgram_trace]
    exact prefix_all_ordered _ index first i j before hjIndex
  obtain ⟨history, covered⟩ := target_covered (machine password) target tables
    (execute tables (fullProgram password container adversary)).2 []
    (nodes.take index) selected selectedMember targetSelected targetOnly
    (follows_take (machine password) tables nodes (walk_follows password tables 36 _) index)
    present ordered (by intro cursor _; simp only [List.not_mem_nil, not_false_eq_true])
  refine ⟨history, ?_⟩
  have head : (nodes.take index).head (by intro empty; rw [empty] at selectedMember; cases selectedMember) =
      .salt 11 container := by
    cases index with
    | zero => omega
    | succ previous => rfl
  rw [head, ← monitor_scans] at covered
  exact covered

end MhfeMonitorCoverage

/-!
Private-query accounting uses only oracle family and public round number.
Erasing keys, salts and Feistel state avoids any distinct-salt premise.
-/

namespace ChainMetadata

open Gamma2Model QueryCounts

variable {Password Entropy Result : Type}

/-- The public query label needed for G3's private-prefix accounting. -/
inductive Label
  | a
  | b (round : Nat)
  | h (round : Nat)
  | g
  deriving DecidableEq

/-- Erase every secret-dependent argument from a query point. -/
def label : Point Password Entropy → Label
  | .a _ _ => .a
  | .b round _ => .b round.val
  | .h _ round _ => .h round.val
  | .g _ => .g

/-- A public sequence of B/A/H labels for inverse rounds fuel-1 down to zero. -/
def inverseLabels : Nat → List Label
  | 0 => []
  | fuel + 1 => [.b fuel, .a, .h fuel] ++ inverseLabels fuel

/-- Whether a public label denotes an expensive A query. -/
def isLabelA : Label → Bool
  | .a => true
  | _ => false

/-- Whether a public label denotes B at a specified index. -/
def isLabelB (round : Nat) : Label → Bool
  | .b candidate => decide (candidate = round)
  | _ => false

/-- Whether a public label denotes H at a specified index. -/
def isLabelH (round : Nat) : Label → Bool
  | .h candidate => decide (candidate = round)
  | _ => false

/-- The actual private finalization has exactly the public inverse-label sequence. -/
theorem finalize_labels (tables : Tables Password Entropy) (password : Password) (fuel : Nat)
    (state : State) (bounded : fuel ≤ 12) :
    ((execute tables (finalize password fuel state bounded)).1.2).map label = inverseLabels fuel := by
  classical
  induction fuel generalizing state <;> aesop (add simp [finalize, execute_bind, execute_ask,
    execute_pure, answer, List.cons_append, List.nil_append, List.append_nil, List.map_cons, label,
    inverseLabels])

/-- The full actual chain's labels carry no table- or password-dependent data. -/
theorem full_labels (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (outcome password container tables adversary).chain.map label = inverseLabels 12 := by
  simpa only [outcome] using finalize_labels tables password 12 container (by omega)

/-- Label erasure preserves the total A-query count. -/
theorem count_a (history : List (Point Password Entropy)) :
    (history.map label).countP isLabelA = history.countP isA := by
  rw [List.countP_map]
  congr 1
  funext point
  cases point <;> rfl

/-- Label erasure preserves B-query counts by round. -/
theorem count_b (round : Fin 12) (history : List (Point Password Entropy)) :
    (history.map label).countP (isLabelB round.val) = history.countP (bFor round) := by
  rw [List.countP_map]
  congr 1
  funext point
  cases point <;> simp [label, isLabelB, bFor, Fin.ext_iff]

/-- Label erasure preserves H-query counts by round. -/
theorem count_h (round : Fin 12) (history : List (Point Password Entropy)) :
    (history.map label).countP (isLabelH round.val) = history.countP (hFor round) := by
  rw [List.countP_map]
  congr 1
  funext point
  cases point <;> simp [label, isLabelH, hFor, Fin.ext_iff]

/-- Password-specific A queries are no more numerous than all A queries. -/
theorem password_count_le [DecidableEq Password] (password : Password)
    (history : List (Point Password Entropy)) : history.countP (aFor password) ≤ history.countP isA := by
  apply List.countP_mono_left
  intro point _ found
  cases point <;> simp_all [aFor, isA]

/-- Before B_i, the private chain contains precisely 11-i older A queries. -/
theorem labels_before_b (round : Fin 12) :
    ((inverseLabels 12).take (3 * (11 - round.val))).countP isLabelA = 11 - round.val := by
  fin_cases round <;> decide

/-- Before A_i, no private H query carries the same round index. -/
theorem labels_before_a (round : Fin 12) :
    ((inverseLabels 12).take (3 * (11 - round.val) + 1)).countP (isLabelH round.val) = 0 := by
  fin_cases round <;> decide

/-- Before H_i, no private B query carries the next round i-1, when it exists. -/
theorem labels_before_h (round : Fin 12) (positive : 0 < round.val) :
    ((inverseLabels 12).take (3 * (11 - round.val) + 2)).countP (isLabelB (round.val - 1)) = 0 := by
  fin_cases round
  all_goals dsimp only at positive
  all_goals first | omega | decide

/-- Private A points before B_i contribute at most 11-i, including repeated salts. -/
theorem private_a_bound [DecidableEq Password] (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (round : Fin 12) :
    ((outcome password container tables adversary).chain.take (3 * (11 - round.val))).countP
        (aFor password) ≤ 11 - round.val := by
  refine (password_count_le password _).trans_eq ?_
  rw [← count_a, List.map_take, full_labels]
  exact labels_before_b round

/-- No same-round private mask query is added before A_i. -/
theorem private_h_zero (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (round : Fin 12) :
    ((outcome password container tables adversary).chain.take (3 * (11 - round.val) + 1)).countP
        (hFor round) = 0 := by
  rw [← count_h, List.map_take, full_labels]
  exact labels_before_a round

/-- No next-round private salt query is added before H_i. -/
theorem private_b_zero (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (round : Fin 12) (positive : 0 < round.val) :
    ((outcome password container tables adversary).chain.take (3 * (11 - round.val) + 2)).countP
        (bFor ⟨round.val - 1, by omega⟩) = 0 := by
  rw [← count_b, List.map_take, full_labels]
  exact labels_before_h round positive

end ChainMetadata

/-!
Reorder the four independently uniform ideal tables. Every factorization is
derived from Gamma2Model.sampleTables, not postulated as an independence axiom.
-/

namespace TableFactors

open Gamma2Model ProbabilityTools

variable {Password Entropy : Type}

abbrev ATable (Password : Type) := Password × Half → Key
abbrev BTable := Fin 12 × Half → Half
abbrev HTable := Key × Fin 12 × Half → Half
abbrev GTable (Entropy : Type) := Entropy → Hash
abbrev Quad (Password Entropy : Type) := ATable Password × BTable × HTable × GTable Entropy

/-- The four fields of the ideal-table record form a Cartesian product. -/
def tableEquiv : Tables Password Entropy ≃ Quad Password Entropy where
  toFun tables := (tables.a, tables.b, tables.h, tables.g)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  left_inv := by intro tables; cases tables; rfl
  right_inv := by rintro ⟨a, b, h, g⟩; rfl

/-- Fix B/H/G first and place the independently sampled A table last. -/
def packA : ((BTable × HTable × GTable Entropy) × ATable Password) ≃ Tables Password Entropy where
  toFun selected := ⟨selected.2, selected.1.1, selected.1.2.1, selected.1.2.2⟩
  invFun tables := ((tables.b, tables.h, tables.g), tables.a)
  left_inv := by rintro ⟨⟨b, h, g⟩, a⟩; rfl
  right_inv := by intro tables; cases tables; rfl

/-- Fix A/H/G first and place the independently sampled B table last. -/
def packB : ((ATable Password × HTable × GTable Entropy) × BTable) ≃ Tables Password Entropy where
  toFun selected := ⟨selected.1.1, selected.2, selected.1.2.1, selected.1.2.2⟩
  invFun tables := ((tables.a, tables.h, tables.g), tables.b)
  left_inv := by rintro ⟨⟨a, h, g⟩, b⟩; rfl
  right_inv := by intro tables; cases tables; rfl

/-- Fix A/B/G first and place the independently sampled H table last. -/
def packH : ((ATable Password × BTable × GTable Entropy) × HTable) ≃ Tables Password Entropy where
  toFun selected := ⟨selected.1.1, selected.1.2.1, selected.2, selected.1.2.2⟩
  invFun tables := ((tables.a, tables.b, tables.g), tables.h)
  left_inv := by rintro ⟨⟨a, b, g⟩, h⟩; rfl
  right_inv := by intro tables; cases tables; rfl

noncomputable section

local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

variable [Fintype Password] [DecidableEq Password] [Fintype Entropy] [DecidableEq Entropy]

local instance : Fintype (Tables Password Entropy) :=
  Fintype.ofEquiv (Quad Password Entropy) tableEquiv.symm

local instance : Nonempty (Tables Password Entropy) := ⟨tableEquiv.symm default⟩

/-- The specified independent field sampling is the uniform law on full ideal-table records. -/
theorem sample_uniform : sampleTables (Password := Password) (Entropy := Entropy) =
    PMF.uniformOfFintype (Tables Password Entropy) := by
  have transported := PMF.uniformOfFintype_map_of_bijective
    (tableEquiv (Password := Password) (Entropy := Entropy)).symm
    (tableEquiv (Password := Password) (Entropy := Entropy)).symm.bijective
  calc
    sampleTables = (PMF.uniformOfFintype (Quad Password Entropy)).map tableEquiv.symm := by
      simp only [sampleTables, uniform_product, independentPair,
        PMF.map_bind, PMF.map_comp, Function.comp_def, tableEquiv]
      rfl
    _ = _ := transported

/-- Any product presentation of the table record yields independent sampling in that order. -/
theorem sample_factor {Others Selected : Type} [Fintype Others] [Nonempty Others] [Fintype Selected]
    [Nonempty Selected] (pack : (Others × Selected) ≃ Tables Password Entropy) :
    sampleTables (Password := Password) (Entropy := Entropy) =
      (PMF.uniformOfFintype Others).bind fun others =>
        (PMF.uniformOfFintype Selected).map fun selected => pack (others, selected) := by
  rw [sample_uniform]
  have transported := PMF.uniformOfFintype_map_of_bijective pack pack.bijective
  rw [← transported, uniform_product]
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- A's full random table is independent of the three fixed other tables. -/
theorem factor_a : sampleTables (Password := Password) (Entropy := Entropy) =
    (PMF.uniformOfFintype (BTable × HTable × GTable Entropy)).bind fun others =>
      (PMF.uniformOfFintype (ATable Password)).map fun a =>
        (⟨a, others.1, others.2.1, others.2.2⟩ : Tables Password Entropy) :=
  sample_factor packA

/-- B's full random table is independent of the three fixed other tables. -/
theorem factor_b : sampleTables (Password := Password) (Entropy := Entropy) =
    (PMF.uniformOfFintype (ATable Password × HTable × GTable Entropy)).bind fun others =>
      (PMF.uniformOfFintype BTable).map fun b =>
        (⟨others.1, b, others.2.1, others.2.2⟩ : Tables Password Entropy) :=
  sample_factor packB

/-- H's full random table is independent of the three fixed other tables. -/
theorem factor_h : sampleTables (Password := Password) (Entropy := Entropy) =
    (PMF.uniformOfFintype (ATable Password × BTable × GTable Entropy)).bind fun others =>
      (PMF.uniformOfFintype HTable).map fun h =>
        (⟨others.1, others.2.1, h, others.2.2⟩ : Tables Password Entropy) :=
  sample_factor packH

end

end TableFactors

/-! A shared finite-bit enumeration for the final theorem assemblies. -/
namespace FiniteBits
/-- Port to Lean 4.35: used as a local instance, so it is unfolded at instance transparency as before. -/
@[instance_reducible] noncomputable def fintype (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm
end FiniteBits

end
end MhfeLean
