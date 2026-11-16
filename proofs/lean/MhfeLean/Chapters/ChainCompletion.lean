import Mathlib.Data.List.GetD
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.OracleModel

namespace MhfeLean
noncomputable section

/-! # Lemmas G4 and G5: terminal freshness and complete chains
-/

/-! Retain an adaptive program's exact trace inside its result, without direct table access. -/
namespace TraceProgram
open Gamma2Model
variable {Password Entropy Result : Type}

def withTrace (program : OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Password Entropy) (Result × List (Point Password Entropy)) :=
  OracleComp.construct
    (fun result => pure (result, []))
    (fun point _ recurse => do
      let value ← ask point
      let later ← recurse value
      pure (later.1, point :: later.2)) program

theorem execute_withTrace (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) :
    execute tables (withTrace program) = (execute tables program, (execute tables program).2) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih =>
    change execute tables (do
      let value ← ask point
      let later ← withTrace (next value)
      pure (later.1, point :: later.2)) =
      (execute tables (ask point >>= next), (execute tables (ask point >>= next)).2)
    simp only [execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, execute_pure, ih,
      List.append_nil, List.singleton_append]

end TraceProgram

/-! A causal cut of the actual inverse computation just before its terminal H0 query. -/
namespace FinalCut
open Gamma2Model
variable {Password Entropy : Type}

structure Cut (Password Entropy : Type) where
  state : State
  key : Key
  before : List (Point Password Entropy)

def terminal (cut : Cut Password Entropy) : Point Password Entropy :=
  .h cut.key 0 cut.state.1

def finish (tables : Tables Password Entropy) (cut : Cut Password Entropy) : State :=
  (cut.state.2 ^^^ tables.h (cut.key, 0, cut.state.1), cut.state.1)

def prepare (password : Password) :
    (round : Nat) → State → round < 12 → OracleComp (spec Password Entropy) (Cut Password Entropy)
  | 0, state, _ => do
    let salt ← ask (.b 0 state.1)
    let key ← ask (.a password salt)
    pure ⟨state, key, [.b 0 state.1, .a password salt]⟩
  | round + 1, state, bound => do
    let selected : Fin 12 := ⟨round + 1, bound⟩
    let salt ← ask (.b selected state.1)
    let key ← ask (.a password salt)
    let mask ← ask (.h key selected state.1)
    let remaining ← prepare password round (BitVec.xor state.2 mask, state.1) (by omega)
    pure { remaining with before := [.b selected state.1, .a password salt,
      .h key selected state.1] ++ remaining.before }

variable (password : Password) (tables : Tables Password Entropy) (round : Nat)

/-- One inverse step, stated with a variable remaining fuel to avoid unfolding it. -/
theorem finalize_step (bound : round < 12) (state : State) :
    execute tables (finalize password (round + 1) state (by omega)) =
      let selected : Fin 12 := ⟨round, bound⟩
      let salt := tables.b (selected, state.1)
      let key := tables.a (password, salt)
      let mask := tables.h (key, selected, state.1)
      let rest := execute tables (finalize password round (state.2 ^^^ mask, state.1) (by omega))
      ((rest.1.1, [.b selected state.1, .a password salt, .h key selected state.1] ++ rest.1.2),
        [.b selected state.1, .a password salt, .h key selected state.1] ++ rest.2) := by
  simp only [finalize, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, execute_pure, answer,
    List.append_nil, List.cons_append, List.nil_append]

/-- One prefix step, with its unexpanded recursive remainder. -/
theorem prepare_step (bound : round + 1 < 12) (state : State) :
    execute tables (prepare password (round + 1) state bound) =
      let selected : Fin 12 := ⟨round + 1, bound⟩
      let salt := tables.b (selected, state.1)
      let key := tables.a (password, salt)
      let mask := tables.h (key, selected, state.1)
      let rest := execute tables (prepare password round (state.2 ^^^ mask, state.1) (by omega))
      ({ rest.1 with before := [.b selected state.1, .a password salt, .h key selected state.1] ++ rest.1.before },
        [.b selected state.1, .a password salt, .h key selected state.1] ++ rest.2) := by
  simp only [prepare, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, execute_pure, answer, BitVec.xor_eq,
    List.append_nil, List.cons_append, List.nil_append]

/-- The returned private prefix is exactly the emitted prefix. -/
theorem trace (bound : round < 12) (state : State) :
    (execute tables (prepare password round state bound)).2 =
      (execute tables (prepare password round state bound)).1.before := by
  classical
  induction round generalizing state <;> aesop (add simp [prepare, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,
    execute_pure, List.append_nil, List.singleton_append])

/-- Completing the cut with one H0 lookup gives exactly the original finalized result and chain. -/
theorem finalized (bound : round < 12) (state : State) :
    (execute tables (finalize password (round + 1) state (by omega))).1 =
      let cut := (execute tables (prepare password round state bound)).1
      (finish tables cut, cut.before ++ [terminal cut]) := by
  induction round generalizing state with
  | zero => rfl
  | succ round ih =>
    rw [finalize_step, prepare_step]
    dsimp only
    rw [ih (by omega)]
    rfl

/-- No private-prefix query has H round zero. -/
theorem terminal_absent (bound : round < 12) (state : State) (key : Key) (right : Half) :
    Point.h key 0 right ∉ (execute tables (prepare password round state bound)).1.before := by
  induction round generalizing state with
  | zero => simp [prepare, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g]
  | succ round ih =>
    rw [prepare_step]
    dsimp only
    have different : (0 : Fin 12) ≠ ⟨round + 1, bound⟩ := by
      intro equal
      have := congrArg Fin.val equal
      change 0 = round + 1 at this
      omega
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Point.h.injEq, reduceCtorEq, different, false_and, and_false, false_or]
    exact ih (by omega) _

end FinalCut

/-! Cut the actual execution before H0 and test a bounded set of source-half guesses. -/
namespace G4Programs
open Gamma2Model FinalCut TraceProgram
open OracleTree OracleProjection FocusedExecution
open FreshSampling MatchingSets G3Programs
variable {Password Entropy Result : Type}

abbrev Context (Password Entropy : Type) := Half × List (Point Password Entropy)

def isG : Point Password Entropy → Bool
  | .g _ => true
  | _ => false

def extract (firstHalf : Entropy → Half) (offset : Half) : Point Password Entropy → Option Half
  | .g entropy => some (offset ^^^ firstHalf entropy)
  | _ => none

def matching (firstHalf : Entropy → Half) (qG : Nat) (context : Context Password Entropy) :
    Finset Half :=
  (((context.2.filterMap (extract firstHalf context.1)).take qG).toFinset)

/-- Truncation is redundant on budget-respecting executions and bounds all other contexts too. -/
theorem matching_bound (firstHalf : Entropy → Half) (qG : Nat) (context : Context Password Entropy) :
    (matching firstHalf qG context).card ≤ qG := by
  exact (List.toFinset_card_le _).trans (List.length_take_le ..)

def program (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Password Entropy) ((Key × Fin 12 × Half) × Context Password Entropy) := do
  let before ← withTrace (adversary container)
  let cut ← prepare password 11 container (by omega)
  pure ((cut.key, 0, cut.state.1), (cut.state.2, before.2))

def focusedProgram (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (others : OthersH Password Entropy) :=
  focused (focusH others.1 others.2.1 others.2.2) (program password container adversary)

/-- The cut program returns the actual terminal point and original adversary trace. -/
theorem execute_program (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    execute tables (program password container adversary) =
      let before := execute tables (adversary container)
      let cut := (execute tables (prepare password 11 container (by omega))).1
      (((cut.key, 0, cut.state.1), (cut.state.2, before.2)), before.2 ++ cut.before) := by
  simp only [program, execute_bind, execute_withTrace, execute_pure, List.append_nil, trace]

def event (firstHalf : Entropy → Half) (qG : Nat) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (tables : Tables Password Entropy) : Bool :=
  hits (matching firstHalf qG) (observedTable
    (focusedProgram password container adversary (tables.a, tables.b, tables.g)) tables.h)

end G4Programs

/-! Bad with an unqueried terminal point implies a fresh-table hit, with no probability premise. -/
namespace G4Hit
open Gamma2Model FinalCut G4Programs
open OracleTree OracleProjection FocusedExecution
open FreshSampling G3Fresh
variable {Password Entropy Result : Type}

attribute [local irreducible] prepare finalize

theorem extract_length (firstHalf : Entropy → Half) (offset : Half)
    (history : List (Point Password Entropy)) :
    (history.filterMap (extract firstHalf offset)).length = history.countP isG := by
  induction history with
  | nil => rfl
  | cons point history ih => cases point <;> simp [extract, isG, ih, List.filterMap_cons, List.countP_cons]

theorem matching_has (firstHalf : Entropy → Half) (qG : Nat) (offset : Half)
    (history : List (Point Password Entropy)) (mask : Half) (entropy : Entropy)
    (budget : history.countP isG ≤ qG) (queried : Point.g entropy ∈ history)
    (agrees : firstHalf entropy = offset ^^^ mask) : mask ∈ matching firstHalf qG (offset, history) := by
  unfold matching
  rw [List.take_of_length_le (by rw [extract_length]; exact budget)]
  apply List.mem_toFinset.mpr
  apply List.mem_filterMap.mpr
  refine ⟨Point.g entropy, queried, ?_⟩
  change some (offset ^^^ firstHalf entropy) = some mask
  rw [agrees]
  simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- G4's larger half-match event: full source equality necessarily implies this. -/
def BadHalf (firstHalf : Entropy → Half) (out : Outcome Password Entropy Result) : Prop :=
  ∃ entropy, Point.g entropy ∈ out.adversaryQueries ∧ firstHalf entropy = out.recovered.1

set_option maxHeartbeats 1000000 in
/-- An unqueried H0 and a correct source-half query force the operational fresh-hit test. -/
theorem bad_fresh_hit (firstHalf : Entropy → Half) (qG : Nat)
    (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (budget : (execute tables (adversary container)).2.countP isG ≤ qG)
    (bad : BadHalf firstHalf (outcome password container tables adversary))
    (notQueried : terminal (execute tables (prepare password 11 container (by omega))).1 ∉
      (execute tables (adversary container)).2) :
    event firstHalf qG password container adversary tables = true := by
  let cut := (execute tables (prepare password 11 container (by omega))).1
  have cutResult := finalized password tables 11 (by omega) container
  obtain ⟨entropy, queried, sourceHalf⟩ := bad
  have recovered : (outcome password container tables adversary).recovered = finish tables cut := by
    dsimp only [outcome]
    with_reducible exact congrArg (fun output : State × List (Point Password Entropy) => output.1) cutResult
  have half : firstHalf entropy = cut.state.2 ^^^ tables.h (cut.key, 0, cut.state.1) :=
    sourceHalf.trans (congrArg Prod.fst recovered)
  have isMatching := matching_has firstHalf qG cut.state.2
    (execute tables (adversary container)).2 (tables.h (cut.key, 0, cut.state.1)) entropy budget queried half
  have typedFresh : terminal cut ∉ (execute tables (program password container adversary)).2 := by
    rw [execute_program]
    simp only [List.mem_append, not_or]
    exact ⟨notQueried, terminal_absent password tables 11 (by omega) container cut.key cut.state.1⟩
  have focusedFresh := fresh_of_typed (focusH tables.a tables.b tables.g) tables.h tables
    (by intro point; cases point <;> rfl) (program password container adversary)
    (terminal cut) (cut.key, 0, cut.state.1) (fun point found => identifiesH (tables.a, tables.b, tables.g) point (cut.key, 0, cut.state.1) found) typedFresh
  have result := result_eq (focusH tables.a tables.b tables.g) tables.h tables
    (by intro point; cases point <;> rfl) (program password container adversary)
  rw [execute_program] at result
  have freshActual :
      (evaluate tables.h (focused (focusH tables.a tables.b tables.g) (program password container adversary))).1.1 ∉
      (evaluate tables.h (focused (focusH tables.a tables.b tables.g) (program password container adversary))).2 := by
    rw [result]
    exact focusedFresh
  unfold event observedTable selectFresh focusedProgram
  rw [if_neg freshActual]
  simp only [Option.map_some, hits]
  simp only [result]
  exact decide_eq_true isMatching

end G4Hit

/-! The deterministic order implication required by G4. -/
namespace G4Order
open Gamma2Model G2 QueryCounts
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]

/-- All chain A points were queried before private finalization. -/
def Complete (run : Run (Point Password Entropy)) : Prop :=
  ∀ index, index < run.count → isA (run.point index) = true → Queried run index

/-- Without Early, an incomplete A chain cannot have queried its terminal H point. -/
theorem incomplete_terminal (run : Run (Point Password Entropy)) (size : run.count = 36)
    (lastNotA : isA (run.point 35) = false) (notEarly : ¬ Early run) (notComplete : ¬ Complete run) :
    ¬ Queried run 35 := by
  intro terminalQueried
  apply notComplete
  intro index within isAnA
  have bound : index < 36 := by omega
  have earlier : index < 35 := by
    by_cases equal : index = 35
    · subst index; rw [lastNotA] at isAnA; contradiction
    · omega
  exact Nat.lt_trans (all_ordered run notEarly index 35 earlier (by omega)) terminalQueried

/-- Chronological queriedness refers exactly to membership in the adversary's prefix. -/
theorem queried_iff_mem (before chain : List (Point Password Entropy)) (index : Nat) :
    Queried (fromTrace before chain) index ↔ (fromTrace before chain).point index ∈ before := by
  simp only [Queried, firstTime, fromTrace, List.idxOf_append]
  by_cases found : chain.getD index fallbackPoint ∈ before
  · simp only [found, if_true, iff_true]
    exact List.idxOf_lt_length_iff.mpr found
  · simp only [found, if_false, iff_false]
    omega

end G4Order

/-! Identify the chronological last point with the causal cut's actual H0 query. -/
namespace G4Terminal
open Gamma2Model FinalCut G4Order QueryCounts
variable {Password Entropy Result : Type}

attribute [local irreducible] prepare finalize

variable (password : Password) (container : State) (tables : Tables Password Entropy)

theorem chain_shape
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (outcome password container tables adversary).chain =
      let cut := (execute tables (prepare password 11 container (by omega))).1
      cut.before ++ [terminal cut] := by
  dsimp only [outcome]
  with_reducible exact (congrArg (fun output : State × List (Point Password Entropy) => output.2) (finalized password tables 11 (by omega) container))

theorem prefix_length :
    (execute tables (prepare password 11 container (by omega))).1.before.length = 35 := by
  have size := finalize_chain_length tables password 12 container (by omega)
  have shape := congrArg (fun output => output.2.length) (finalized password tables 11 (by omega) container)
  simp only [List.length_append, List.length_singleton] at shape
  rw [size] at shape
  omega

theorem last_point
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (chronologicalRun password container tables adversary).point 35 =
      terminal (execute tables (prepare password 11 container (by omega))).1 := by
  dsimp only [chronologicalRun, fromTrace]
  rw [chain_shape, List.getD_append_right _ _ _ _ (by rw [prefix_length])]
  rw [prefix_length]
  rfl

variable [DecidableEq Password] [DecidableEq Entropy]

/-- The order conclusion refers to the same terminal point that the cut program selects. -/
theorem not_queried (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ G2.Early (chronologicalRun password container tables adversary))
    (notComplete : ¬ Complete (chronologicalRun password container tables adversary)) :
    terminal (execute tables (prepare password 11 container (by omega))).1 ∉
      (execute tables (adversary container)).2 := by
  have lastNotA : isA ((chronologicalRun password container tables adversary).point 35) = false := by
    rw [last_point]
    rfl
  have missing := incomplete_terminal _ (chronologicalRun_count password container tables adversary)
    lastNotA notEarly notComplete
  simp only [chronologicalRun] at missing
  rw [queried_iff_mem] at missing
  change (chronologicalRun password container tables adversary).point 35 ∉
    (outcome password container tables adversary).adversaryQueries at missing
  rw [last_point] at missing
  exact missing

end G4Terminal

/-!
Lemma G4. A source query matching the full unknown source also matches its
first 128 bits, so we prove the stronger bound for that larger half-match event.
-/
namespace G4
open Gamma2Model G4Programs G4Hit G4Order
open G3Assembly G3Probability TableFactors
open GameExpectation MomentTools FreshSampling
variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

def test (firstHalf : Entropy → Half) (out : Outcome Password Entropy Result) : Bool := by
  classical
  exact decide (BadHalf firstHalf out ∧ ¬ Complete (fromTrace out.adversaryQueries out.chain) ∧
    ¬ G2.Early (fromTrace out.adversaryQueries out.chain))

theorem hit_bound (firstHalf : Entropy → Half) (qG : Nat) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    moment sampleTables (fun tables => if event firstHalf qG password container adversary tables then 1 else 0) ≤
      (qG : ENNReal) / (2 ^ 128 : ENNReal) := by
  rw [factor_h, MomentTools.bind]
  apply bounded
  intro others
  rw [moment_map]
  have bound := fresh_hit_bound (focusedProgram password container adversary others)
    (matching firstHalf qG) qG (matching_bound firstHalf qG)
  rw [PMF.map_comp, probability] at bound
  simp only [event, Function.comp_def, card_bits, Nat.cast_pow, Nat.cast_ofNat] at bound ⊢
  exact bound

/-- G4 for the actual game: no completed chain and no Early leave only blind half matches. -/
theorem lemma_g4 (firstHalf : Entropy → Half) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) (qG : Nat)
    (budget : ∀ container tables, (execute tables (adversary container)).2.countP isG ≤ qG) :
    ((game passwords adversary).map (test firstHalf)) true ≤ (qG : ENNReal) / (2 ^ 128 : ENNReal) := by
  classical
  rw [probability]
  calc
    _ ≤ moment (game passwords adversary) (fun _ => (qG : ENNReal) / (2 ^ 128 : ENNReal)) := by
      apply game_transfer
      intro password container
      calc
        _ ≤ moment sampleTables (fun tables => if event firstHalf qG password container adversary tables then 1 else 0) := by
          apply mono
          intro tables
          by_cases enabled : test firstHalf (outcome password container tables adversary) = true
          · have details : BadHalf firstHalf (outcome password container tables adversary) ∧
                ¬ Complete (chronologicalRun password container tables adversary) ∧
                ¬ G2.Early (chronologicalRun password container tables adversary) :=
              of_decide_eq_true enabled
            have hit := bad_fresh_hit firstHalf qG password container tables adversary (budget container tables)
              details.1 (G4Terminal.not_queried password container tables adversary details.2.2 details.2.1)
            simp only [enabled, hit, ↓reduceIte, le_refl]
          · have disabled : test firstHalf (outcome password container tables adversary) = false := Bool.eq_false_iff.mpr enabled
            simp only [disabled, Bool.false_eq_true, ↓reduceIte, zero_le]
        _ ≤ _ := by rw [constant]; exact hit_bound firstHalf qG password container adversary
    _ = _ := constant _ _

/-- The source Bad event queries G at the full recovered entropy, not just a half. -/
def sourceTest (source : State → Entropy) (out : Outcome Password Entropy Result) : Bool := by
  classical
  exact decide (Point.g (source out.recovered) ∈ out.adversaryQueries ∧
    ¬ Complete (fromTrace out.adversaryQueries out.chain) ∧
    ¬ G2.Early (fromTrace out.adversaryQueries out.chain))

/-- Exact source form; the projection premise only says entropy includes the first state half. -/
theorem lemma_g4_source (source : State → Entropy) (firstHalf : Entropy → Half)
    (projects : ∀ state, firstHalf (source state) = state.1) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) (qG : Nat)
    (budget : ∀ container tables, (execute tables (adversary container)).2.countP isG ≤ qG) :
    ((game passwords adversary).map (sourceTest source)) true ≤ (qG : ENNReal) / (2 ^ 128 : ENNReal) := by
  classical
  apply le_trans _ (lemma_g4 firstHalf passwords adversary qG budget)
  rw [probability, probability]
  apply mono
  intro out
  by_cases enabled : sourceTest source out = true
  · have details : Point.g (source out.recovered) ∈ out.adversaryQueries ∧
        ¬ Complete (fromTrace out.adversaryQueries out.chain) ∧
        ¬ G2.Early (fromTrace out.adversaryQueries out.chain) := of_decide_eq_true enabled
    have larger : test firstHalf out = true := decide_eq_true
      ⟨⟨source out.recovered, details.1, projects out.recovered⟩, details.2⟩
    simp only [enabled, larger, ↓reduceIte, le_refl]
  · have disabled := Bool.eq_false_iff.mpr enabled
    simp only [disabled, Bool.false_eq_true, ↓reduceIte, zero_le]

/-- Independent private random coins do not change G4's bound. -/
theorem randomized {Strategy : Type} (coins : PMF Strategy) (source : State → Entropy)
    (firstHalf : Entropy → Half) (projects : ∀ state, firstHalf (source state) = state.1)
    (passwords : PMF Password)
    (adversary : Strategy → State → OracleComp (spec Password Entropy) Result) (qG : Nat)
    (budget : ∀ strategy container tables, (execute tables (adversary strategy container)).2.countP isG ≤ qG) :
    ((G3.randomizedGame coins passwords adversary).map (sourceTest source)) true ≤
      (qG : ENNReal) / (2 ^ 128 : ENNReal) := by
  rw [probability, G3.randomizedGame, MomentTools.bind]
  apply bounded
  intro strategy
  rw [← probability]
  exact lemma_g4_source source firstHalf projects passwords (adversary strategy) qG (budget strategy)

end G4

/-! Concrete source-prefix instantiation for ENT = 128,160,192,224. -/
namespace G4Bip39
open Gamma2Model G4 G4Programs
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

/-- The source consists of L0 and the high tailBits bits of R0. -/
def entropy (tailBits : Nat) (state : State) : Half × BitVec tailBits :=
  (state.1, (state.2 >>> (128 - tailBits)).setWidth tailBits)

/-- The first 128 entropy bits are L0 by construction, not a probabilistic assumption. -/
theorem first_half (tailBits : Nat) (state : State) : (entropy tailBits state).1 = state.1 := rfl

variable {Password Result : Type} [Fintype Password] [DecidableEq Password]

/-- The full source-query bound for each supported short entropy width. -/
theorem lemma_g4 (tailBits : Nat) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password (Half × BitVec tailBits)) Result) (qG : Nat)
    (budget : ∀ container tables, (execute tables (adversary container)).2.countP isG ≤ qG) :
    ((game passwords adversary).map (sourceTest (entropy tailBits))) true ≤
      (qG : ENNReal) / (2 ^ 128 : ENNReal) :=
  lemma_g4_source (entropy tailBits) Prod.fst (first_half tailBits) passwords adversary qG budget

/-- Actual tail widths of the four short BIP39 sources. -/
theorem supported_widths :
    ([(128 : Nat), 160, 192, 224].map (fun ent => ent - 128)) = [0, 32, 64, 96] := by decide

end G4Bip39

/-! Lemma G5: distinct actual chain points and twelve real-password A queries. -/
namespace G5
open Gamma2Model G2 G4Order QueryCounts
open MhfeChain WalkProperties MhfeMonitorCoverage
variable {TracePoint : Type} [DecidableEq TracePoint]

theorem distinct (run : Run TracePoint) (notEarly : ¬ Early run) :
    Function.Injective (fun index : Fin run.count => run.point index.val) := by
  intro first second equal
  apply Fin.ext
  by_contra different
  have sameTime : firstTime run first.val = firstTime run second.val :=
    congrArg (fun point => run.queries.idxOf point) equal
  rcases lt_or_gt_of_ne different with before | before
  · have := all_ordered run notEarly first.val second.val before second.isLt; omega
  · have := all_ordered run notEarly second.val first.val before first.isLt; omega

variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

attribute [local irreducible] finalize walk

def aStage (index : Fin 12) : Fin 36 := ⟨3 * index.val + 1, by have := index.isLt; omega⟩

theorem a_point (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (index : Fin 12) :
    ∃ salt, (chronologicalRun password container tables adversary).point (aStage index).val = Point.a password salt := by
  have within : (aStage index).val < (walk password tables 36 (.salt 11 container)).length := by
    rw [full_walk_length password container tables adversary]
    exact (aStage index).isLt
  have pointAt := chronological_point password container tables adversary (aStage index).val within
  have position := full_stage_at password container tables (aStage index).val within
  cases cursor : (walk password tables 36 (.salt 11 container))[(aStage index).val]'within with
  | salt round state => rw [cursor] at position; simp only [stage, aStage] at position; omega
  | key round state salt => exact ⟨salt, by simpa only [cursor, point] using pointAt⟩
  | mask round state key => rw [cursor] at position; simp only [stage, aStage] at position; omega

/-- The cardinality conclusion counts actual adversary queries, with repetitions allowed. -/
theorem twelve_queries (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (complete : Complete (chronologicalRun password container tables adversary)) :
    12 ≤ (outcome password container tables adversary).adversaryQueries.countP (aFor password) := by
  classical
  let run := chronologicalRun password container tables adversary
  let choices : Fin 12 → Point Password Entropy := fun index => run.point (aStage index).val
  have size : run.count = 36 := chronologicalRun_count password container tables adversary
  have injective : Function.Injective choices := by
    intro first second equal
    have equation : run.point (aStage first).val = run.point (aStage second).val := by
      with_reducible exact equal
    have sameIndex := distinct run notEarly
      (a₁ := ⟨(aStage first).val, by rw [size]; exact (aStage first).isLt⟩)
      (a₂ := ⟨(aStage second).val, by rw [size]; exact (aStage second).isLt⟩) equation
    have numeric := congrArg Fin.val sameIndex
    apply Fin.ext
    change 3 * first.val + 1 = 3 * second.val + 1 at numeric
    omega
  have member : ∀ index, choices index ∈
      ((outcome password container tables adversary).adversaryQueries.filter (aFor password)).toFinset := by
    intro index
    obtain ⟨salt, shape⟩ := a_point password container tables adversary index
    have aQuery : isA (run.point (aStage index).val) = true := by rw [shape]; rfl
    have asked := complete (aStage index).val (by rw [size]; exact (aStage index).isLt) aQuery
    change Queried (fromTrace (outcome password container tables adversary).adversaryQueries
      (outcome password container tables adversary).chain) (aStage index).val at asked
    rw [queried_iff_mem] at asked
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    refine ⟨asked, ?_⟩
    change aFor password (run.point (aStage index).val) = true
    rw [shape]
    simp only [aFor, decide_true]
  have subset : Finset.univ.image choices ⊆
      ((outcome password container tables adversary).adversaryQueries.filter (aFor password)).toFinset := by
    intro query found
    obtain ⟨index, _, equal⟩ := Finset.mem_image.mp found
    rw [← equal]
    exact member index
  calc
    12 = (Finset.univ.image choices).card := by rw [Finset.card_image_of_injective _ injective]; rfl
    _ ≤ _ := Finset.card_le_card subset
    _ ≤ _ := List.toFinset_card_le _
    _ = _ := List.countP_eq_length_filter.symm

end G5

end
end MhfeLean
