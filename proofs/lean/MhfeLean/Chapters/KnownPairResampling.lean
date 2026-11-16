import Mathlib.Data.List.GetD
import MhfeLean.Chapters.ChainCompletion
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.ShortSources

namespace MhfeLean
noncomputable section

/-! # Lemma K1 and the two known-pair chains
-/

/-! Discharge the structural re-sampling hypotheses using the actual MHFE round indices. -/
namespace K1System
open Gamma2Model TableFactors KnownPairModel
open PathResampling
variable {Password : Type}

variable (selected : Fin 11) (password : Password) (a : ATable Password) (b : BTable)
  (source : State)

def prefixState (rest : Rest selected) : State :=
  Lemma1.encrypt (beforeMasks selected password a b (fill selected rest)) source

def system : System HInput (Rest selected) where
  rest := restrict selected
  first := fun rest =>
    let state := prefixState selected password a b source rest
    (a (password, b (selected.castSucc, state.2)), selected.castSucc, state.2)
  second := fun _ left => (a (password, b (selected.succ, left)), selected.succ, left)
  input := prefixState selected password a b source
  suffix := fun rest => roundsEquiv (afterMasks selected password a b (fill selected rest))
  apart := by
    intro rest left equal
    have rounds := congrArg (fun query : HInput => query.2.1.val) equal
    change selected.val = selected.val + 1 at rounds
    omega
  keepFirst := by
    intro table value
    funext query
    apply Function.update_of_ne
    intro equal
    apply query.property.1
    exact congrArg (fun point : HInput => point.2.1) equal
  keepSecond := by
    intro table left value
    funext query
    apply Function.update_of_ne
    intro equal
    apply query.property.2
    exact congrArg (fun point : HInput => point.2.1) equal

/-- Prefix/suffix composition of the already verified Feistel round permutation. -/
theorem encrypt_append (masks later : List (Half → Half)) (state : State) :
    Lemma1.encrypt (masks ++ later) state =
      Lemma1.encrypt later (Lemma1.encrypt masks state) := by
  induction masks generalizing state with
  | nil => rfl
  | cons mask masks ih => simpa only [List.cons_append, Lemma1.encrypt] using ih _

/-- The structural system's output is exactly the twelve-round MHFE ciphertext. -/
theorem output_is_cipher (h : HTable) :
    output (system selected password a b source) h = cipher password a b h source := by
  simp only [output, middle, system, prefixState, before_fill, after_fill, roundsEquiv]
  unfold cipher
  rw [mask_partition selected, encrypt_append, encrypt_append]
  rfl

end K1System

/-! Uniform full-table law for the structural two-path re-sampling equivalence. -/
namespace PathLaw
open Gamma2Model PathResampling ProbabilityTools
variable {Domain Context : Type} [DecidableEq Domain]
variable (system : System Domain Context)

def original (table : Domain → Half) : State × (Domain → Half) :=
  (output system table, table)

def programmed (value : State × (Domain → Half)) : State × (Domain → Half) :=
  (value.1, restore system value)

theorem observations (seed : (Domain → Half) × State) :
    programmed system (exchange system seed) = original system seed.1 := by
  apply Prod.ext
  · rfl
  · exact congrArg Prod.fst ((exchange system).left_inv seed)

local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm
variable [Fintype Domain]

theorem exact_law :
    (PMF.uniformOfFintype (State × (Domain → Half))).map (programmed system) =
      (PMF.uniformOfFintype (Domain → Half)).map (original system) := by
  have transported := PMF.uniformOfFintype_map_of_bijective (exchange system) (exchange system).bijective
  calc
    _ = ((PMF.uniformOfFintype ((Domain → Half) × State)).map (exchange system)).map (programmed system) := by
      rw [transported]
    _ = (PMF.uniformOfFintype ((Domain → Half) × State)).map (fun seed => original system seed.1) := by
      rw [PMF.map_comp]
      congr 1
      funext seed
      exact observations system seed
    _ = ((PMF.uniformOfFintype ((Domain → Half) × State)).map Prod.fst).map (original system) :=
      (PMF.map_comp Prod.fst _ (original system)).symm
    _ = _ := by rw [uniform_fst]

/-- All independent outer context, including password and A/B, is retained jointly. -/
theorem joint {Environment : Type} (environment : PMF Environment)
    (systems : Environment → System Domain Context) :
    (environment.bind fun env =>
      ((PMF.uniformOfFintype (State × (Domain → Half))).map (programmed (systems env))).map
        (fun value => (env, value))) =
    (environment.bind fun env =>
      ((PMF.uniformOfFintype (Domain → Half)).map (original (systems env))).map
        (fun value => (env, value))) := by
  simp_rw [exact_law]

end PathLaw

/-!
Lemma K1: exact joint re-sampling for the actual twelve-round known-pair cipher.
The complete H table is retained along with P,A,B,Y. Every two-round position
uses the same independently uniform container and independently uniform H'.
-/
namespace K1
open Gamma2Model TableFactors KnownPairModel K1System
open PathResampling ProbabilityTools
variable {Password : Type}
abbrev Environment (Password : Type) := Password × ATable Password × BTable
abbrev Observation (Password : Type) := Password × ATable Password × BTable × HTable × State

/-- Original known pair: retain the complete primitive tables with their ciphertext. -/
def real (source : State) (env : Environment Password) (h : HTable) : Observation Password :=
  (env.1, env.2.1, env.2.2, h, cipher env.1 env.2.1 env.2.2 h source)

/-- Program exactly the two adjacent H masks, using the fixed outer prefix and inverse suffix. -/
def programmed (selected : Fin 11) (source : State) (env : Environment Password)
    (value : State × HTable) : Observation Password :=
  (env.1, env.2.1, env.2.2,
    restore (system selected env.1 env.2.1 env.2.2 source) value, value.1)

local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

/-- Conditional on arbitrary fixed P,A,B and X, the full observed joint laws agree. -/
theorem fixed (selected : Fin 11) (source : State) (env : Environment Password) :
    (PMF.uniformOfFintype (State × HTable)).map (programmed selected source env) =
      (PMF.uniformOfFintype HTable).map (real source env) := by
  let tag : State × HTable → Observation Password := fun value =>
    (env.1, env.2.1, env.2.2, value.2, value.1)
  have law := congrArg (fun distribution : PMF (State × HTable) => distribution.map tag)
    (PathLaw.exact_law (system selected env.1 env.2.1 env.2.2 source))
  (try simp only [PMF.map_comp, Function.comp_def, PathLaw.programmed, PathLaw.original, output_is_cipher, tag, programmed, real] at law ⊢)
  exact law

def realGame (source : State) (environment : PMF (Environment Password)) :
    PMF (Observation Password) :=
  environment.bind fun env => (PMF.uniformOfFintype HTable).map (real source env)

variable (selected : Fin 11) (source : State) (environment : PMF (Environment Password))

def programmedGame : PMF (Observation Password) :=
  environment.bind fun env =>
    (PMF.uniformOfFintype (State × HTable)).map (programmed selected source env)

/-- Source K1, retaining P,A,B,H,Y jointly for every selected adjacent-round position. -/
theorem joint_law : programmedGame selected source environment = realGame source environment := by
  simp only [programmedGame, realGame, fixed]

/-- The re-sampled experiment draws Y and H' independently, as the source game states. -/
theorem independent_sampling :
    programmedGame selected source environment =
      environment.bind fun env =>
        (PMF.uniformOfFintype State).bind fun container =>
          (PMF.uniformOfFintype HTable).map fun h => programmed selected source env (container, h) := by
  simp only [programmedGame, uniform_product, independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]

end K1

/-! Actual forward-then-backward finalization and per-chain Early for the known-pair game. -/
namespace TwoChainModel
open Gamma2Model G2 QueryCounts
variable {Password Entropy Result : Type}

/-- Query forward rounds in their actual ascending order, retaining every chain point. -/
def forward (password : Password) :
    (fuel start : Nat) → State → start + fuel ≤ 12 →
      OracleComp (spec Password Entropy) (State × List (Point Password Entropy))
  | 0, _, state, _ => pure (state, [])
  | fuel + 1, start, state, bound => do
    let round : Fin 12 := ⟨start, by omega⟩
    let salt ← ask (.b round state.2)
    let key ← ask (.a password salt)
    let mask ← ask (.h key round state.2)
    let remaining ← forward password fuel (start + 1) (state.2, BitVec.xor state.1 mask) (by omega)
    pure (remaining.1, [.b round state.2, .a password salt, .h key round state.2] ++ remaining.2)

theorem forward_trace (password : Password) (tables : Tables Password Entropy) (fuel start : Nat)
    (state : State) (bound : start + fuel ≤ 12) :
    (execute tables (forward password fuel start state bound)).2 =
      (execute tables (forward password fuel start state bound)).1.2 := by
  induction fuel generalizing start state with
  | zero => rfl
  | succ fuel ih =>
    simp only [forward, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, execute_pure, List.append_nil,
      List.cons_append, List.nil_append]
    rw [ih]

theorem forward_length (password : Password) (tables : Tables Password Entropy) (fuel start : Nat)
    (state : State) (bound : start + fuel ≤ 12) :
    (execute tables (forward password fuel start state bound)).1.2.length = 3 * fuel := by
  induction fuel generalizing start state with
  | zero => rfl
  | succ fuel ih =>
    simp only [forward, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, execute_pure]
    rw [List.length_append, ih]
    simp only [List.length_cons, List.length_nil]
    omega

structure Outcome2 (Password Entropy Result : Type) where
  base : Outcome Password Entropy Result
  source : State
  forwardState : State
  forwardChain : List (Point Password Entropy)

def enrich (source : State) (out : Outcome Password Entropy Result) :
    Outcome2 Password Entropy Result :=
  let first := execute out.tables (forward out.password 12 0 source (by omega))
  ⟨out, source, first.1.1, first.1.2⟩

def queries (out : Outcome2 Password Entropy Result) : List (Point Password Entropy) :=
  out.base.adversaryQueries ++ out.forwardChain ++ out.base.chain

/-- Both runs use the same global chronological table transcript and the original halt. -/
def run (out : Outcome2 Password Entropy Result) (isForward : Bool) : Run (Point Password Entropy) :=
  let chain := if isForward then out.forwardChain else out.base.chain
  { queries := queries out
    halt := out.base.adversaryQueries.length
    halt_le_length := by simp [queries, List.length_append]
    point := fun index => chain.getD index fallbackPoint
    count := chain.length
    complete := by
      intro index within
      have member : chain.getD index fallbackPoint ∈ chain := by
        rw [← List.getElem_eq_getD (h := within) fallbackPoint]
        exact List.getElem_mem within
      cases isForward with
      | false => exact List.mem_append_right _ member
      | true => exact List.mem_append_left _ (List.mem_append_right _ member) }

/-- The operational finalization performs the forward chain first, then the backward chain. -/
def fullProgram (source : State) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Password Entropy) Unit := do
  let _ ← adversary container
  let _ ← forward password 12 0 source (by omega)
  let _ ← finalize password 12 container (by omega)
  pure ()

attribute [local irreducible] forward finalize

theorem full_trace (source : State) (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (execute tables (fullProgram source password container adversary)).2 =
      queries (enrich source (outcome password container tables adversary)) := by
  simp only [fullProgram, execute_bind, execute_pure, List.append_nil, forward_trace,
    finalize_trace, queries, enrich, outcome, List.append_assoc]

/-- Both actual finalized chains contain exactly 36 points. -/
theorem run_count (source : State) (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (direction : Bool) :
    (run (enrich source (outcome password container tables adversary)) direction).count = 36 := by
  cases direction <;> simp only [run, enrich, outcome, Bool.false_eq_true, ↓reduceIte,
    forward_length, finalize_chain_length]

variable [DecidableEq Password] [DecidableEq Entropy]
def Early2 (out : Outcome2 Password Entropy Result) : Prop :=
  Early (run out true) ∨ Early (run out false)

/-- K2(1): ordering is per chain but its first samples may come from either finalization. -/
theorem predecessor (out : Outcome2 Password Entropy Result) (notEarly : ¬ Early2 out)
    (direction : Bool) (index : Nat) (positive : 0 < index)
    (within : index < (run out direction).count) (queried : Queried (run out direction) index) :
    Queried (run out direction) (index - 1) ∧
      firstTime (run out direction) (index - 1) < firstTime (run out direction) index := by
  have clean : ¬ Early (run out direction) := by
    cases direction with
    | false => exact fun early => notEarly (Or.inr early)
    | true => exact fun early => notEarly (Or.inl early)
  exact predecessor_queried _ clean index positive within queried

/-- K2(2): each chain is distinct; nothing asserts different-chain same-round distinctness. -/
theorem per_chain_distinct (out : Outcome2 Password Entropy Result) (notEarly : ¬ Early2 out)
    (direction : Bool) :
    Function.Injective (fun index : Fin (run out direction).count =>
      (run out direction).point index.val) := by
  apply G5.distinct
  cases direction with
  | false => exact fun early => notEarly (Or.inr early)
  | true => exact fun early => notEarly (Or.inl early)

noncomputable section
variable [Fintype Password] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

/-- The actual known-pair Delta2 law: fixed X, uniform independent Y and ideal tables. -/
def game (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    PMF (Outcome2 Password Entropy Result) :=
  (Gamma2Model.game passwords adversary).map (enrich source)
end

end TwoChainModel

/-! Actual adjacent B/A query values for both known-pair chain directions. -/
namespace RoundBlocks
open Gamma2Model TwoChainModel
variable {Password Entropy : Type}

theorem forward_step (password : Password) (tables : Tables Password Entropy)
    (fuel start : Nat) (state : State) (bound : start + (fuel + 1) ≤ 12) :
    execute tables (forward password (fuel + 1) start state bound) =
      let round : Fin 12 := ⟨start, by omega⟩
      let salt := tables.b (round, state.2)
      let key := tables.a (password, salt)
      let mask := tables.h (key, round, state.2)
      let rest := execute tables (forward password fuel (start + 1) (state.2, state.1 ^^^ mask) (by omega))
      ((rest.1.1, [.b round state.2, .a password salt, .h key round state.2] ++ rest.1.2),
        [.b round state.2, .a password salt, .h key round state.2] ++ rest.2) := by
  simp only [forward, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, execute_pure, answer, BitVec.xor_eq,
    List.append_nil, List.cons_append, List.nil_append]

attribute [local irreducible] forward finalize

theorem forward_block (password : Password) (tables : Tables Password Entropy)
    (fuel start : Nat) (state : State) (bound : start + fuel ≤ 12) (index : Nat) (inside : index < fuel) :
    ∃ right : Half,
      (execute tables (forward password fuel start state bound)).2.getD (3 * index) fallbackPoint =
        Point.b ⟨start + index, by omega⟩ right ∧
      (execute tables (forward password fuel start state bound)).2.getD (3 * index + 1) fallbackPoint =
        Point.a password (tables.b (⟨start + index, by omega⟩, right)) := by
  induction fuel generalizing start state index with
  | zero => omega
  | succ fuel ih =>
    cases index with
    | zero =>
      refine ⟨state.2, ?_, ?_⟩ <;> rw [forward_step] <;> rfl
    | succ index =>
      let round : Fin 12 := ⟨start, by omega⟩
      let nextState : State := (state.2, state.1 ^^^ tables.h
        (tables.a (password, tables.b (round, state.2)), round, state.2))
      obtain ⟨right, atB, atA⟩ := ih (start + 1) nextState (by omega) index (by omega)
      have sameRound : start + 1 + index = start + (index + 1) := by omega
      refine ⟨right, ?_, ?_⟩
      · rw [forward_step]
        have arithmetic : 3 * (index + 1) = 3 * index + 3 := by omega
        rw [arithmetic]
        simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
        simpa only [sameRound] using atB
      · rw [forward_step]
        have arithmetic : 3 * (index + 1) + 1 = (3 * index + 1) + 3 := by omega
        rw [arithmetic]
        simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
        simpa only [sameRound] using atA

theorem backward_block (password : Password) (tables : Tables Password Entropy)
    (fuel : Nat) (state : State) (bound : fuel ≤ 12) (index : Nat) (inside : index < fuel) :
    ∃ right : Half,
      (execute tables (finalize password fuel state bound)).2.getD (3 * index) fallbackPoint =
        Point.b ⟨fuel - 1 - index, by omega⟩ right ∧
      (execute tables (finalize password fuel state bound)).2.getD (3 * index + 1) fallbackPoint =
        Point.a password (tables.b (⟨fuel - 1 - index, by omega⟩, right)) := by
  induction fuel generalizing state index with
  | zero => omega
  | succ fuel ih =>
    cases index with
    | zero =>
      refine ⟨state.1, ?_, ?_⟩ <;> rw [FinalCut.finalize_step] <;> rfl
    | succ index =>
      let round : Fin 12 := ⟨fuel, by omega⟩
      let nextState : State := (state.2 ^^^ tables.h
        (tables.a (password, tables.b (round, state.1)), round, state.1), state.1)
      obtain ⟨right, atB, atA⟩ := ih nextState (by omega) index (by omega)
      have sameRound : fuel - 1 - index = (fuel + 1) - 1 - (index + 1) := by omega
      refine ⟨right, ?_, ?_⟩
      · rw [FinalCut.finalize_step]
        have arithmetic : 3 * (index + 1) = 3 * index + 3 := by omega
        rw [arithmetic]
        simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
        simpa only [sameRound] using atB
      · rw [FinalCut.finalize_step]
        have arithmetic : 3 * (index + 1) + 1 = (3 * index + 1) + 3 := by omega
        rw [arithmetic]
        simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
        simpa only [sameRound] using atA

end RoundBlocks

end
end MhfeLean
