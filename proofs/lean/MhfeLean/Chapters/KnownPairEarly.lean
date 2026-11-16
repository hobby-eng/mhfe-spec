import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.Basic
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.KnownPairResampling
import MhfeLean.Chapters.OracleModel

namespace MhfeLean
noncomputable section

/-! # Lemma K3: forward and backward premature queries
-/

/-! Reversible round-index relabelling for reusing inverse-chain bounds on the forward chain. -/
namespace RoundFlip
open Gamma2Model TableFactors OracleProjection
variable {Password Entropy Result : Type}

def flipPoint : Point Password Entropy → Point Password Entropy
  | .a password salt => .a password salt
  | .b round right => .b round.rev right
  | .h key round right => .h key round.rev right
  | .g entropy => .g entropy

theorem point_involution (point : Point Password Entropy) : flipPoint (flipPoint point) = point := by
  cases point <;> simp only [flipPoint, Fin.rev_rev]

def flipTables (tables : Tables Password Entropy) : Tables Password Entropy :=
  ⟨tables.a, (fun point => tables.b (point.1.rev, point.2)),
    (fun point => tables.h (point.1, point.2.1.rev, point.2.2)), tables.g⟩

theorem table_involution (tables : Tables Password Entropy) :
    flipTables (flipTables tables) = tables := by
  cases tables
  simp only [flipTables, Fin.rev_rev]

/-- Relabel a query without changing its answer family or observing any function table. -/
def relabel (point : Point Password Entropy) :
    OracleComp (spec Password Entropy) (spec Password Entropy point) :=
  match point with
  | .a password salt => ask (.a password salt)
  | .b round right => ask (.b round.rev right)
  | .h key round right => ask (.h key round.rev right)
  | .g entropy => ask (.g entropy)

def flipProgram (program : OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Password Entropy) Result :=
  OracleComp.construct pure (fun point _ recurse => relabel point >>= recurse) program

theorem execute_relabel (tables : Tables Password Entropy) (point : Point Password Entropy) :
    execute tables (relabel point) = (answer (flipTables tables) point, [flipPoint point]) := by
  cases point <;> simp only [relabel, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, answer, flipTables, flipPoint]

/-- Results are retained and every query, including repeats, is relabelled bijectively. -/
theorem execution (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) :
    execute tables (flipProgram program) =
      ((execute (flipTables tables) program).1, (execute (flipTables tables) program).2.map flipPoint) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih =>
    change execute tables (relabel point >>= fun answer => flipProgram (next answer)) =
      ((execute (flipTables tables) (ask point >>= next)).1,
        (execute (flipTables tables) (ask point >>= next)).2.map flipPoint)
    simp only [execute_bind, execute_relabel, ih, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, List.singleton_append, List.map_cons]

/-- Uniform full-table sampling is invariant under this round-index permutation. -/
def tableEquiv : Tables Password Entropy ≃ Tables Password Entropy where
  toFun := flipTables
  invFun := flipTables
  left_inv := table_involution
  right_inv := table_involution

noncomputable section
variable [Fintype Password] [DecidableEq Password] [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm
local instance : Fintype (Tables Password Entropy) :=
  Fintype.ofEquiv (Quad Password Entropy) TableFactors.tableEquiv.symm
local instance : Nonempty (Tables Password Entropy) := ⟨TableFactors.tableEquiv.symm default⟩

theorem sampling : (sampleTables (Password := Password) (Entropy := Entropy)).map flipTables = sampleTables := by
  rw [sample_uniform]
  exact PMF.uniformOfFintype_map_of_bijective tableEquiv tableEquiv.bijective

end
end RoundFlip

/-! Forward query paths are inverse query paths with swapped halves and reversed round labels. -/
namespace ForwardInverse
open Gamma2Model TwoChainModel RoundFlip
variable {Password Entropy : Type}

def swap (state : State) : State := (state.2, state.1)

theorem swap_involution (state : State) : swap (swap state) = state := rfl

attribute [local irreducible] forward finalize

/-- Exact trace identity, including every query value and every repeated query. -/
theorem owner_trace (password : Password) (tables : Tables Password Entropy)
    (fuel : Nat) (state : State) (bound : fuel ≤ 12) :
    (execute (flipTables tables) (finalize password fuel (swap state) bound)).2 =
      ((execute tables (forward password fuel (12 - fuel) state (by omega))).2.map flipPoint) := by
  induction fuel generalizing state with
  | zero => simp only [finalize, forward, execute_pure, List.map_nil]
  | succ fuel ih =>
    let inverseRound : Fin 12 := ⟨fuel, by omega⟩
    let forwardRound : Fin 12 := ⟨12 - (fuel + 1), by omega⟩
    have roundEq : inverseRound.rev = forwardRound := by
      apply Fin.ext
      simp only [inverseRound, forwardRound, Fin.val_rev]
    have reverseEq : forwardRound.rev = inverseRound := by rw [← roundEq, Fin.rev_rev]
    dsimp only [inverseRound, forwardRound] at roundEq reverseEq
    have nextStart : 12 - (fuel + 1) + 1 = 12 - fuel := by omega
    rw [FinalCut.finalize_step password (flipTables tables) fuel (by omega) (swap state)]
    rw [RoundBlocks.forward_step password tables fuel (12 - (fuel + 1)) state (by omega)]
    have aFlip : (flipTables tables).a = tables.a := rfl
    have bFlip : (flipTables tables).b = fun point => tables.b (point.1.rev, point.2) := rfl
    have hFlip : (flipTables tables).h = fun point => tables.h (point.1, point.2.1.rev, point.2.2) := rfl
    simp only [swap, aFlip, bFlip, hFlip, roundEq, reverseEq, nextStart, List.map_append,
      List.map_cons, List.map_nil, flipPoint]
    let nextState : State := (state.2, state.1 ^^^ tables.h
      (tables.a (password, tables.b (forwardRound, state.2)), forwardRound, state.2))
    have recursive := ih nextState (by omega)
    dsimp only [swap, nextState, forwardRound] at recursive
    simp only [recursive]

end ForwardInverse

/-! Early depends on first query times and point identities, not on the halt field. -/
namespace TraceTransport
open G2
variable {α β : Type} [DecidableEq α] [DecidableEq β]

theorem idxOf_map (f : α → β) (injective : Function.Injective f) (items : List α) (point : α) :
    (items.map f).idxOf (f point) = items.idxOf point := by
  induction items with
  | nil => rfl
  | cons first later ih =>
    by_cases equal : first = point
    · subst first; simp
    · have different : f first ≠ f point := fun same => equal (injective same)
      simp [equal, different, ih]

/-- Equality of in-range first query times carries the recursive definition times too. -/
theorem defined_eq (first : Run α) (second : Run β) (count : first.count = second.count)
    (times : ∀ i, i < first.count → firstTime first i = firstTime second i) (index : Nat)
    (inside : index ≤ first.count) : definedTime first index = definedTime second index := by
  induction index with
  | zero => rfl
  | succ index ih =>
    simp only [definedTime]
    rw [ih (by omega), times index (by omega)]

/-- A bijective relabelling or a harmless appended suffix cannot alter Early. -/
theorem early_iff (first : Run α) (second : Run β) (count : first.count = second.count)
    (times : ∀ i, i < first.count → firstTime first i = firstTime second i) :
    Early first ↔ Early second := by
  constructor
  · rintro ⟨index, positive, inside, early⟩
    refine ⟨index, positive, by omega, ?_⟩
    rw [times index inside, defined_eq first second count times index (by omega)] at early
    exact early
  · rintro ⟨index, positive, inside, early⟩
    refine ⟨index, positive, by omega, ?_⟩
    rw [times index (by omega), defined_eq first second count times index (by omega)]
    exact early

end TraceTransport

/-! Concrete Early transports for the shared two-chain chronology. -/
namespace TraceRunMap
open Gamma2Model G2 TwoChainModel
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

theorem mapped (before chain : List (Point Password Entropy))
    (f : Point Password Entropy → Point Password Entropy) (injective : Function.Injective f) :
    Early (fromTrace (before.map f) (chain.map f)) ↔ Early (fromTrace before chain) := by
  apply Iff.symm
  apply TraceTransport.early_iff
  · simp only [fromTrace, List.length_map]
  · intro index inside
    change index < chain.length at inside
    have mappedInside : index < (chain.map f).length := by simpa only [List.length_map] using inside
    have pointEq : (chain.map f).getD index fallbackPoint = f (chain.getD index fallbackPoint) := by
      rw [← List.getElem_eq_getD (h := mappedInside) fallbackPoint]
      rw [← List.getElem_eq_getD (h := inside) fallbackPoint]
      simp only [List.getElem_map]
    simp only [firstTime, fromTrace]
    rw [pointEq, ← List.map_append, TraceTransport.idxOf_map f injective]

/-- Later backward finalization cannot change any already completed forward-chain first time. -/
theorem forward_suffix (out : Outcome2 Password Entropy Result) :
    Early (run out true) ↔ Early (fromTrace out.base.adversaryQueries out.forwardChain) := by
  apply TraceTransport.early_iff
  · rfl
  · intro index inside
    change index < out.forwardChain.length at inside
    have member : out.forwardChain.getD index fallbackPoint ∈ out.base.adversaryQueries ++ out.forwardChain := by
      apply List.mem_append_right
      rw [← List.getElem_eq_getD (h := inside) fallbackPoint]
      exact List.getElem_mem inside
    simp only [firstTime, run, queries, fromTrace, ↓reduceIte]
    rw [List.idxOf_append_of_mem member]

/-- A larger synthetic halt does not alter Early on the backward chain. -/
theorem backward_prefix (out : Outcome2 Password Entropy Result) :
    Early (run out false) ↔ Early (fromTrace (out.base.adversaryQueries ++ out.forwardChain) out.base.chain) := by
  apply TraceTransport.early_iff
  · rfl
  · intro index inside
    rfl

end TraceRunMap

/-! Reuse G3's inverse-chain Early bound for the actual forward chain. -/
namespace ForwardEarly
open Gamma2Model TwoChainModel G2
open RoundFlip ForwardInverse TraceRunMap
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

def shadow (container : State) (adversary : State → OracleComp (spec Password Entropy) Result) :
    State → OracleComp (spec Password Entropy) Result := fun _ => flipProgram (adversary container)

attribute [local irreducible] forward finalize

variable (source : State) (password : Password) (container : State)
  (tables : Tables Password Entropy) (adversary : State → OracleComp (spec Password Entropy) Result)

omit [DecidableEq Password] [DecidableEq Entropy] in
/-- The transformed run is exactly the original forward-prefix trace, pointwise relabelled. -/
theorem run_shape :
    chronologicalRun password (swap source) (flipTables tables) (shadow container adversary) =
      fromTrace ((execute tables (adversary container)).2.map flipPoint)
        ((execute tables (forward password 12 0 source (by omega))).2.map flipPoint) := by
  change fromTrace (execute (flipTables tables) (flipProgram (adversary container))).2
    (execute (flipTables tables) (finalize password 12 (swap source) (by omega))).1.2 = _
  rw [execution, table_involution, ← finalize_trace, owner_trace]

theorem early_iff :
    Early (run (enrich source (outcome password container tables adversary)) true) ↔
      Early (chronologicalRun password (swap source) (flipTables tables) (shadow container adversary)) := by
  rw [run_shape]
  have injective : Function.Injective (flipPoint : Point Password Entropy → Point Password Entropy) :=
    Function.Involutive.injective point_involution
  rw [mapped _ _ flipPoint injective]
  have sourceRun := forward_suffix (enrich source (outcome password container tables adversary))
  simpa only [enrich, outcome, forward_trace] using sourceRun

noncomputable def sourceTest (out : Outcome2 Password Entropy Result) : Bool := by
  classical
  exact decide (Early (run out true))

theorem test_eq :
    sourceTest (enrich source (outcome password container tables adversary)) =
      G3Sums.earlyTest (outcome password (swap source) (flipTables tables) (shadow container adversary)) := by
  classical
  apply Bool.decide_congr
  exact early_iff source password container tables adversary

end ForwardEarly

/-! Exact private forward-chain query accounting, including repeated salts. -/
namespace ForwardMetadata
open Gamma2Model TwoChainModel RoundBlocks
open ChainMetadata QueryCounts
variable {Password Entropy : Type}

def labels : Nat → Nat → List Label
  | 0, _ => []
  | fuel + 1, start => [.b start, .a, .h start] ++ labels fuel (start + 1)

attribute [local irreducible] forward finalize

variable (password : Password) (tables : Tables Password Entropy)

theorem actual_labels (fuel start : Nat) (state : State) (bound : start + fuel ≤ 12) :
    (execute tables (forward password fuel start state bound)).2.map label = labels fuel start := by
  induction fuel generalizing start state with
  | zero => simp only [forward, execute_pure, List.map_nil, labels]
  | succ fuel ih =>
    rw [forward_step]
    simp only [List.map_append, List.map_cons, List.map_nil, label, labels]
    rw [ih]

theorem a_count (source : State) :
    (execute tables (forward password 12 0 source (by omega))).2.countP isA = 12 := by
  rw [← count_a, actual_labels]
  decide

theorem b_count (source : State) (round : Fin 12) :
    (execute tables (forward password 12 0 source (by omega))).2.countP (bFor round) = 1 := by
  rw [← count_b, actual_labels]
  fin_cases round <;> decide

theorem h_count (source : State) (round : Fin 12) :
    (execute tables (forward password 12 0 source (by omega))).2.countP (hFor round) = 1 := by
  rw [← count_h, actual_labels]
  fin_cases round <;> decide

theorem total_h_count (source : State) :
    (execute tables (forward password 12 0 source (by omega))).2.countP isH = 12 := by
  rw [← h_partition]
  simp only [h_count, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem password_count [DecidableEq Password] (password : Password)
    (tables : Tables Password Entropy) (source : State) :
    (execute tables (forward password 12 0 source (by omega))).2.countP (aFor password) ≤ 12 := by
  calc
    _ ≤ _ := password_count_le password _
    _ = 12 := a_count password tables source

end ForwardMetadata

/-!
For backward-chain accounting, forward finalization is an explicit private
prefix. Its password dependence is retained; only base adversary counts may be
charged using independence of the hidden password.
-/
namespace BackwardEarly
open Gamma2Model TwoChainModel G2
open QueryCounts G3Programs G3Sums
variable {Password Entropy Result : Type}

attribute [local irreducible] forward finalize

def extended (source : State) (password : Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    State → OracleComp (spec Password Entropy) Result := fun container => do
  let result ← adversary container
  let _ ← forward password 12 0 source (by omega)
  pure result

variable (source : State) (password : Password) (container : State)
  (tables : Tables Password Entropy) (adversary : State → OracleComp (spec Password Entropy) Result)

theorem execution :
    execute tables (extended source password adversary container) =
      ((execute tables (adversary container)).1,
        (execute tables (adversary container)).2 ++
          (execute tables (forward password 12 0 source (by omega))).2) := by
  simp only [extended, execute_bind, execute_pure, List.append_nil]

theorem a_count [DecidableEq Password] (source : State) (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (execute tables (extended source password adversary container)).2.countP (aFor password) ≤
      (execute tables (adversary container)).2.countP (aFor password) + 12 := by
  rw [execution, List.countP_append]
  exact Nat.add_le_add_left (ForwardMetadata.password_count password tables source) _

theorem h_count :
    (execute tables (extended source password adversary container)).2.countP isH =
      (execute tables (adversary container)).2.countP isH + 12 := by
  rw [execution, List.countP_append, ForwardMetadata.total_h_count]

theorem b_count :
    (∑ index : Fin 11,
      (execute tables (extended source password adversary container)).2.countP (bFor (hNext index))) ≤
      (execute tables (adversary container)).2.countP isB + 11 := by
  simp only [execution, List.countP_append, Finset.sum_add_distrib, ForwardMetadata.b_count,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simpa only [Nat.cast_ofNat, Nat.mul_one] using
    Nat.add_le_add_right (nonterminal_b_count (execute tables (adversary container)).2) 11

variable [DecidableEq Password] [DecidableEq Entropy]

theorem early_iff (source : State) (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    Early (run (enrich source (outcome password container tables adversary)) false) ↔
      Early (chronologicalRun password container tables (extended source password adversary)) := by
  rw [TraceRunMap.backward_prefix]
  change Early (fromTrace ((execute tables (adversary container)).2 ++
      (execute tables (forward password 12 0 source (by omega))).1.2)
        (execute tables (finalize password 12 container (by omega))).1.2) ↔
    Early (fromTrace (execute tables (extended source password adversary container)).2
      (execute tables (finalize password 12 container (by omega))).1.2)
  rw [execution, forward_trace]

noncomputable def sourceTest (out : Outcome2 Password Entropy Result) : Bool := by
  classical
  exact decide (Early (run out false))

theorem test_eq (source : State) (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    sourceTest (enrich source (outcome password container tables adversary)) =
      earlyTest (outcome password container tables (extended source password adversary)) := by
  classical
  apply Bool.decide_congr
  exact early_iff source password container tables adversary

end BackwardEarly

/-! Round-index relabelling preserves the base adversary budgets exactly. -/
namespace RoundFlipCounts
open Gamma2Model RoundFlip QueryCounts
variable {Password Entropy : Type}

theorem b_count (trace : List (Point Password Entropy)) :
    (trace.map flipPoint).countP isB = trace.countP isB := by
  rw [List.countP_map]
  congr 1
  funext point
  cases point <;> rfl

theorem h_count (trace : List (Point Password Entropy)) :
    (trace.map flipPoint).countP isH = trace.countP isH := by
  rw [List.countP_map]
  congr 1
  funext point
  cases point <;> rfl

theorem a_count [DecidableEq Password] (password : Password) (trace : List (Point Password Entropy)) :
    (trace.map flipPoint).countP (aFor password) = trace.countP (aFor password) := by
  rw [List.countP_map]
  congr 1
  funext point
  cases point <;> rfl

end RoundFlipCounts

/-! Conditional two-chain Early bounds before averaging the independently hidden password. -/
namespace K3Conditional
open Gamma2Model TwoChainModel QueryCounts
open GameExpectation MomentTools
variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

def forwardBound (password : Password) (trace : List (Point Password Entropy)) : ENNReal :=
  ((12 * trace.countP (aFor password) + 66 + trace.countP isB : Nat) : ENNReal) / (2 ^ 128 : ENNReal) +
    (trace.countP isH : ENNReal) / (2 ^ 256 : ENNReal)

def backwardBound (password : Password) (trace : List (Point Password Entropy)) : ENNReal :=
  ((12 * (trace.countP (aFor password) + 12) + 66 : Nat) : ENNReal) / (2 ^ 128 : ENNReal) +
    ((trace.countP isH + 12 : Nat) : ENNReal) / (2 ^ 256 : ENNReal) +
    ((trace.countP isB + 11 : Nat) : ENNReal) / (2 ^ 128 : ENNReal)

theorem invariant_moment (f : Tables Password Entropy → ENNReal) :
    moment sampleTables f = moment sampleTables (fun tables => f (RoundFlip.flipTables tables)) := by
  calc
    _ = moment (sampleTables.map RoundFlip.flipTables) f := by rw [RoundFlip.sampling]
    _ = _ := moment_map _ _ _

theorem forward_counts (source : State) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    moment sampleTables (fun tables =>
      if ForwardEarly.sourceTest (enrich source (outcome password container tables adversary)) then 1 else 0) ≤
    moment sampleTables (fun tables => forwardBound password (execute tables (adversary container)).2) := by
  let f := fun tables => if G3Sums.earlyTest
    (outcome password (ForwardInverse.swap source) tables (ForwardEarly.shadow container adversary)) then (1 : ENNReal) else 0
  let g := fun tables => forwardBound password
    (execute tables (ForwardEarly.shadow container adversary (ForwardInverse.swap source))).2
  have bound : moment sampleTables f ≤ moment sampleTables g :=
    G3Assembly.union_counts password (ForwardInverse.swap source)
      (ForwardEarly.shadow container adversary)
  rw [invariant_moment f, invariant_moment g] at bound
  simpa only [f, g, ForwardEarly.test_eq, ForwardEarly.shadow,
    RoundFlip.execution, RoundFlip.table_involution, forwardBound,
    RoundFlipCounts.a_count, RoundFlipCounts.b_count, RoundFlipCounts.h_count] using bound

theorem backward_counts (source : State) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    moment sampleTables (fun tables =>
      if BackwardEarly.sourceTest (enrich source (outcome password container tables adversary)) then 1 else 0) ≤
    moment sampleTables (fun tables => backwardBound password (execute tables (adversary container)).2) := by
  simp only [BackwardEarly.test_eq]
  apply (G3Refined.union_counts_refined password container
    (BackwardEarly.extended source password adversary)).trans
  apply mono
  intro tables
  apply add_le_add
  · apply add_le_add
    · apply ENNReal.div_le_div_right
      exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 12
        (BackwardEarly.a_count source password container tables adversary)) 66
    · exact le_of_eq (by change ((execute tables (BackwardEarly.extended source password adversary container)).2.countP isH : ENNReal) / _ = _; rw [BackwardEarly.h_count])
  · apply ENNReal.div_le_div_right
    exact_mod_cast BackwardEarly.b_count source password container tables adversary

end K3Conditional

/-! Source K3: all two-chain Early events with the exact 287 accounting constant. -/
namespace K3
open Gamma2Model TwoChainModel QueryCounts
open GameExpectation MomentTools G3Assembly
open K3Conditional
variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

attribute [local irreducible] forward finalize

theorem indicator_or (p q : Prop) [Decidable p] [Decidable q] :
    (if p ∨ q then (1 : ENNReal) else 0) ≤ (if p then 1 else 0) + (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

def test (out : Outcome2 Password Entropy Result) : Bool := by classical exact decide (Early2 out)

theorem conditional_bound (source : State) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    moment sampleTables (fun tables => if test (enrich source (outcome password container tables adversary)) then 1 else 0) ≤
    moment sampleTables (fun tables =>
      ((24 * (execute tables (adversary container)).2.countP (aFor password) + 287 +
        2 * (execute tables (adversary container)).2.countP isB : Nat) : ENNReal) / (2 ^ 128 : ENNReal) +
      ((2 * (execute tables (adversary container)).2.countP isH + 12 : Nat) : ENNReal) / (2 ^ 256 : ENNReal)) := by
  classical
  calc
    _ ≤ moment sampleTables (fun tables =>
        (if ForwardEarly.sourceTest (enrich source (outcome password container tables adversary)) then 1 else 0) +
        (if BackwardEarly.sourceTest (enrich source (outcome password container tables adversary)) then 1 else 0)) := by
      apply mono
      intro tables
      simp only [test, ForwardEarly.sourceTest, BackwardEarly.sourceTest, decide_eq_true_eq]
      rw [Early2]
      split_ifs <;> simp_all
    _ ≤ moment sampleTables (fun tables => forwardBound password (execute tables (adversary container)).2) +
        moment sampleTables (fun tables => backwardBound password (execute tables (adversary container)).2) := by
      rw [MomentTools.add]
      exact add_le_add (forward_counts source password container adversary) (backward_counts source password container adversary)
    _ = _ := by
      rw [← MomentTools.add]
      congr 1
      funext tables
      simp only [forwardBound, backwardBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      ring

theorem early_bound (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) (p1 : ENNReal)
    (largest : ∀ password, passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ container tables, (execute tables (adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables, (execute tables (adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables, (execute tables (adversary container)).2.countP isH ≤ qH) :
    ((TwoChainModel.game source passwords adversary).map test) true ≤
      (24 * p1 * kA + 287 + 2 * qB) / (2 ^ 128 : ENNReal) + (2 * qH + 12) / (2 ^ 256 : ENNReal) := by
  rw [TwoChainModel.game, PMF.map_comp, probability]
  calc
    _ ≤ moment (game passwords adversary) (fun out =>
        ((24 * out.adversaryQueries.countP (aFor out.password) + 287 + 2 * out.adversaryQueries.countP isB : Nat) : ENNReal) /
          (2 ^ 128 : ENNReal) + ((2 * out.adversaryQueries.countP isH + 12 : Nat) : ENNReal) / (2 ^ 256 : ENNReal)) := by
      apply game_transfer
      exact fun password container => conditional_bound source password container adversary
    _ = (24 * moment (game passwords adversary)
        (fun out => (out.adversaryQueries.countP (aFor out.password) : ENNReal)) + 287 +
        2 * moment (game passwords adversary) (fun out => (out.adversaryQueries.countP isB : ENNReal))) /
        (2 ^ 128 : ENNReal) +
        (2 * moment (game passwords adversary) (fun out => (out.adversaryQueries.countP isH : ENNReal)) + 12) / (2 ^ 256 : ENNReal) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, MomentTools.add, div_const, constant]
      simp_rw [show ∀ (f : Outcome Password Entropy Result → ENNReal) (n : ENNReal),
        moment (Gamma2Model.game passwords adversary) (fun out => n * f out) =
          n * moment (Gamma2Model.game passwords adversary) f from
          fun f n => by simpa only [mul_comm] using mul_const (Gamma2Model.game passwords adversary) f n]

    _ ≤ _ := by
      apply add_le_add
      · apply ENNReal.div_le_div_right
        apply add_le_add
        · apply add_le_add _ le_rfl
          simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_left
            (gamma2_password_count passwords adversary p1 largest kA budgetA) 24
        · simpa only [mul_comm] using mul_le_mul_left (game_budget passwords adversary isB qB budgetB) 2
      · apply ENNReal.div_le_div_right
        apply add_le_add _ le_rfl
        simpa only [mul_comm] using mul_le_mul_left (game_budget passwords adversary isH qH budgetH) 2

/-- Independent private coins preserve the full source K3 bound. -/
theorem randomized_early_bound {Strategy : Type} (coins : PMF Strategy) (source : State)
    (passwords : PMF Password)
    (adversary : Strategy → State → OracleComp (spec Password Entropy) Result) (p1 : ENNReal)
    (largest : ∀ password, passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ strategy container tables, (execute tables (adversary strategy container)).2.countP isA ≤ kA)
    (budgetB : ∀ strategy container tables, (execute tables (adversary strategy container)).2.countP isB ≤ qB)
    (budgetH : ∀ strategy container tables, (execute tables (adversary strategy container)).2.countP isH ≤ qH) :
    ((coins.bind fun strategy => TwoChainModel.game source passwords (adversary strategy)).map test) true ≤
      (24 * p1 * kA + 287 + 2 * qB) / (2 ^ 128 : ENNReal) + (2 * qH + 12) / (2 ^ 256 : ENNReal) := by
  rw [probability, MomentTools.bind]
  apply bounded
  intro strategy
  rw [← probability]
  exact early_bound source passwords (adversary strategy) p1 largest kA qB qH
    (budgetA strategy) (budgetB strategy) (budgetH strategy)

end K3

end
end MhfeLean
