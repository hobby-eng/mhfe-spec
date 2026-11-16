import MhfeLean.Chapters.ChainCompletion
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.ChainMonitoring
import MhfeLean.Chapters.KnownPairResampling
import MhfeLean.Chapters.OracleModel

namespace MhfeLean
noncomputable section

/-! # Lemma K2: intersections of the two chains
-/

/-!
A causal query machine obtained directly from an OracleComp chain. Nodes retain
its actual pending continuation and ordinal. Proof-only materialization uses the
same tables; the observer's machine itself has no table argument.
-/
namespace ProgramNodes
open Gamma2Model ChainMonitor ScanCoverage CompletePaths
variable {Password Entropy Result : Type}

structure Node (Password Entropy Result : Type) where
  ordinal : Nat
  query : Point Password Entropy
  continuation : spec Password Entropy query → OracleComp (spec Password Entropy) Result

def view (program : OracleComp (spec Password Entropy) Result) :
    Option (Σ query : Point Password Entropy, spec Password Entropy query → OracleComp (spec Password Entropy) Result) :=
  OracleComp.construct (fun _ => none) (fun point next _ => some ⟨point, next⟩) program

def initial (ordinal : Nat) (program : OracleComp (spec Password Entropy) Result) :
    Option (Node Password Entropy Result) :=
  (view program).map fun item => ⟨ordinal, item.1, item.2⟩

def machine : Machine Password Entropy (Node Password Entropy Result) where
  point := Node.query
  next := fun node answer => initial (node.ordinal + 1) (node.continuation answer)

variable (tables : Tables Password Entropy) (program : OracleComp (spec Password Entropy) Result)

def nodes : Nat → List (Node Password Entropy Result) :=
  OracleComp.construct (fun _ => fun _ => [])
    (fun point next recurse => fun ordinal =>
      ⟨ordinal, point, next⟩ :: recurse (answer tables point) (ordinal + 1)) program

theorem initial_is_head (ordinal : Nat) :
    (nodes tables program ordinal).head? = initial ordinal program := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih => rfl

theorem point_trace (ordinal : Nat) :
    (nodes tables program ordinal).map Node.query = (execute tables program).2 := by
  induction program using OracleComp.inductionOn generalizing ordinal with
  | pure result => rfl
  | query_bind point next ih =>
    change point :: (nodes tables (next (answer tables point)) (ordinal + 1)).map Node.query =
      (execute tables (ask point >>= next)).2
    simp only [ih, execute_bind, execute_ask, List.singleton_append]

theorem ordinal_at (ordinal index : Nat) (within : index < (nodes tables program ordinal).length) :
    (nodes tables program ordinal)[index].ordinal = ordinal + index := by
  induction program using OracleComp.inductionOn generalizing ordinal index with
  | pure result => simp only [nodes, OracleComp.construct_pure, List.length_nil] at within; omega
  | query_bind point next ih =>
    cases index with
    | zero => rfl
    | succ index =>
      change index + 1 < (Node.mk ordinal point next :: nodes tables (next (answer tables point)) (ordinal + 1)).length at within
      have inside : index < (nodes tables (next (answer tables point)) (ordinal + 1)).length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using within
      change (nodes tables (next (answer tables point)) (ordinal + 1))[index].ordinal = ordinal + (index + 1)
      rw [ih (answer tables point) (ordinal + 1) index inside]
      omega

/-- The materialized chain includes its true terminal transition. -/
theorem closed (ordinal : Nat) : Closed machine tables (nodes tables program ordinal) := by
  induction program using OracleComp.inductionOn generalizing ordinal with
  | pure result => trivial
  | query_bind point next ih =>
    have head := initial_is_head tables (next (answer tables point)) (ordinal + 1)
    have recursive := ih (answer tables point) (ordinal + 1)
    change Closed machine tables (Node.mk ordinal point next :: nodes tables (next (answer tables point)) (ordinal + 1))
    cases tail : nodes tables (next (answer tables point)) (ordinal + 1) with
    | nil =>
      change initial (ordinal + 1) (next (answer tables point)) = none
      rw [tail] at head
      exact head.symm
    | cons first later =>
      change initial (ordinal + 1) (next (answer tables point)) = some first ∧ Closed machine tables (first :: later)
      rw [tail] at head recursive
      exact ⟨head.symm, recursive⟩

end ProgramNodes

/-! Causal monitor coverage for any actual OracleComp chain in a complete shared trace. -/
namespace ProgramCoverage
open Gamma2Model G2 ProgramNodes
open ChainMonitor ScanCoverage CompletePaths MonitorScan
variable {Password Entropy Result : Type}

theorem closed_follows {NodeType : Type} (machine : Machine Password Entropy NodeType)
    (tables : Tables Password Entropy) (items : List NodeType)
    (closed : Closed machine tables items) : Follows machine tables items := by
  induction items with
  | nil => trivial
  | cons first later ih =>
    cases later with
    | nil => trivial
    | cons second rest => exact ⟨closed.1, ih closed.2⟩

theorem unique_ordinal (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result)
    (first second : Node Password Entropy Result) (firstMember : first ∈ nodes tables program 0)
    (secondMember : second ∈ nodes tables program 0) (equal : first.ordinal = second.ordinal) :
    first = second := by
  obtain ⟨i, hi, atFirst⟩ := List.getElem_of_mem firstMember
  obtain ⟨j, hj, atSecond⟩ := List.getElem_of_mem secondMember
  have firstOrdinal := ordinal_at tables program 0 i hi
  have secondOrdinal := ordinal_at tables program 0 j hj
  rw [atFirst] at firstOrdinal
  rw [atSecond] at secondOrdinal
  have sameIndex : i = j := by omega
  have sameNode : (nodes tables program 0)[i] = (nodes tables program 0)[j] := by cases sameIndex; rfl
  exact atFirst.symm.trans (sameNode.trans atSecond)

variable [DecidableEq Password] [DecidableEq Entropy]

/-- The selector is an operational machine; only the witness node is described using fixed tables. -/
theorem covered (tables : Tables Password Entropy)
    (chainProgram : OracleComp (spec Password Entropy) Result)
    (fullProgram : OracleComp (spec Password Entropy) Unit) (run : Run (Point Password Entropy))
    (trace : (execute tables fullProgram).2 = run.queries)
    (size : run.count = (execute tables chainProgram).2.length)
    (pointShape : ∀ index, index < run.count →
      run.point index = (execute tables chainProgram).2.getD index fallbackPoint)
    (clean : ¬ Early run) (index : Nat) (within : index < run.count) :
    ∃ history,
      (execute tables (monitor ProgramNodes.machine (fun node => decide (node.ordinal = index))
        fullProgram (initial 0 chainProgram) [])).1 =
      some ((nodes tables chainProgram 0)[index]'(by
        have lengths := congrArg List.length (point_trace tables chainProgram 0)
        simp only [List.length_map] at lengths
        omega), history) := by
  let items := nodes tables chainProgram 0
  have lengths : items.length = run.count := by
    have equality := congrArg List.length (point_trace tables chainProgram 0)
    simpa only [List.length_map, ← size] using equality
  have inside : index < items.length := by omega
  let selected := items[index]'inside
  have selectedMember : selected ∈ items := List.getElem_mem inside
  have selectedOrdinal : selected.ordinal = index := by
    simpa only [Nat.zero_add] using ordinal_at tables chainProgram 0 index inside
  have actualPoint (i : Nat) (inside : i < items.length) : run.point i = (items[i]'inside).query := by
    rw [pointShape i (by omega), ← point_trace tables chainProgram 0]
    rw [← List.getElem_eq_getD (h := by simpa only [List.length_map] using inside) fallbackPoint]
    simp only [List.getElem_map]
    rfl
  have present : ∀ node ∈ items, ProgramNodes.machine.point node ∈ (execute tables fullProgram).2 := by
    intro node found
    obtain ⟨i, hi, atNode⟩ := List.getElem_of_mem found
    have member := run.complete i (by omega)
    rw [actualPoint i hi, atNode, ← trace] at member
    exact member
  have ordered : items.Pairwise (fun a b =>
      (execute tables fullProgram).2.idxOf (ProgramNodes.machine.point a) <
      (execute tables fullProgram).2.idxOf (ProgramNodes.machine.point b)) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj before
    change (execute tables fullProgram).2.idxOf (items[i]'hi).query <
      (execute tables fullProgram).2.idxOf (items[j]'hj).query
    rw [← actualPoint i hi, ← actualPoint j hj, trace]
    exact all_ordered run clean i j before (by omega)
  have targetSelected : decide (selected.ordinal = index) = true := decide_eq_true selectedOrdinal
  have targetOnly : ∀ node ∈ items, decide (node.ordinal = index) = true → node = selected := by
    intro node found marked
    exact unique_ordinal tables chainProgram node selected found selectedMember
      ((of_decide_eq_true marked).trans selectedOrdinal.symm)
  obtain ⟨history, found⟩ := target_covered ProgramNodes.machine
    (fun node => decide (node.ordinal = index)) tables (execute tables fullProgram).2 []
    items selected selectedMember targetSelected targetOnly
    (closed_follows _ _ _ (closed tables chainProgram 0)) present ordered
    (by intro node _; simp only [List.not_mem_nil, not_false_eq_true])
  have nonempty : items ≠ [] := by intro empty; rw [empty] at selectedMember; cases selectedMember
  have initialEqual : initial 0 chainProgram = some (items.head nonempty) := by
    rw [← initial_is_head]
    exact List.head?_eq_some_head nonempty
  rw [← initialEqual, ← monitor_scans] at found
  exact ⟨history, found⟩

end ProgramCoverage

/-!
Replay two causal stopping prefixes against one consistent table, then answer
the earlier selected B query. A query-history guard certifies that the later
selected B query remains unread. No full table is supplied to the program.
-/
namespace ReplayPair
open Gamma2Model TraceProgram G3Fresh
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]
abbrev BInput := Fin 12 × Half
abbrev Recorded (Password Entropy : Type) := Option BInput × List (Point Password Entropy)

def choose (first second : Recorded Password Entropy) : Option (BInput × BInput) :=
  match first.1, second.1 with
  | some p, some q => if first.2.length < second.2.length then some (p, q) else some (q, p)
  | _, _ => none

def past (first second : Recorded Password Entropy) (early : BInput) :=
  first.2 ++ second.2 ++ [embedB early]

def program (first second : OracleComp (spec Password Entropy) (Option BInput)) :
    OracleComp (spec Password Entropy) (BInput × Option Half) := do
  let left ← withTrace first
  let right ← withTrace second
  match choose left right with
  | none => pure ((0, 0), none)
  | some (early, later) =>
    let old ← ask (.b early.1 early.2)
    if embedB later ∈ past left right early then pure ((0, 0), none)
    else pure (later, some old)

/-- Proof-only deterministic description of the same execution. -/
def described (tables : Tables Password Entropy) (first second : Recorded Password Entropy) :
    (BInput × Option Half) × List (Point Password Entropy) :=
  match choose first second with
  | none => (((0, 0), none), first.2 ++ second.2)
  | some (early, later) =>
    (if embedB later ∈ past first second early then ((0, 0), none)
      else (later, some (tables.b early)), past first second early)

theorem execution (tables : Tables Password Entropy)
    (first second : OracleComp (spec Password Entropy) (Option BInput)) :
    execute tables (program first second) = described tables (execute tables first) (execute tables second) := by
  simp only [program, execute_bind, execute_withTrace]
  cases chosen : choose (execute tables first) (execute tables second) with
  | none => simp only [chosen, execute_pure, described, List.append_nil]
  | some pair =>
    rcases pair with ⟨early, later⟩
    simp only [chosen, execute_bind, execute_ask, described]
    by_cases cached : embedB later ∈ past (execute tables first) (execute tables second) early
    · simp only [past, List.append_assoc] at cached ⊢
      simp only [if_pos cached, execute_pure, List.append_nil]
      rfl
    · simp only [past, List.append_assoc] at cached ⊢
      simp only [if_neg cached, execute_pure, List.append_nil, answer]
      rfl

/-- The explicit history guard guarantees freshness for every table, with no no-Early premise. -/
theorem certificate (tables : Tables Password Entropy)
    (first second : OracleComp (spec Password Entropy) (Option BInput))
    (enabled : (execute tables (program first second)).1.2 ≠ none) :
    embedB (execute tables (program first second)).1.1 ∉ (execute tables (program first second)).2 := by
  rw [execution] at enabled ⊢
  unfold described at enabled ⊢
  cases chosen : choose (execute tables first) (execute tables second) with
  | none => simp only [chosen] at enabled; exact False.elim (enabled rfl)
  | some pair =>
    rcases pair with ⟨early, later⟩
    simp only [chosen] at enabled ⊢
    by_cases cached : embedB later ∈ past (execute tables first) (execute tables second) early
    · simp only [if_pos cached] at enabled
      exact False.elim (enabled rfl)
    · simpa only [if_neg cached] using cached

end ReplayPair

/-! Extract a salt input from the causal query machine's actual selected query. -/
namespace ProgramObserver
open Gamma2Model ProgramNodes ProgramCoverage
open ChainMonitor G3Fresh ReplayPair
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

def saltInput : Point Password Entropy → Option BInput
  | .b round right => some (round, right)
  | _ => none

def picked : Option (Node Password Entropy Result × List (Point Password Entropy)) → Option BInput
  | none => none
  | some (node, _) => saltInput node.query

def stop (chainProgram : OracleComp (spec Password Entropy) Result)
    (fullProgram : OracleComp (spec Password Entropy) Unit) (index : Nat) :=
  monitor ProgramNodes.machine (fun node => decide (node.ordinal = index))
    fullProgram (initial 0 chainProgram) []

def observe (chainProgram : OracleComp (spec Password Entropy) Result)
    (fullProgram : OracleComp (spec Password Entropy) Unit) (index : Nat) :=
  picked <$> stop chainProgram fullProgram index

/-- Every successful B selection has an original-prefix transcript and an unread selected point. -/
theorem prefix_fresh (tables : Tables Password Entropy)
    (chainProgram : OracleComp (spec Password Entropy) Result)
    (fullProgram : OracleComp (spec Password Entropy) Unit) (index : Nat) (point : BInput)
    (selected : (execute tables (observe chainProgram fullProgram index)).1 = some point) :
    (execute tables (observe chainProgram fullProgram index)).2 <+: (execute tables fullProgram).2 ∧
      embedB point ∉ (execute tables (observe chainProgram fullProgram index)).2 := by
  have mapped : execute tables (observe chainProgram fullProgram index) =
      (picked (execute tables (stop chainProgram fullProgram index)).1,
        (execute tables (stop chainProgram fullProgram index)).2) := by rw [observe, execute_map]
  rw [mapped] at selected ⊢
  generalize hit : (execute tables (stop chainProgram fullProgram index)).1 = result at selected
  cases result with
  | none => cases selected
  | some pair =>
    rcases pair with ⟨node, history⟩
    have query : node.query = embedB point := by
      cases shape : node.query with
      | a password salt => simp only [picked, shape, saltInput] at selected; cases selected
      | h key round right => simp only [picked, shape, saltInput] at selected; cases selected
      | g entropy => simp only [picked, shape, saltInput] at selected; cases selected
      | b round right =>
        simp only [picked, shape, saltInput] at selected
        have equal : (round, right) = point := Option.some.inj selected
        rw [← equal]
        rfl
    have details := information ProgramNodes.machine (fun node => decide (node.ordinal = index)) tables
      fullProgram (initial 0 chainProgram) [] node history hit
    have fresh := details.2.1
    rw [details.1] at fresh
    simp only [List.nil_append, ProgramNodes.machine] at fresh
    obtain ⟨later, trace⟩ := trace_prefix ProgramNodes.machine (fun node => decide (node.ordinal = index)) tables
      fullProgram (initial 0 chainProgram) [] node history hit
    refine ⟨⟨node.query :: later, trace.symm⟩, ?_⟩
    rw [← query]
    exact fresh

/-- Actual no-Early chain chronology guarantees that the salt observer succeeds. -/
theorem covered (tables : Tables Password Entropy)
    (chainProgram : OracleComp (spec Password Entropy) Result)
    (fullProgram : OracleComp (spec Password Entropy) Unit) (run : G2.Run (Point Password Entropy))
    (trace : (execute tables fullProgram).2 = run.queries)
    (size : run.count = (execute tables chainProgram).2.length)
    (pointShape : ∀ i, i < run.count → run.point i = (execute tables chainProgram).2.getD i fallbackPoint)
    (clean : ¬ G2.Early run) (index : Nat) (within : index < run.count) (point : BInput)
    (isSalt : run.point index = embedB point) :
    (execute tables (observe chainProgram fullProgram index)).1 = some point := by
  obtain ⟨history, selected⟩ := ProgramCoverage.covered tables chainProgram fullProgram run
    trace size pointShape clean index within
  have lengths := congrArg List.length (point_trace tables chainProgram 0)
  simp only [List.length_map] at lengths
  have inside : index < (nodes tables chainProgram 0).length := by omega
  have actual : ((nodes tables chainProgram 0)[index]'inside).query = embedB point := by
    rw [← isSalt, pointShape index within, ← point_trace tables chainProgram 0]
    rw [← List.getElem_eq_getD (h := by simpa only [List.length_map] using inside) fallbackPoint]
    simp only [List.getElem_map]
  rw [observe, execute_map]
  change picked (execute tables (stop chainProgram fullProgram index)).1 = some point
  rw [stop, selected]
  simp only [picked, actual, embedB, saltInput]

end ProgramObserver

/-! The source Cross event refers to actual A points of different rounds in the two chains. -/
namespace CrossModel
open Gamma2Model TwoChainModel RoundBlocks G3Fresh
variable {Password Entropy Result : Type}

def bIndex (direction : Bool) (round : Fin 12) : Nat :=
  if direction then 3 * round.val else 3 * (11 - round.val)

def actualA (out : Outcome2 Password Entropy Result) (direction : Bool) (round : Fin 12) :
    Point Password Entropy :=
  (run out direction).point (bIndex direction round + 1)

def actualB (out : Outcome2 Password Entropy Result) (direction : Bool) (round : Fin 12) :
    Point Password Entropy :=
  (run out direction).point (bIndex direction round)

def Cross (out : Outcome2 Password Entropy Result) : Prop :=
  ∃ first second : Fin 12, first ≠ second ∧ actualA out true first = actualA out false second

def chainProgram (source : State) (password : Password) (container : State) (direction : Bool) :
    OracleComp (spec Password Entropy) (State × List (Point Password Entropy)) :=
  if direction then forward password 12 0 source (by omega) else finalize password 12 container (by omega)

attribute [local irreducible] forward finalize

variable (source : State) (password : Password) (container : State)
  (tables : Tables Password Entropy) (adversary : State → OracleComp (spec Password Entropy) Result)
  (direction : Bool)

/-- The per-chain run uses exactly the points emitted by that actual owner computation. -/
theorem run_point (index : Nat) :
    (run (enrich source (outcome password container tables adversary)) direction).point index =
      (execute tables (chainProgram source password container direction)).2.getD index fallbackPoint := by
  cases direction <;> simp only [run, enrich, outcome, chainProgram, Bool.false_eq_true, ↓reduceIte]
  · rw [finalize_trace]
  · rw [forward_trace]

theorem run_size :
    (run (enrich source (outcome password container tables adversary)) direction).count =
      (execute tables (chainProgram source password container direction)).2.length := by
  cases direction <;> simp only [run, enrich, outcome, chainProgram, Bool.false_eq_true, ↓reduceIte]
  · rw [finalize_trace]
  · rw [forward_trace]

/-- A points expose the B output as their salt, irrespective of A-output collisions. -/
theorem block (round : Fin 12) :
    ∃ right : Half,
      actualB (enrich source (outcome password container tables adversary)) direction round = Point.b round right ∧
      actualA (enrich source (outcome password container tables adversary)) direction round =
        Point.a password (tables.b (round, right)) := by
  cases direction with
  | false =>
    obtain ⟨right, atB, atA⟩ := backward_block password tables 12 container (by omega) (11 - round.val) (by have := round.isLt; omega)
    have sameRound : 12 - 1 - (11 - round.val) = round.val := by have := round.isLt; omega
    refine ⟨right, ?_, ?_⟩
    · rw [actualB, run_point]
      simpa only [chainProgram, bIndex, Bool.false_eq_true, ↓reduceIte, sameRound, Fin.eta] using atB
    · rw [actualA, run_point]
      simpa only [chainProgram, bIndex, Bool.false_eq_true, ↓reduceIte, sameRound, Fin.eta] using atA
  | true =>
    obtain ⟨right, atB, atA⟩ := forward_block password tables 12 0 source (by omega) round.val round.isLt
    refine ⟨right, ?_, ?_⟩
    · rw [actualB, run_point]
      simpa only [chainProgram, bIndex, ↓reduceIte, Nat.zero_add, Fin.eta] using atB
    · rw [actualA, run_point]
      simpa only [chainProgram, bIndex, ↓reduceIte, Nat.zero_add, Fin.eta] using atA

/-- Different source rounds give different B inputs even if their salt answers coincide. -/
theorem inputs_different (first second : Fin 12) (left right : Half) (different : first ≠ second) :
    (first, left) ≠ (second, right) := by
  intro equal
  exact different (congrArg Prod.fst equal)

set_option maxRecDepth 4096 in
/-- Number of ordered pairs of different rounds. -/
theorem pair_count : Fintype.card { pair : Fin 12 × Fin 12 // pair.1 ≠ pair.2 } = 132 := by decide

end CrossModel

/-! Replay-prefix completeness without any table-reading selector or no-Early conditioning. -/
namespace ReplayCoverage
open Gamma2Model ReplayPair G3Fresh
variable {Password Entropy : Type}

theorem embed_injective : Function.Injective (embedB : BInput → Point Password Entropy) := by
  rintro ⟨r, right⟩ ⟨s, other⟩ equal
  exact Prod.ext (Point.b.inj equal).1 (Point.b.inj equal).2

/-- The late point is absent from both replayed prefixes and the added earlier query. -/
theorem guard (first second : Recorded Password Entropy) (shared : List (Point Password Entropy))
    (p q : BInput) (firstChosen : first.1 = some p) (secondChosen : second.1 = some q)
    (firstPrefix : first.2 <+: shared) (secondPrefix : second.2 <+: shared)
    (firstFresh : embedB p ∉ first.2) (secondFresh : embedB q ∉ second.2) (different : p ≠ q) :
    ∃ early later, choose first second = some (early, later) ∧
      embedB later ∉ past first second early := by
  have pointsDifferent : (embedB p : Point Password Entropy) ≠ embedB q :=
    fun equal => different (embed_injective equal)
  by_cases shorter : first.2.length < second.2.length
  · refine ⟨p, q, ?_, ?_⟩
    · simp only [choose, firstChosen, secondChosen, if_pos shorter]
    · have savedPrefix := List.prefix_of_prefix_length_le firstPrefix secondPrefix (Nat.le_of_lt shorter)
      simp only [past, List.mem_append, List.mem_singleton, not_or]
      exact ⟨⟨fun found => secondFresh (savedPrefix.subset found), secondFresh⟩, pointsDifferent.symm⟩
  · refine ⟨q, p, ?_, ?_⟩
    · simp only [choose, firstChosen, secondChosen, if_neg shorter]
    · have savedPrefix := List.prefix_of_prefix_length_le secondPrefix firstPrefix (by omega)
      simp only [past, List.mem_append, List.mem_singleton, not_or]
      exact ⟨⟨firstFresh, fun found => firstFresh (savedPrefix.subset found)⟩, pointsDifferent⟩

variable [DecidableEq Password] [DecidableEq Entropy]

/-- A genuine salt collision passes the causal fresh test regardless of which stop came first. -/
theorem matching_result (tables : Tables Password Entropy)
    (first second : OracleComp (spec Password Entropy) (Option BInput))
    (shared : List (Point Password Entropy)) (p q : BInput)
    (firstChosen : (execute tables first).1 = some p)
    (secondChosen : (execute tables second).1 = some q)
    (firstPrefix : (execute tables first).2 <+: shared)
    (secondPrefix : (execute tables second).2 <+: shared)
    (firstFresh : embedB p ∉ (execute tables first).2)
    (secondFresh : embedB q ∉ (execute tables second).2) (different : p ≠ q)
    (collision : tables.b p = tables.b q) :
    (execute tables (program first second)).1.2 =
      some (tables.b (execute tables (program first second)).1.1) := by
  obtain ⟨early, later, chosen, fresh⟩ := guard (execute tables first) (execute tables second)
    shared p q firstChosen secondChosen firstPrefix secondPrefix firstFresh secondFresh different
  have equalValues : tables.b early = tables.b later := by
    simp only [choose, firstChosen, secondChosen] at chosen
    by_cases shorter : (execute tables first).2.length < (execute tables second).2.length
    · rw [if_pos shorter] at chosen
      have pair := Option.some.inj chosen
      have first := congrArg Prod.fst pair
      have second := congrArg Prod.snd pair
      dsimp only at first second
      simpa only [← first, ← second] using collision
    · rw [if_neg shorter] at chosen
      have pair := Option.some.inj chosen
      have first := congrArg Prod.fst pair
      have second := congrArg Prod.snd pair
      dsimp only at first second
      simpa only [← first, ← second] using collision.symm
  simp only [execution, described, chosen, if_neg fresh, equalValues]

end ReplayCoverage

/-! One unconditional 2^-128 bound for the later of two causally selected salt queries. -/
namespace ReplayProbability
open Gamma2Model G3Programs G3Fresh
open ReplayPair OracleProjection FocusedExecution
open OracleTree OptionalFresh EnabledProjection
open TableFactors GameExpectation MomentTools
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]

def matching (answer : Half) : Finset Half := {answer}

variable (first second : OracleComp (spec Password Entropy) (Option BInput))

def focusedPair
    (others : OthersB Password Entropy) :=
  focused (focusB others.1 others.2.1 others.2.2) (program first second)

theorem fresh (others : OthersB Password Entropy) : EnabledFresh (focusedPair first second others) := by
  apply enabled_fresh (focusB others.1 others.2.1 others.2.2)
    (fun b => (⟨others.1, b, others.2.1, others.2.2⟩ : Tables Password Entropy))
    (by intro table point; cases point <;> rfl) (program first second)
    embedB (identifiesB others)
  intro table
  exact certificate _ first second

def event (tables : Tables Password Entropy) : Bool :=
  rawHit (focusedPair first second (tables.a, tables.h, tables.g)) matching tables.b

theorem result (tables : Tables Password Entropy) :
    (evaluate tables.b (focusedPair first second (tables.a, tables.h, tables.g))).1 =
      (execute tables (program first second)).1 := by
  exact result_eq (focusB tables.a tables.h tables.g) tables.b tables
    (by intro point; cases point <;> rfl) (program first second)

theorem collision_covered (tables : Tables Password Entropy)
    (first second : OracleComp (spec Password Entropy) (Option BInput))
    (shared : List (Point Password Entropy)) (p q : BInput)
    (firstChosen : (execute tables first).1 = some p)
    (secondChosen : (execute tables second).1 = some q)
    (firstPrefix : (execute tables first).2 <+: shared)
    (secondPrefix : (execute tables second).2 <+: shared)
    (firstFresh : embedB p ∉ (execute tables first).2)
    (secondFresh : embedB q ∉ (execute tables second).2) (different : p ≠ q)
    (collision : tables.b p = tables.b q) : event first second tables = true := by
  have chosen := ReplayCoverage.matching_result tables first second shared p q
    firstChosen secondChosen firstPrefix secondPrefix firstFresh secondFresh different collision
  simp only [event, rawHit, result]
  rw [chosen]
  simp only [optionalSet, matching, Finset.mem_singleton, decide_true]

variable [Fintype Password] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

/-- No conditioning on no Early: the pair observer always has probability at most 2^-128. -/
theorem probability (first second : OracleComp (spec Password Entropy) (Option BInput)) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if event first second tables then 1 else 0) ≤ (1 : ENNReal) / (2 ^ 128 : ENNReal) := by
  have bound := G3Probability.averaged sampleTables
    (PMF.uniformOfFintype (OthersB Password Entropy))
    (fun others b => (⟨others.1, b, others.2.1, others.2.2⟩ : Tables Password Entropy)) factor_b
    (focusedPair first second) matching (event first second) (by intro others table; rfl)
    (fresh first second) (fun _ => 1) (by
      intro others table
      cases selected : (evaluate table (focusedPair first second others)).1.2 with
      | none => simp only [optionalSet, Finset.card_empty]; omega
      | some answer => simp only [optionalSet, matching, Finset.card_singleton, le_refl])
  simpa only [G3Probability.card_bits, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, constant] using bound

end ReplayProbability

/-! K2: actual per-chain order/distinctness and the exact 132/2^128 Cross bound. -/
namespace K2
open Gamma2Model TwoChainModel CrossModel
open G3Fresh G3Sums GameExpectation MomentTools
open G3Assembly
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] forward finalize

abbrev Pair := { pair : Fin 12 × Fin 12 // pair.1 ≠ pair.2 }

def observer (source : State) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (direction : Bool) (round : Fin 12) :=
  ProgramObserver.observe (chainProgram source password container direction)
    (TwoChainModel.fullProgram source password container adversary) (bIndex direction round)

def pairEvent (source : State) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (pair : Pair) :=
  ReplayProbability.event (observer source password container adversary true pair.val.1)
    (observer source password container adversary false pair.val.2)

/-- The actual A-point Cross event yields a collision test for one fixed pair of distinct rounds. -/
theorem covered (source : State) (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (cross : Cross (enrich source (outcome password container tables adversary)))
    (clean : ¬ Early2 (enrich source (outcome password container tables adversary))) :
    ∃ pair : Pair, pairEvent source password container adversary pair tables = true := by
  let out := enrich source (outcome password container tables adversary)
  obtain ⟨first, second, different, equalA⟩ := cross
  obtain ⟨left, bFirst, aFirst⟩ := block source password container tables adversary true first
  obtain ⟨right, bSecond, aSecond⟩ := block source password container tables adversary false second
  have collision : tables.b (first, left) = tables.b (second, right) := by
    rw [aFirst, aSecond] at equalA
    exact (Point.a.inj equalA).2
  have observed (direction : Bool) (round : Fin 12) (half : Half)
      (isB : actualB out direction round = Point.b round half) :
      (execute tables (observer source password container adversary direction round)).1 = some (round, half) := by
    apply ProgramObserver.covered tables (chainProgram source password container direction)
      (TwoChainModel.fullProgram source password container adversary) (run out direction)
      (full_trace source password container tables adversary)
      (run_size source password container tables adversary direction)
      (fun index _ => run_point source password container tables adversary direction index)
    · cases direction with
      | false => exact fun early => clean (Or.inr early)
      | true => exact fun early => clean (Or.inl early)
    · rw [run_count]
      cases direction <;> simp only [bIndex, Bool.false_eq_true, ↓reduceIte] <;> have := round.isLt <;> omega
    · exact isB
  have firstChosen := observed true first left bFirst
  have secondChosen := observed false second right bSecond
  have firstDetails := ProgramObserver.prefix_fresh tables
    (chainProgram source password container true) (TwoChainModel.fullProgram source password container adversary)
    (bIndex true first) (first, left) firstChosen
  have secondDetails := ProgramObserver.prefix_fresh tables
    (chainProgram source password container false) (TwoChainModel.fullProgram source password container adversary)
    (bIndex false second) (second, right) secondChosen
  refine ⟨⟨(first, second), different⟩, ?_⟩
  exact ReplayProbability.collision_covered tables
    (observer source password container adversary true first)
    (observer source password container adversary false second)
    (execute tables (TwoChainModel.fullProgram source password container adversary)).2
    (first, left) (second, right) firstChosen secondChosen firstDetails.1 secondDetails.1
    firstDetails.2 secondDetails.2 (inputs_different first second left right different) collision

omit [DecidableEq Password] [DecidableEq Entropy] in
/-- The inter-chain part of K2(2) requires Cross's exclusion; same-round equality is allowed. -/
theorem cross_distinct (out : Outcome2 Password Entropy Result) (notCross : ¬ Cross out)
    (first second : Fin 12) (different : first ≠ second) :
    actualA out true first ≠ actualA out false second :=
  fun equal => notCross ⟨first, second, different, equal⟩

noncomputable section
variable [Fintype Password] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

def test (out : Outcome2 Password Entropy Result) : Bool := by classical exact decide (Cross out ∧ ¬ Early2 out)

theorem conditional_bound (source : State) (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    moment sampleTables (fun tables => if test (enrich source (outcome password container tables adversary)) then 1 else 0) ≤
      (132 : ENNReal) / (2 ^ 128 : ENNReal) := by
  classical
  calc
    _ ≤ moment sampleTables (fun tables => ∑ pair : Pair,
        if pairEvent source password container adversary pair tables then 1 else 0) := by
      apply mono
      intro tables
      by_cases enabled : test (enrich source (outcome password container tables adversary)) = true
      · have details : Cross (enrich source (outcome password container tables adversary)) ∧
            ¬ Early2 (enrich source (outcome password container tables adversary)) := of_decide_eq_true enabled
        rw [enabled]
        exact one_le_indicator_sum _ (covered source password container tables adversary details.1 details.2)
      · have disabled := Bool.eq_false_iff.mpr enabled
        simp only [disabled, Bool.false_eq_true, ↓reduceIte, zero_le]
    _ = ∑ pair : Pair, moment sampleTables (fun tables =>
        if pairEvent source password container adversary pair tables then 1 else 0) := finite_sum _ _
    _ ≤ ∑ _ : Pair, (1 : ENNReal) / (2 ^ 128 : ENNReal) := by
      apply Finset.sum_le_sum
      intro pair _
      exact ReplayProbability.probability _ _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, pair_count, nsmul_eq_mul]
      simp [div_eq_mul_inv]

/-- K2(3) in the actual two-chain Delta2 game; no adversary-query budget is needed. -/
theorem cross_bound (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    ((TwoChainModel.game source passwords adversary).map test) true ≤
      (132 : ENNReal) / (2 ^ 128 : ENNReal) := by
  rw [TwoChainModel.game, PMF.map_comp, probability]
  calc
    _ ≤ moment (Gamma2Model.game passwords adversary) (fun _ => (132 : ENNReal) / (2 ^ 128 : ENNReal)) := by
      apply game_transfer
      intro password container
      rw [constant]
      exact conditional_bound source password container adversary
    _ = _ := constant _ _

/-- Independent private random coins preserve the source Cross bound. -/
theorem randomized_cross_bound {Strategy : Type} (coins : PMF Strategy) (source : State)
    (passwords : PMF Password)
    (adversary : Strategy → State → OracleComp (spec Password Entropy) Result) :
    ((coins.bind fun strategy => TwoChainModel.game source passwords (adversary strategy)).map test) true ≤
      (132 : ENNReal) / (2 ^ 128 : ENNReal) := by
  rw [probability, MomentTools.bind]
  apply bounded
  intro strategy
  rw [← probability]
  exact cross_bound source passwords (adversary strategy)

end
end K2

end
end MhfeLean
