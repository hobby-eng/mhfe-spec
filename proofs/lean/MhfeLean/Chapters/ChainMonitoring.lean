import MhfeLean.Chapters.OracleModel

namespace MhfeLean
noncomputable section

/-! # Stopping times and coverage of early chain queries
-/

/-! Cover each real Early execution by one of 35 causal stopping-hit events. -/

namespace EarlyHitCoverage

open Gamma2Model MhfeChain WalkProperties
open ChainMonitor ScanCoverage MhfeMonitorCoverage G2

variable {Password Entropy Result : Type}

/-- Different oracle families remain different even when argument bit strings coincide. -/
def kind : Point Password Entropy → Nat
  | .b _ _ => 0
  | .a _ _ => 1
  | .h _ _ _ => 2
  | .g _ => 3

/-- Concrete chain phases cycle B/A/H by their source stage. -/
theorem point_kind (password : Password) (cursor : Cursor) :
    kind (point password cursor : Point Password Entropy) = stage cursor % 3 := by
  cases cursor <;> simp [kind, point, stage, Nat.add_mod]

/-- The chronological chain preserves the same phase information. -/
theorem chronological_kind (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (index : Nat)
    (within : index < 36) :
    kind ((chronologicalRun password container tables adversary).point index) = index % 3 := by
  have inWalk : index < (walk password tables 36 (.salt 11 container)).length := by
    rw [full_walk_length password container tables adversary]
    exact within
  rw [chronological_point password container tables adversary index inWalk, point_kind,
    full_stage_at]

/-- Adjacent source points cannot coincide: their oracle families differ. -/
theorem adjacent_distinct (password : Password) (container : State)
    (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (index : Nat)
    (positive : 0 < index) (within : index < 36) :
    (chronologicalRun password container tables adversary).point index ≠
      (chronologicalRun password container tables adversary).point (index - 1) := by
  intro equal
  have families := congrArg kind equal
  rw [chronological_kind password container tables adversary index within,
    chronological_kind password container tables adversary (index - 1) (by omega)] at families
  omega

/-- Consecutive elements of a valid materialized path follow the real machine transition. -/
theorem follows_consecutive (machine : Machine Password Entropy Node)
    (tables : Tables Password Entropy) (nodes : List Node) (follows : Follows machine tables nodes)
    (index : Nat) (within : index + 1 < nodes.length) :
    machine.next nodes[index] (answer tables (machine.point nodes[index])) =
      some nodes[index + 1] := by
  induction index generalizing nodes with
  | zero =>
    cases nodes with
    | nil => simp only [List.length_nil] at within; omega
    | cons first later =>
      cases later with
      | nil => simp only [List.length_cons, List.length_nil] at within; omega
      | cons second remaining => exact follows.1
  | succ index ih =>
    cases nodes with
    | nil => simp only [List.length_nil] at within; omega
    | cons first later =>
      cases later with
      | nil => simp only [List.length_cons, List.length_nil] at within; omega
      | cons second remaining =>
        have inside : index + 1 < (second :: remaining).length := by
          simp only [List.length_cons] at within ⊢
          omega
        simpa only [List.getElem_cons_succ] using ih (second :: remaining) follows.2 inside

/-- At FirstEarly the next chain point is in the history saved before its predecessor's answer. -/
theorem firstEarly_stopping_hit [DecidableEq Password] [DecidableEq Entropy] (password : Password)
    (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (index : Nat)
    (first : FirstEarly.First (chronologicalRun password container tables adversary) index) :
    ∃ cursor history next,
      stage cursor = index - 1 ∧
      (execute tables (monitor (machine password) (fun node => decide (stage node = index - 1))
        (fullProgram password container adversary) (some (.salt 11 container)) [])).1 =
          some (cursor, history) ∧
      advance password cursor (answer tables (point password cursor)) = some next ∧
      point password next ∈ history := by
  let run := chronologicalRun password container tables adversary
  let nodes := walk password tables 36 (.salt 11 container)
  have size : nodes.length = 36 := full_walk_length password container tables adversary
  have positive := first.1
  have bounded : index < 36 := by simpa only [chronologicalRun_count] using first.2.1
  have priorWithin : index - 1 < nodes.length := by omega
  have nextWithin : index < nodes.length := by omega
  let cursor := nodes[index - 1]'priorWithin
  let next := nodes[index]'nextWithin
  obtain ⟨history, hit⟩ := firstEarly_target_covered password container tables adversary index first
  have details := information (machine password) (fun node => decide (stage node = index - 1))
    tables (fullProgram password container adversary) (some (.salt 11 container)) [] cursor history hit
  have historyIsTrace : history = (execute tables
      (monitor (machine password) (fun node => decide (stage node = index - 1))
        (fullProgram password container adversary) (some (.salt 11 container)) [])).2 := by
    simpa only [List.nil_append] using details.1
  have fresh : point password cursor ∉ history := details.2.1
  obtain ⟨later, trace⟩ := trace_prefix (machine password)
    (fun node => decide (stage node = index - 1)) tables (fullProgram password container adversary)
    (some (.salt 11 container)) [] cursor history hit
  have traceEq : run.queries = history ++ point password cursor :: later := by
    rw [fullProgram_trace, ← historyIsTrace] at trace
    exact trace
  have priorPoint : run.point (index - 1) = point password cursor :=
    chronological_point password container tables adversary (index - 1) priorWithin
  have priorTime : firstTime run (index - 1) = history.length := by
    simp only [firstTime, priorPoint]
    rw [traceEq, List.idxOf_append, if_neg fresh, List.idxOf_cons_self, Nat.zero_add]
  have before := FirstEarly.queried_before_previous run index first
    (adjacent_distinct password container tables adversary index positive bounded)
  rw [priorTime] at before
  have cached : run.point index ∈ history := by
    by_cases found : run.point index ∈ history
    · exact found
    · have tooLate : history.length ≤ firstTime run index := by
        simp only [firstTime]
        rw [traceEq, List.idxOf_append, if_neg found]
        omega
      omega
  have step := follows_consecutive (machine password) tables nodes
    (walk_follows password tables 36 (.salt 11 container)) (index - 1) (by omega)
  have nextIndex : index - 1 + 1 = index := by omega
  have stepped : advance password cursor (answer tables (point password cursor)) = some next := by
    simpa only [nextIndex, cursor, next, machine] using step
  refine ⟨cursor, history, next, ?_, hit, stepped, ?_⟩
  · exact full_stage_at password container tables (index - 1) priorWithin
  · rw [chronological_point password container tables adversary index nextWithin] at cached
    exact cached

/-- Early is covered by the union of the 35 stopping hits, without assuming global no-Early. -/
theorem early_covered [DecidableEq Password] [DecidableEq Entropy] (password : Password)
    (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (early : Early (chronologicalRun password container tables adversary)) :
    ∃ selected : Fin 35, ∃ cursor history next,
      stage cursor = selected.val ∧
      (execute tables (monitor (machine password) (fun node => decide (stage node = selected.val))
        (fullProgram password container adversary) (some (.salt 11 container)) [])).1 =
          some (cursor, history) ∧
      advance password cursor (answer tables (point password cursor)) = some next ∧
      point password next ∈ history := by
  obtain ⟨index, first⟩ := FirstEarly.exists_first _ early
  have positive := first.1
  have bounded : index < 36 := by simpa only [chronologicalRun_count] using first.2.1
  refine ⟨⟨index - 1, by omega⟩, ?_⟩
  exact firstEarly_stopping_hit password container tables adversary index first

end EarlyHitCoverage

/-!
Every successful selection follows a real complete chain, including runs that
are not first-Early witnesses. This prevents arbitrary stopping contexts from
escaping the private-chain prefix bounds used by G3.
-/

namespace CompletePaths

open Gamma2Model ChainMonitor MonitorScan MhfeChain

variable {Password Entropy Node : Type}

/-- A finite machine path includes the terminal transition to none. -/
def Closed (machine : Machine Password Entropy Node) (tables : Tables Password Entropy) :
    List Node → Prop
  | [] => True
  | [last] => machine.next last (answer tables (machine.point last)) = none
  | first :: second :: remaining =>
    machine.next first (answer tables (machine.point first)) = some second ∧
      Closed machine tables (second :: remaining)

/-- No active cursor means the observer cannot return a successful selection. -/
theorem scan_none [DecidableEq Password] [DecidableEq Entropy]
    (machine : Machine Password Entropy Node) (target : Node → Bool)
    (tables : Tables Password Entropy) (queries past : List (Point Password Entropy)) :
    scan machine target tables queries none past = none := by
  cases queries <;> rfl

/-- A successful replay cannot leave the complete materialized chain it started on. -/
theorem selected_member [DecidableEq Password] [DecidableEq Entropy]
    (machine : Machine Password Entropy Node) (target : Node → Bool)
    (tables : Tables Password Entropy) (queries past : List (Point Password Entropy)) (first : Node)
    (later : List Node) (closed : Closed machine tables (first :: later)) (chosen : Node)
    (history : List (Point Password Entropy))
    (hit : scan machine target tables queries (some first) past = some (chosen, history)) :
    chosen ∈ first :: later := by
  induction queries generalizing first later past with
  | nil => cases hit
  | cons queried remaining ih =>
    simp only [scan] at hit
    by_cases cached : machine.point first ∈ past
    · rw [if_pos cached] at hit
      cases hit
    · rw [if_neg cached] at hit
      by_cases stop : target first = true ∧ queried = machine.point first
      · rw [if_pos stop] at hit
        have equal := Option.some.inj hit
        cases equal
        exact List.mem_cons_self ..
      · rw [if_neg stop] at hit
        by_cases equal : queried = machine.point first
        · subst queried
          simp only [dite_true] at hit
          cases later with
          | nil =>
            change machine.next first (answer tables (machine.point first)) = none at closed
            rw [closed, scan_none] at hit
            cases hit
          | cons next rest =>
            change machine.next first (answer tables (machine.point first)) = some next ∧
              Closed machine tables (next :: rest) at closed
            rw [closed.1] at hit
            exact List.mem_cons_of_mem first (ih (past ++ [machine.point first]) next rest closed.2 hit)
        · simp only [dif_neg equal] at hit
          exact ih (past ++ [queried]) first later closed hit

/-- The materialized inverse walk contains its genuine terminal query at stage 35. -/
theorem closed_walk (password : Password) (tables : Tables Password Entropy) (fuel : Nat)
    (cursor : Cursor) (complete : stage cursor + fuel = 36) :
    Closed (machine password) tables (walk password tables fuel cursor) := by
  induction fuel generalizing cursor with
  | zero => have bounded := stage_bound cursor; omega
  | succ fuel ih =>
    rw [walk]
    cases stepped : advance password cursor (answer tables (point password cursor)) with
    | none => exact stepped
    | some next =>
      have progress := advance_stage password cursor next
        (answer tables (point password cursor)) stepped
      cases fuel with
      | zero => have bounded := stage_bound next; omega
      | succ previous =>
        change advance password cursor (answer tables (point password cursor)) = some next ∧
          Closed (machine password) tables (walk password tables (previous + 1) next)
        exact ⟨stepped, ih next (by omega)⟩

end CompletePaths

/-!
Every successful stopping history is bounded by the adversary's full trace and
the private chain prefix preceding the selected stage. No conditioning on a
first-Early event is used in these universal bounds.
-/

namespace HistoryPrefix

open Gamma2Model MhfeChain WalkProperties
open ChainMonitor MonitorScan CompletePaths
open MhfeMonitorCoverage

variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

/-- The first occurrence cannot be later than a known indexed occurrence. -/
theorem idxOf_le_at {Element : Type} [DecidableEq Element] (items : List Element) (index : Nat)
    (within : index < items.length) : items.idxOf items[index] ≤ index := by
  induction items generalizing index with
  | nil => simp only [List.length_nil] at within; omega
  | cons first remaining ih =>
    cases index with
    | zero => simp
    | succ index =>
      have inTail : index < remaining.length := by simpa only [List.length_cons,
        Nat.succ_lt_succ_iff] using within
      by_cases same : first = remaining[index]
      · simp [same]
      · simpa [List.idxOf_cons, same] using Nat.add_le_add_right (ih index inTail) 1

variable (password : Password) (container : State) (tables : Tables Password Entropy)
  (adversary : State → OracleComp (spec Password Entropy) Result)

/-- Every successful actual selection belongs to the complete inverse-chain walk. -/
theorem successful_member (target : Cursor → Bool) (chosen : Cursor)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password) target (fullProgram password container adversary) (some (.salt 11 container)) [])).1 = some (chosen, history)) :
    chosen ∈ walk password tables 36 (.salt 11 container) := by
  let nodes := walk password tables 36 (.salt 11 container)
  have shape : nodes = .salt 11 container :: nodes.tail := rfl
  have closed : Closed (machine password) tables nodes :=
    closed_walk password tables 36 (.salt 11 container) (by rfl)
  rw [shape] at closed
  rw [monitor_scans] at hit
  have member := selected_member (machine password) target tables
    (execute tables (fullProgram password container adversary)).2 []
    (.salt 11 container) nodes.tail closed chosen history hit
  rw [← shape] at member
  exact member

/-- A successful stage-j selection is the actual cursor at index j of the chain. -/
theorem successful_cursor (selected : Fin 35)
    (chosen : Cursor) (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password)
      (fun cursor => decide (stage cursor = selected.val))
      (fullProgram password container adversary) (some (.salt 11 container)) [])).1 =
        some (chosen, history)) :
    chosen = (walk password tables 36 (.salt 11 container))[selected.val]'(by
      rw [full_walk_length password container tables adversary]; omega) := by
  have member := successful_member password container tables adversary _ chosen history hit
  have details := information (machine password) (fun cursor => decide (stage cursor = selected.val))
    tables (fullProgram password container adversary) (some (.salt 11 container)) [] chosen history hit
  have sameStage : stage chosen = selected.val := of_decide_eq_true details.2.2
  have within : selected.val < (walk password tables 36 (.salt 11 container)).length := by
    rw [full_walk_length password container tables adversary]
    omega
  apply full_stage_injective password container tables chosen _ member (List.getElem_mem within)
  rw [full_stage_at]
  exact sameStage

/-- A fresh first occurrence precedes any known private occurrence of that point. -/
theorem prefix_from_index {Element : Type} [DecidableEq Element]
    (before chain history later : List Element) (value : Element) (index : Nat)
    (within : index < chain.length) (pointAt : chain[index]'within = value)
    (trace : before ++ chain = history ++ value :: later) (fresh : value ∉ history) :
    history <+: before ++ chain.take index := by
  have firstIndex : (before ++ chain).idxOf value = history.length := by
    rw [trace, List.idxOf_append, if_neg fresh, List.idxOf_cons_self, Nat.zero_add]
  have privateBound : chain.idxOf value ≤ index := by
    rw [← pointAt]
    exact idxOf_le_at chain index within
  have historyBound : history.length ≤ before.length + index := by
    rw [← firstIndex, List.idxOf_append]
    split
    · have bounded := List.idxOf_le_length (l := before) (a := value)
      omega
    · omega
  have takeHistory : (before ++ chain).take history.length = history := by
    rw [trace]
    exact List.take_left
  have boundedPrefix := List.take_prefix_take_left (l := before ++ chain) historyBound
  rw [takeHistory, List.take_length_add_append] at boundedPrefix
  exact boundedPrefix

set_option maxHeartbeats 1000000 in
/-- All saved queries precede the stage-j point's occurrence in private finalization. -/
theorem successful_prefix (selected : Fin 35) (chosen : Cursor)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password) (fun cursor => decide (stage cursor = selected.val)) (fullProgram password container adversary) (some (.salt 11 container)) [])).1 = some (chosen, history)) :
    history <+: (outcome password container tables adversary).adversaryQueries ++
      (outcome password container tables adversary).chain.take selected.val := by
  let nodes := walk password tables 36 (.salt 11 container)
  have inWalk : selected.val < nodes.length := by
    rw [full_walk_length password container tables adversary]
    omega
  have inMap : selected.val < (nodes.map (point password : Cursor → Point Password Entropy)).length := by
    simpa only [List.length_map] using inWalk
  have chosenAt := successful_cursor password container tables adversary selected chosen history hit
  have pointAt : (nodes.map (point password : Cursor → Point Password Entropy))[selected.val]'inMap =
      point password chosen := by
    simp only [List.getElem_map]
    rw [← chosenAt]
  have details := information (machine password) (fun cursor => decide (stage cursor = selected.val))
    tables (fullProgram password container adversary) (some (.salt 11 container)) [] chosen history hit
  have saved : history = (execute tables (monitor (machine password)
      (fun cursor => decide (stage cursor = selected.val))
      (fullProgram password container adversary) (some (.salt 11 container)) [])).2 := by
    simpa only [List.nil_append] using details.1
  have fresh : point password chosen ∉ history := details.2.1
  obtain ⟨later, trace⟩ := trace_prefix (machine password)
    (fun cursor => decide (stage cursor = selected.val)) tables
    (fullProgram password container adversary) (some (.salt 11 container)) [] chosen history hit
  rw [← saved] at trace
  have mapChain : nodes.map (point password : Cursor → Point Password Entropy) =
      (execute tables (finalize password 12 container (by omega))).1.2 :=
    walk_matches_finalize password tables 11 (by omega) container
  have completeTrace : (execute tables (adversary container)).2 ++
      nodes.map (point password : Cursor → Point Password Entropy) =
        history ++ point password chosen :: later := by
    rw [fullProgram_trace, chronologicalRun_queries, finalize_trace] at trace
    rw [mapChain]
    simp only [machine] at trace
    with_reducible exact trace
  have boundedPrefix := prefix_from_index (execute tables (adversary container)).2
    (nodes.map (point password : Cursor → Point Password Entropy)) history later
    (point password chosen) selected.val inMap pointAt completeTrace fresh
  rw [mapChain] at boundedPrefix
  simpa only [outcome] using boundedPrefix

end HistoryPrefix

/-!
Pointwise G3 matching-set bounds for every successful causal selection. The
bounds use final adversary query counts plus only the permitted private prefix.
-/

namespace StoppingCounts

open Gamma2Model MhfeChain ChainMonitor
open MhfeMonitorCoverage HistoryPrefix ChainMetadata
open MatchingSets QueryCounts

variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

variable (password : Password) (container : State) (tables : Tables Password Entropy)
  (adversary : State → OracleComp (spec Password Entropy) Result)

/-- The selected cursor's stage is fixed before its selected answer is read. -/
theorem selected_stage (selected : Fin 35) (chosen : Cursor)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password) (fun cursor => decide (stage cursor = selected.val)) (fullProgram password container adversary) (some (.salt 11 container)) [])).1 = some (chosen, history)) :
    stage chosen = selected.val := by
  exact of_decide_eq_true (information (machine password)
    (fun cursor => decide (stage cursor = selected.val)) tables
    (fullProgram password container adversary) (some (.salt 11 container)) [] chosen history hit).2.2

/-- Any matching query count is bounded by adversary and private-prefix counts. -/
theorem history_count (selected : Fin 35) (chosen : Cursor)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password) (fun cursor => decide (stage cursor = selected.val)) (fullProgram password container adversary) (some (.salt 11 container)) [])).1 = some (chosen, history))
    (predicate : Point Password Entropy → Bool) :
    history.countP predicate ≤
      (outcome password container tables adversary).adversaryQueries.countP predicate +
        ((outcome password container tables adversary).chain.take selected.val).countP predicate := by
  have bounded := (successful_prefix password container tables adversary selected chosen history hit).countP_le
    (p := predicate)
  simpa only [List.countP_append] using bounded

/-- At B_i the matching salts cost only real-password A queries and 11-i private queries. -/
theorem salt_budget (selected : Fin 35) (round : Fin 12) (state : State)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password) (fun cursor => decide (stage cursor = selected.val)) (fullProgram password container adversary) (some (.salt 11 container)) [])).1 = some (.salt round state, history)) :
    (values (saltValue password) history).card ≤
      (outcome password container tables adversary).adversaryQueries.countP (aFor password) +
        (11 - round.val) := by
  have position : 3 * (11 - round.val) = selected.val :=
    selected_stage password container tables adversary selected _ history hit
  have counted := history_count password container tables adversary selected _ history hit (aFor password)
  rw [← position] at counted
  have privateBound := private_a_bound password container tables adversary round
  exact (salt_card password history).trans (counted.trans (Nat.add_le_add_left privateBound _))

/-- At A_i the matching keys are bounded by final same-round H queries alone. -/
theorem key_budget (selected : Fin 35) (round : Fin 12) (state : State) (salt : Half)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password) (fun cursor => decide (stage cursor = selected.val)) (fullProgram password container adversary) (some (.salt 11 container)) [])).1 = some (.key round state salt, history)) :
    (values (keyValue round state.1) history).card ≤
      (outcome password container tables adversary).adversaryQueries.countP (hFor round) := by
  have position : 3 * (11 - round.val) + 1 = selected.val :=
    selected_stage password container tables adversary selected _ history hit
  have counted := history_count password container tables adversary selected _ history hit (hFor round)
  rw [← position, private_h_zero, Nat.add_zero] at counted
  exact (key_card round state.1 history).trans counted

/-- A selected H cursor has a following round; terminal H_0 cannot be selected. -/
theorem selected_mask_positive (selected : Fin 35) (round : Fin 12) (state : State) (key : Key)
    (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password) (fun cursor => decide (stage cursor = selected.val)) (fullProgram password container adversary) (some (.salt 11 container)) [])).1 = some (.mask round state key, history)) :
    0 < round.val := by
  have position : 3 * (11 - round.val) + 2 = selected.val :=
    selected_stage password container tables adversary selected _ history hit
  have bounded := selected.isLt
  omega

/-- At H_i the matching masks are bounded by final next-round B queries alone. -/
theorem mask_budget (selected : Fin 35)
    (round : Fin 12) (state : State) (key : Key) (history : List (Point Password Entropy))
    (hit : (execute tables (monitor (machine password)
      (fun cursor => decide (stage cursor = selected.val))
      (fullProgram password container adversary) (some (.salt 11 container)) [])).1 =
        some (.mask round state key, history)) :
    (values (maskValue ⟨round.val - 1, by omega⟩ state.2) history).card ≤
      (outcome password container tables adversary).adversaryQueries.countP
        (bFor ⟨round.val - 1, by omega⟩) := by
  have position : 3 * (11 - round.val) + 2 = selected.val :=
    selected_stage password container tables adversary selected _ history hit
  have positive := selected_mask_positive password container tables adversary selected round state key history hit
  have counted := history_count password container tables adversary selected _ history hit
    (bFor ⟨round.val - 1, by omega⟩)
  rw [← position, private_b_zero _ _ _ _ round positive, Nat.add_zero] at counted
  exact (mask_card ⟨round.val - 1, by omega⟩ state.2 history).trans counted

end StoppingCounts

end
end MhfeLean
