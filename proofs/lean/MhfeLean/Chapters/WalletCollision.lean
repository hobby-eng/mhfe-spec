/- long: the two-chain collision argument is kept with its stopping-time machinery. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Data.Finset.Lattice.Fold
import MhfeLean.Chapters.ChainCompletion
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.GenerationSurvival
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.ShortSources

namespace MhfeLean
noncomputable section

/-! # Lemma W4: key and state collisions with adaptive queries
-/

/-! Causal selection of the actual real chain's terminal H0 query inside the adversary run. -/
namespace W4Terminal
open Gamma2Model MhfeChain WalkProperties MhfeMonitorCoverage
open ChainMonitor MonitorScan ScanCoverage G2
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

def stopped (password : Password) (container : State) (adversary : State → OracleComp (spec Password Entropy) Result) :=
  monitor (machine password) (fun cursor => decide (stage cursor = 35)) (adversary container) (some (.salt 11 container)) []

variable (password : Password) (container : State) (tables : Tables Password Entropy)
  (adversary : State → OracleComp (spec Password Entropy) Result)

/-- Each chain point was read by the actual adversary if the last point was read and no Early occurred. -/
theorem all_queried (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (terminal : Queried (chronologicalRun password container tables adversary) 35) (index : Nat)
    (within : index < 36) : Queried (chronologicalRun password container tables adversary) index := by
  by_cases last : index = 35
  · simpa only [last] using terminal
  · exact (all_ordered _ notEarly index 35 (by omega) (by rw [chronologicalRun_count]; omega)).trans terminal

/-- A chronological first query already in the adversary prefix has exactly its original prefix position. -/
theorem queried_time (index : Nat)
    (queried : Queried (chronologicalRun password container tables adversary) index) :
    firstTime (chronologicalRun password container tables adversary) index =
      (execute tables (adversary container)).2.idxOf ((chronologicalRun password container tables adversary).point index) := by
  have member := (G4Order.queried_iff_mem _ _ index).mp queried
  change ((outcome password container tables adversary).adversaryQueries ++
    (outcome password container tables adversary).chain).idxOf _ = _
  exact List.idxOf_append_of_mem member

def stoppedAt (password : Password) (container : State) (adversary : State → OracleComp (spec Password Entropy) Result) (selectedIndex : Fin 36) :=
  monitor (machine password) (fun cursor => decide (stage cursor = selectedIndex.val)) (adversary container) (some (.salt 11 container)) []

/-- The actual no-Early completed chain is reached causally before its terminal answer. -/
theorem at_covered (selectedIndex : Fin 36)
    (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (terminal : Queried (chronologicalRun password container tables adversary) 35) :
    ∃ history, (execute tables (stoppedAt password container adversary selectedIndex)).1 =
      some ((walk password tables 36 (.salt 11 container))[selectedIndex.val]'(by
        rw [full_walk_length password container tables adversary]; omega),history) := by
  let nodes := walk password tables 36 (.salt 11 container)
  have size : nodes.length = 36 := full_walk_length password container tables adversary
  have inside : selectedIndex.val < nodes.length := by have := selectedIndex.isLt; omega
  let selected := nodes[selectedIndex.val]'inside
  let target := fun cursor => decide (stage cursor = selectedIndex.val)
  have selectedStage : stage selected = selectedIndex.val := full_stage_at password container tables selectedIndex.val inside
  have member : selected ∈ nodes := List.getElem_mem inside
  have onlyTarget : ∀ cursor ∈ nodes, target cursor = true → cursor = selected := by
    intro cursor found marked
    apply full_stage_injective password container tables cursor selected found member
    exact (of_decide_eq_true marked).trans selectedStage.symm
  have present : ∀ cursor ∈ nodes, (machine password).point cursor ∈ (execute tables (adversary container)).2 := by
    intro cursor found
    obtain ⟨index,within,equal⟩ := List.getElem_of_mem found
    have queried := all_queried password container tables adversary notEarly terminal index (by omega)
    have pointEq := chronological_point password container tables adversary index within
    rw [equal] at pointEq
    change point password cursor ∈ (execute tables (adversary container)).2
    rw [← pointEq]
    exact (G4Order.queried_iff_mem _ _ index).mp queried
  have ordered : nodes.Pairwise (fun a b =>
      (execute tables (adversary container)).2.idxOf ((machine password).point a) <
      (execute tables (adversary container)).2.idxOf ((machine password).point b)) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj before
    have qi := all_queried password container tables adversary notEarly terminal i (by omega)
    have qj := all_queried password container tables adversary notEarly terminal j (by omega)
    have order := all_ordered (chronologicalRun password container tables adversary) notEarly i j before (by rw [chronologicalRun_count]; omega)
    rw [queried_time password container tables adversary i qi, queried_time password container tables adversary j qj,
      chronological_point password container tables adversary i hi, chronological_point password container tables adversary j hj] at order
    exact order
  obtain ⟨history,hit⟩ := target_covered (machine password) target tables (execute tables (adversary container)).2 []
    nodes selected member (by simp only [target,selectedStage,decide_true]) onlyTarget
    (walk_follows password tables 36 _) present ordered (by intro cursor _; simp only [List.not_mem_nil, not_false_eq_true])
  have head : nodes.head (by intro empty; rw [empty] at member; cases member) = .salt 11 container := rfl
  rw [head, ← monitor_scans] at hit
  exact ⟨history,hit⟩

/-- The actual no-Early completed chain is reached causally before its terminal answer. -/
theorem covered
    (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (terminal : Queried (chronologicalRun password container tables adversary) 35) :
    ∃ history, (execute tables (stopped password container adversary)).1 =
      some ((walk password tables 36 (.salt 11 container))[35]'(by
        rw [full_walk_length password container tables adversary]; omega),history) := by
  simpa only [stopped, stoppedAt] using
    at_covered password container tables adversary ⟨35, by decide⟩ notEarly terminal

/-- The stopping program itself certifies freshness, without assuming no Early for this guarantee. -/
theorem fresh (cursor : Cursor) (history : List (Point Password Entropy))
    (hit : (execute tables (stopped password container adversary)).1 = some (cursor,history)) :
    point password cursor ∉ (execute tables (stopped password container adversary)).2 := by
  have details := information (machine password) (fun cursor => decide (stage cursor = 35)) tables
    (adversary container) (some (.salt 11 container)) [] cursor history hit
  rw [details.1] at details
  (try simp only [List.nil_append, machine] at details.2.1 ⊢)
  exact details.2.1

end W4Terminal

/-! Identify the terminal machine cursor with the actual pre-H0 inverse cut and output state. -/
namespace W4Cursor
open Gamma2Model MhfeChain FinalCut
variable {Password Entropy Result : Type}
attribute [local irreducible] prepare finalize

/-- The last concrete cursor retains exactly the state and key immediately preceding H0. -/
theorem last_prepare (password : Password) (tables : Tables Password Entropy) (round : Nat)
    (bound : round < 12) (state : State) :
    (walk password tables (3*(round+1)) (.salt ⟨round,bound⟩ state)).getLast? =
      some (.mask 0 (execute tables (prepare password round state bound)).1.state
        (execute tables (prepare password round state bound)).1.key) := by
  induction round generalizing state with
  | zero => simp [walk, advance, point, answer, prepare, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g]
  | succ round ih =>
    rw [prepare_step]
    dsimp only
    have fuel : 3*(round+1+1) = 3*(round+1)+3 := by omega
    rw [fuel]
    simp only [walk, advance, point, answer, Nat.succ_pos, dif_pos, Nat.add_sub_cancel,
      List.getLast?_cons_cons]
    exact ih (by omega) _

/-- The actual full inverse's first half is the cursor offset xor the fresh terminal mask. -/
theorem output (password : Password) (container : State) (tables : Tables Password Entropy)
    :
    let cut := (execute tables (prepare password 11 container (by omega))).1
    (execute tables (finalize password 12 container (by omega))).1.1.1 =
      cut.state.2 ^^^ tables.h (cut.key,0,cut.state.1) := by
  have same := finalized password tables 11 (by omega) container
  exact congrArg (fun result : State × List (Point Password Entropy) => result.1.1) same

/-- The last indexed cursor is the same actual pre-H0 cut, not just a query point with matching metadata. -/
theorem indexed_prepare (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (walk password tables 36 (.salt 11 container))[35]'(by rw [WalkProperties.full_walk_length password container tables adversary]; omega) =
      .mask 0 (execute tables (prepare password 11 container (by omega))).1.state
        (execute tables (prepare password 11 container (by omega))).1.key := by
  have last : (walk password tables 36 (.salt 11 container)).getLast? =
      some (.mask 0 (execute tables (prepare password 11 container (by omega))).1.state
        (execute tables (prepare password 11 container (by omega))).1.key) :=
    last_prepare password tables 11 (by omega) container
  have size := WalkProperties.full_walk_length password container tables adversary
  have indexed : (walk password tables 36 (.salt 11 container)).getLast? =
      some ((walk password tables 36 (.salt 11 container))[35]'(by omega)) := by
    rw [List.getLast?_eq_getElem?]
    rw [show (walk password tables 36 (.salt 11 container)).length-1 = 35 from by omega]
    exact List.getElem?_eq_getElem (by omega)
  rw [indexed] at last
  exact Option.some.inj last

end W4Cursor

/-! The real A0 selector names the actual final-cut key input, including repeated salts. -/
namespace W4CutKey
open Gamma2Model MhfeChain FinalCut
variable {Password Entropy : Type}
attribute [local irreducible] prepare

theorem key_value (password : Password) (tables : Tables Password Entropy) (round : Nat)
    (bound : round < 12) (state : State) :
    let cut := (execute tables (prepare password round state bound)).1
    cut.key = tables.a (password,tables.b (0,cut.state.1)) := by
  induction round generalizing state with
  | zero => simp [prepare, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, answer]
  | succ round ih =>
    rw [prepare_step]
    dsimp only
    exact ih (by omega) _

theorem key_member (password : Password) (tables : Tables Password Entropy) (round : Nat)
    (bound : round < 12) (state : State) :
    let cut := (execute tables (prepare password round state bound)).1
    Point.a password (tables.b (0,cut.state.1)) ∈ cut.before := by
  induction round generalizing state with
  | zero => simp [prepare, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, answer]
  | succ round ih =>
    rw [prepare_step]
    dsimp only
    exact List.mem_append_right _ (ih (by omega) _)

theorem cursor (password : Password) (tables : Tables Password Entropy) (round : Nat)
    (bound : round < 12) (state : State) :
    (walk password tables (3*(round+1)) (.salt ⟨round,bound⟩ state))[3*round+1]? =
      some (.key 0 (execute tables (prepare password round state bound)).1.state
        (tables.b (0,(execute tables (prepare password round state bound)).1.state.1))) := by
  induction round generalizing state with
  | zero => simp [walk, advance, point, answer, prepare, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g]
  | succ round ih =>
    rw [prepare_step]
    dsimp only
    have fuel : 3*(round+1+1) = 3*(round+1)+3 := by omega
    have index : 3*(round+1)+1 = (3*round+1)+3 := by omega
    rw [fuel,index]
    simp only [walk, advance, point, answer, Nat.succ_pos, dif_pos, Nat.add_sub_cancel,
      List.getElem?_cons_succ]
    exact ih (by omega) _

end W4CutKey

/-! Earlier completed inversions are covered by a cache-only first-half set with one entry per queried password. -/
namespace W4Cache
open Gamma2Model
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
abbrev Reads := List (RetainedAnswers.Read (spec Password Entropy))

def zeroTables : Tables Password Entropy := ⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

def cacheAnswer (reads : Reads (Password := Password) (Entropy := Entropy)) :
    (point : Point Password Entropy) → spec Password Entropy point :=
  RetainedAnswers.rebuild reads (answer zeroTables)

def cache (reads : Reads (Password := Password) (Entropy := Entropy)) : Tables Password Entropy :=
  ⟨fun pair => cacheAnswer reads (.a pair.1 pair.2),fun pair => cacheAnswer reads (.b pair.1 pair.2),
   fun triple => cacheAnswer reads (.h triple.1 triple.2.1 triple.2.2),fun e => cacheAnswer reads (.g e)⟩

theorem cache_lookup (reads : Reads (Password := Password) (Entropy := Entropy)) (point : Point Password Entropy) :
    answer (cache reads) point = cacheAnswer reads point := by cases point <;> rfl

/-- Cached entries retain their actual answers; unqueried points receive only fixed zero defaults. -/
theorem cached (reads : Reads (Password := Password) (Entropy := Entropy)) (tables : Tables Password Entropy)
    (valid : ∀ read ∈ reads, read.2 = answer tables read.1) (point : Point Password Entropy)
    (present : point ∈ reads.map Sigma.fst) : answer (cache reads) point = answer tables point := by
  rw [cache_lookup, cacheAnswer, RetainedAnswers.rebuild_value reads (answer tables) (answer zeroTables) valid,
    if_pos present]

/-- Execution with a cache is exact whenever all actual reads were already recorded. -/
theorem execute_cached (reads : Reads (Password := Password) (Entropy := Entropy)) (tables : Tables Password Entropy)
    (valid : ∀ read ∈ reads, read.2 = answer tables read.1)
    (program : OracleComp (spec Password Entropy) Result)
    (present : ∀ point ∈ (execute tables program).2, point ∈ reads.map Sigma.fst) :
    execute (cache reads) program = execute tables program := by
  have same := TranscriptErasure.execute_agree program (answer tables) (answer (cache reads))
    (fun point member => cached reads tables valid point (present point member))
  exact same

def passwords (queries : List (Point Password Entropy)) : Finset Password :=
  (queries.filterMap (fun point => match point with | .a p _ => some p | _ => none)).toFinset

def aCount (queries : List (Point Password Entropy)) : Nat :=
  (queries.filterMap (fun point => match point with | .a p _ => some p | _ => none)).length

def matching (container : State) (offset : Half) (reads : Reads (Password := Password) (Entropy := Entropy)) : Finset Half :=
  (passwords (reads.map Sigma.fst)).image fun password =>
    offset ^^^ (execute (cache reads) (finalize password 12 container (by omega))).1.1.1

theorem size (container : State) (offset : Half) (reads : Reads (Password := Password) (Entropy := Entropy)) :
    (matching container offset reads).card ≤ aCount (reads.map Sigma.fst) := by
  exact Finset.card_image_le.trans (List.toFinset_card_le _)

/-- A completed earlier chain is covered without any no-Early or distinct-salt assumption on that password. -/
theorem covered (container : State) (offset mask : Half) (reads : Reads (Password := Password) (Entropy := Entropy))
    (tables : Tables Password Entropy) (valid : ∀ read ∈ reads, read.2 = answer tables read.1)
    (password : Password) (queried : password ∈ passwords (reads.map Sigma.fst))
    (present : ∀ point ∈ (execute tables (finalize password 12 container (by omega))).2, point ∈ reads.map Sigma.fst)
    (equal : (execute tables (finalize password 12 container (by omega))).1.1.1 = offset ^^^ mask) :
    mask ∈ matching container offset reads := by
  unfold matching
  apply Finset.mem_image.mpr
  refine ⟨password,queried,?_⟩
  rw [execute_cached reads tables valid _ present, equal]
  simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end W4Cache

/-! A successful causal monitor retains exactly the pre-answer prefix of the original adversary trace. -/
namespace W4MonitorPrefix
open Gamma2Model ChainMonitor MonitorScan
variable {Password Entropy Node Result : Type} [DecidableEq Password] [DecidableEq Entropy]

theorem scan_split (machine : Machine Password Entropy Node) (target : Node → Bool)
    (tables : Tables Password Entropy) (queries past : List (Point Password Entropy))
    (pending : Option Node) (chosen : Node) (history : List (Point Password Entropy))
    (hit : scan machine target tables queries pending past = some (chosen,history)) :
    ∃ rest, past ++ queries = history ++ machine.point chosen :: rest := by
  induction queries generalizing pending past with
  | nil => cases hit
  | cons queried remaining ih =>
    cases pending with
    | none => cases hit
    | some node =>
      rw [scan] at hit
      dsimp only at hit
      by_cases cached : machine.point node ∈ past
      · rw [if_pos cached] at hit
        cases hit
      · rw [if_neg cached] at hit
        by_cases stop : target node = true ∧ queried = machine.point node
        · rw [if_pos stop] at hit
          have same := Option.some.inj hit
          cases same
          exact ⟨remaining,by rw [stop.2]⟩
        · rw [if_neg stop] at hit
          have selected := ih (past ++ [queried]) _ hit
          simpa only [List.append_assoc, List.singleton_append] using selected

variable (machine : Machine Password Entropy Node) (target : Node → Bool)
  (tables : Tables Password Entropy) (program : OracleComp (spec Password Entropy) Result)
  (pending : Option Node) (chosen : Node) (history : List (Point Password Entropy))

/-- Neither the retained prefix nor the selected point can depend on future oracle answers. -/
theorem split
    (hit : (execute tables (monitor machine target program pending [])).1 = some (chosen,history)) :
    ∃ rest, (execute tables program).2 = history ++ machine.point chosen :: rest := by
  rw [monitor_scans] at hit
  simpa only [List.nil_append] using scan_split machine target tables (execute tables program).2 [] pending chosen history hit

/-- The retained history ends at the first occurrence of the selected fresh query. -/
theorem before
    (hit : (execute tables (monitor machine target program pending [])).1 = some (chosen,history)) :
    history = (execute tables program).2.take ((execute tables program).2.idxOf (machine.point chosen)) := by
  have details := information machine target tables program pending [] chosen history hit
  obtain ⟨rest,trace⟩ := split machine target tables program pending chosen history hit
  rw [trace, List.idxOf_append]
  rw [if_neg details.2.1]
  simp only [List.idxOf_cons_self, Nat.zero_add]
  exact List.take_left.symm

/-- A successful observer uses no more A queries than the source adversary. -/
theorem a_budget
    (hit : (execute tables (monitor machine target program pending [])).1 = some (chosen,history)) :
    W4Cache.aCount history ≤ W4Cache.aCount (execute tables program).2 := by
  obtain ⟨rest,trace⟩ := split machine target tables program pending chosen history hit
  rw [trace]
  simp only [W4Cache.aCount, List.filterMap_append, List.length_append]
  exact Nat.le_add_right _ _

end W4MonitorPrefix

/-!
Replay two causal stopping prefixes against one consistent table, then answer
the earlier selected A query. A query-history guard certifies that the later
selected A query remains unread. No full table is supplied to the program.
-/
namespace W4KeyReplay
open Gamma2Model TraceProgram G3Fresh
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy] [Inhabited Password]
abbrev AInput (Password : Type) := Password × Half
abbrev Recorded (Password Entropy : Type) := Option (AInput Password) × List (Point Password Entropy)

def choose (first second : Recorded Password Entropy) :
    Option ((AInput Password) × (AInput Password)) :=
  match first.1, second.1 with
  | some p, some q => if first.2.length < second.2.length then some (p, q) else some (q, p)
  | _, _ => none

def past (first second : Recorded Password Entropy) (early : (AInput Password)) :=
  first.2 ++ second.2 ++ [embedA early]

def program (first second : OracleComp (spec Password Entropy) (Option (AInput Password))) :
    OracleComp (spec Password Entropy) ((AInput Password) × Option Key) := do
  let left ← withTrace first
  let right ← withTrace second
  match choose left right with
  | none => pure ((default, 0), none)
  | some (early, later) =>
    let old ← ask (.a early.1 early.2)
    if embedA later ∈ past left right early then pure ((default, 0), none)
    else pure (later, some old)

/-- Proof-only deterministic description of the same execution. -/
def described (tables : Tables Password Entropy) (first second : Recorded Password Entropy) :
    ((AInput Password) × Option Key) × List (Point Password Entropy) :=
  match choose first second with
  | none => (((default, 0), none), first.2 ++ second.2)
  | some (early, later) =>
    (if embedA later ∈ past first second early then ((default, 0), none)
      else (later, some (tables.a early)), past first second early)

theorem execution (tables : Tables Password Entropy)
    (first second : OracleComp (spec Password Entropy) (Option (AInput Password))) :
    execute tables (program first second) = described tables (execute tables first) (execute tables second) := by
  simp only [program, execute_bind, execute_withTrace]
  cases chosen : choose (execute tables first) (execute tables second) with
  | none => simp only [chosen, execute_pure, described, List.append_nil]
  | some pair =>
    rcases pair with ⟨early, later⟩
    simp only [chosen, execute_bind, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, described]
    by_cases cached : embedA later ∈ past (execute tables first) (execute tables second) early
    · simp only [past, List.append_assoc] at cached ⊢
      simp only [if_pos cached, execute_pure, List.append_nil]
      rfl
    · simp only [past, List.append_assoc] at cached ⊢
      simp only [if_neg cached, execute_pure, List.append_nil, answer]
      rfl

/-- The explicit history guard guarantees freshness for every table, with no no-Early premise. -/
theorem certificate (tables : Tables Password Entropy)
    (first second : OracleComp (spec Password Entropy) (Option (AInput Password)))
    (enabled : (execute tables (program first second)).1.2 ≠ none) :
    embedA (execute tables (program first second)).1.1 ∉ (execute tables (program first second)).2 := by
  rw [execution] at enabled ⊢
  unfold described at enabled ⊢
  cases chosen : choose (execute tables first) (execute tables second) with
  | none => simp only [chosen] at enabled; exact False.elim (enabled rfl)
  | some pair =>
    rcases pair with ⟨early, later⟩
    simp only [chosen] at enabled ⊢
    by_cases cached : embedA later ∈ past (execute tables first) (execute tables second) early
    · simp only [if_pos cached] at enabled
      exact False.elim (enabled rfl)
    · simpa only [if_neg cached] using cached

end W4KeyReplay

/-! A causal selection of the real chain's final A input, before its answer is read. -/
namespace W4RealA
open W4KeyReplay
open Gamma2Model MhfeChain ChainMonitor G3Fresh
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] FinalCut.prepare

def pick (password : Password) : Option (Cursor × List (Point Password Entropy)) → Option (AInput Password)
  | some (.key _ _ salt,_) => some (password,salt)
  | _ => none

def program (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Password Entropy) (Option (AInput Password)) :=
  pick password <$> W4Terminal.stoppedAt password container adversary ⟨34,by omega⟩

theorem certificate (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (input : AInput Password)
    (hit : (execute tables (program password container adversary)).1 = some input) :
    embedA input ∉ (execute tables (program password container adversary)).2 ∧
      (execute tables (program password container adversary)).2 <+: (execute tables (adversary container)).2 := by
  rw [program,execute_map] at hit ⊢
  cases stopped : (execute tables (W4Terminal.stoppedAt password container adversary ⟨34,by omega⟩)).1 with
  | none => simp only [stopped,pick] at hit; cases hit
  | some value =>
    rcases value with ⟨cursor,history⟩
    cases cursor with
    | salt round state => simp only [stopped,pick] at hit; cases hit
    | mask round state key => simp only [stopped,pick] at hit; cases hit
    | key round state salt =>
      have same : (password,salt) = input := by simpa only [stopped,pick,Option.some.injEq] using hit
      subst input
      have info := information (machine password) (fun cursor => decide (stage cursor = 34)) tables
        (adversary container) (some (.salt 11 container)) [] (.key round state salt) history stopped
      obtain ⟨rest,trace⟩ := trace_prefix (machine password) (fun cursor => decide (stage cursor = 34)) tables
        (adversary container) (some (.salt 11 container)) [] (.key round state salt) history stopped
      refine ⟨?_,?_⟩
      · rw [info.1] at info
        (try simp only [List.nil_append,machine,point,embedA] at info.2.1 ⊢)
        exact info.2.1
      · exact ⟨point password (.key round state salt) :: rest,trace.symm⟩

/-- Under the source guard this is the real final-cut A0 point, not an arbitrary A query. -/
theorem covered (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ G2.Early (chronologicalRun password container tables adversary))
    (terminal : G2.Queried (chronologicalRun password container tables adversary) 35) :
    let cut := (execute tables (FinalCut.prepare password 11 container (by omega))).1
    (execute tables (program password container adversary)).1 = some (password,tables.b (0,cut.state.1)) := by
  obtain ⟨history,hit⟩ := W4Terminal.at_covered password container tables adversary ⟨34,by omega⟩ notEarly terminal
  have cursor := W4CutKey.cursor password tables 11 (by omega) container
  change (walk password tables 36 (.salt 11 container))[34]? =
    some (.key 0 (execute tables (FinalCut.prepare password 11 container (by omega))).1.state
      (tables.b (0,(execute tables (FinalCut.prepare password 11 container (by omega))).1.state.1))) at cursor
  have size := WalkProperties.full_walk_length password container tables adversary
  rw [List.getElem?_eq_getElem (by omega)] at cursor
  have cursorEq := Option.some.inj cursor
  rw [cursorEq] at hit
  rw [program,execute_map]
  dsimp only
  rw [hit]
  rfl

end W4RealA

/-! Actual first occurrences of A points, with the exact pre-query prefixes they determine. -/
namespace W4ARecords
open Gamma2Model G3Fresh
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]
abbrev Input := Password × Half
abbrev Record := (Input (Password := Password)) × List (Point Password Entropy)

def records : List (Point Password Entropy) → List (Point Password Entropy) → List (Record (Password := Password) (Entropy := Entropy))
  | [], _ => []
  | queried :: remaining, past =>
    let rest := records remaining (past ++ [queried])
    match queried with
    | .a password salt => if queried ∈ past then rest else ((password,salt),past) :: rest
    | _ => rest

/-- There are no more fresh A selections than actual A calls, even when calls repeat. -/
theorem length (queries past : List (Point Password Entropy)) :
    (records queries past).length ≤ W4Cache.aCount queries := by
  induction queries generalizing past with
  | nil => exact le_refl _
  | cons queried remaining ih =>
    cases queried with
    | a password salt =>
      simp only [records]
      split_ifs
      · exact (ih (past ++ [.a password salt])).trans (by change W4Cache.aCount remaining ≤ W4Cache.aCount remaining + 1; omega)
      · simpa only [List.length_cons, W4Cache.aCount, List.filterMap_cons] using
          Nat.succ_le_succ (ih (past ++ [.a password salt]))
    | b round right => simpa only [records, W4Cache.aCount, List.filterMap_cons] using ih (past ++ [.b round right])
    | h key round right => simpa only [records, W4Cache.aCount, List.filterMap_cons] using ih (past ++ [.h key round right])
    | g entropy => simpa only [records, W4Cache.aCount, List.filterMap_cons] using ih (past ++ [.g entropy])

/-- Each selected point is fresh relative to its complete retained prefix. -/
theorem fresh (queries past : List (Point Password Entropy)) (record : Record (Password := Password) (Entropy := Entropy))
    (member : record ∈ records queries past) : embedA record.1 ∉ record.2 := by
  induction queries generalizing past with
  | nil => cases member
  | cons queried remaining ih =>
    cases queried <;> simp only [records] at member
    case a password salt =>
      split_ifs at member with cached
      · exact ih _ member
      · rcases List.mem_cons.mp member with same | later
        · subst record
          exact cached
        · exact ih _ later
    all_goals exact ih _ member

/-- A record's history is the original prefix immediately preceding its actual query. -/
theorem prefix_split (queries past : List (Point Password Entropy)) (record : Record (Password := Password) (Entropy := Entropy))
    (member : record ∈ records queries past) :
    ∃ before after, queries = before ++ embedA record.1 :: after ∧ record.2 = past ++ before := by
  induction queries generalizing past with
  | nil => cases member
  | cons queried remaining ih =>
    have later (included : record ∈ records remaining (past ++ [queried])) :
        ∃ before after, queried :: remaining = before ++ embedA record.1 :: after ∧ record.2 = past ++ before := by
      obtain ⟨before,after,trace,history⟩ := ih _ included
      exact ⟨queried :: before,after,by rw [trace]; rfl,by simpa only [List.append_assoc, List.singleton_append] using history⟩
    cases queried <;> simp only [records] at member
    case a password salt =>
      split_ifs at member
      · exact later member
      · rcases List.mem_cons.mp member with same | included
        · subst record
          exact ⟨[],remaining,rfl,(List.append_nil _).symm⟩
        · exact later included
    all_goals exact later member

/-- Every actually queried A point absent from the initial cache has one fresh selector record. -/
theorem membership (queries past : List (Point Password Entropy)) (input : Input (Password := Password)) :
    input ∈ (records queries past).map Prod.fst ↔ embedA input ∈ queries ∧ embedA input ∉ past := by
  induction queries generalizing past with
  | nil => simp [records]
  | cons queried remaining ih =>
    cases queried with
    | a password salt =>
      by_cases cached : Point.a password salt ∈ past
      · simp only [records, if_pos cached, ih, List.mem_append, not_or, List.mem_cons, List.not_mem_nil, not_false_eq_true, and_true]
        constructor
        · intro both; exact ⟨Or.inr both.1,both.2.1⟩
        · rintro ⟨same | later,notPast⟩
          · exact False.elim (notPast (same.symm ▸ cached))
          · refine ⟨later,notPast,?_⟩
            intro equal
            exact notPast (equal.symm ▸ cached)
      · simp only [records, if_neg cached, List.map_cons, List.mem_cons, ih,
          List.mem_append, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true]
        have equivalent : input = (password,salt) ↔ (embedA input : Point Password Entropy) = Point.a password salt := by
          rcases input with ⟨p,s⟩
          simp only [Prod.mk.injEq, embedA, Point.a.injEq]
        rw [equivalent]
        constructor
        · rintro (same | ⟨later,notPast,different⟩)
          · exact ⟨Or.inl same,by simpa only [same] using cached⟩
          · exact ⟨Or.inr later,notPast⟩
        · rintro ⟨same | later,notPast⟩
          · exact Or.inl same
          · by_cases same : (embedA input : Point Password Entropy) = Point.a password salt
            · exact Or.inl same
            · exact Or.inr ⟨later,notPast,same⟩
    | b round right =>
      have step := ih (past ++ [.b round right])
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at step
      simpa only [records, embedA, List.mem_cons, reduceCtorEq, false_or, or_false, not_false_eq_true, and_true] using step
    | h key round right =>
      have step := ih (past ++ [.h key round right])
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at step
      simpa only [records, embedA, List.mem_cons, reduceCtorEq, false_or, or_false, not_false_eq_true, and_true] using step
    | g entropy =>
      have step := ih (past ++ [.g entropy])
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at step
      simpa only [records, embedA, List.mem_cons, reduceCtorEq, false_or, or_false, not_false_eq_true, and_true] using step

end W4ARecords

/-! Causal selection of the i-th previously unqueried A point of the original adversary. -/
namespace W4NthA
open Gamma2Model G3Fresh W4ARecords
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

def candidate (queried : Point Password Entropy) (past : List (Point Password Entropy)) :
    Option (Input (Password := Password)) :=
  match queried with
  | .a p salt => if queried ∈ past then none else some (p,salt)
  | _ => none

theorem records_step (queried : Point Password Entropy) (remaining past : List (Point Password Entropy)) :
    records (queried :: remaining) past = match candidate queried past with
      | none => records remaining (past ++ [queried])
      | some input => (input,past) :: records remaining (past ++ [queried]) := by
  cases queried <;> simp only [records,candidate]
  split_ifs <;> rfl

/-- The selector never sees a random table; only the actual next query and past points. -/
def select (program : OracleComp (spec Password Entropy) Result) :
    Nat → List (Point Password Entropy) →
    OracleComp (spec Password Entropy) (Option (Record (Password := Password) (Entropy := Entropy))) :=
  OracleComp.construct (fun _ _ _ => pure none)
    (fun queried _ recurse index past => match candidate queried past with
      | some input => if index = 0 then pure (some (input,past)) else do
        let value ← ask queried
        recurse value (index-1) (past ++ [queried])
      | none => do
        let value ← ask queried
        recurse value index (past ++ [queried])) program

theorem select_pure (result : Result) (index : Nat) (past : List (Point Password Entropy)) :
    select (pure result) index past = pure none := rfl

theorem select_query (queried : Point Password Entropy)
    (next : spec Password Entropy queried → OracleComp (spec Password Entropy) Result)
    (index : Nat) (past : List (Point Password Entropy)) :
    select (ask queried >>= next) index past = (match candidate queried past with
      | some input => if index = 0 then pure (some (input,past)) else do
        let value ← ask queried
        select (next value) (index-1) (past ++ [queried])
      | none => do
        let value ← ask queried
        select (next value) index (past ++ [queried])) := rfl

attribute [local irreducible] select

/-- Selector results are exactly indexed records of actual first occurrences. -/
theorem execution (tables : Tables Password Entropy)
    (program : OracleComp (spec Password Entropy) Result) (index : Nat)
    (past : List (Point Password Entropy)) :
    (execute tables (select program index past)).1 = (records (execute tables program).2 past)[index]? := by
  induction program using OracleComp.inductionOn generalizing index past with
  | pure result => rw [select_pure,execute_pure]; rfl
  | query_bind queried next ih =>
    change (execute tables (select (ask queried >>= next) index past)).1 = _
    rw [select_query]
    change (execute tables (match candidate queried past with
      | some input => if index = 0 then pure (some (input,past)) else do
          let value ← ask queried
          select (next value) (index-1) (past ++ [queried])
      | none => do
          let value ← ask queried
          select (next value) index (past ++ [queried]))).1 =
      (records (queried :: (execute tables (next (answer tables queried))).2) past)[index]?
    rw [records_step]
    cases selected : candidate queried past with
    | none =>
      simp only [execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,List.singleton_append]
      exact ih (answer tables queried) index _
    | some input =>
      cases index with
      | zero => rfl
      | succ index =>
        simp only [Nat.succ_ne_zero,if_false,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,List.singleton_append,
          Nat.add_sub_cancel,List.getElem?_cons_succ]
        exact ih (answer tables queried) index _

/-- Successful execution's retained history is precisely its already emitted query prefix. -/
theorem history (tables : Tables Password Entropy) (program : OracleComp (spec Password Entropy) Result)
    (index : Nat) (past : List (Point Password Entropy)) (input : Input (Password := Password))
    (saved : List (Point Password Entropy))
    (hit : (execute tables (select program index past)).1 = some (input,saved)) :
    saved = past ++ (execute tables (select program index past)).2 := by
  induction program using OracleComp.inductionOn generalizing index past with
  | pure result => rw [select_pure,execute_pure] at hit; cases hit
  | query_bind queried next ih =>
    change (execute tables (select (ask queried >>= next) index past)).1 = _ at hit
    change saved = past ++ (execute tables (select (ask queried >>= next) index past)).2
    rw [select_query] at hit ⊢
    cases selected : candidate queried past with
    | none =>
      simp only [selected,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,List.singleton_append] at hit ⊢
      simpa only [List.append_assoc,List.singleton_append] using ih (answer tables queried) index (past ++ [queried]) hit
    | some other =>
      simp only [selected] at hit ⊢
      by_cases zero : index = 0
      · rw [if_pos zero,execute_pure] at hit ⊢
        have same := Option.some.inj hit
        cases same
        exact (List.append_nil _).symm
      · rw [if_neg zero] at hit ⊢
        simp only [execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,List.singleton_append] at hit ⊢
        simpa only [List.append_assoc,List.singleton_append] using ih (answer tables queried) (index-1) (past ++ [queried]) hit

/-- The index counts fresh A inputs; repeated calls cannot manufacture extra selector positions. -/
def program (adversary : OracleComp (spec Password Entropy) Result) (index : Nat) :
    OracleComp (spec Password Entropy) (Option (Input (Password := Password))) :=
  (fun output => output.map Prod.fst) <$> select adversary index []

/-- The actual stopped result is a queried A input with an unread answer. -/
theorem certificate (tables : Tables Password Entropy) (adversary : OracleComp (spec Password Entropy) Result)
    (index : Nat) (input : Input (Password := Password))
    (hit : (execute tables (program adversary index)).1 = some input) :
    embedA input ∉ (execute tables (program adversary index)).2 := by
  rw [program,execute_map] at hit ⊢
  dsimp only at hit ⊢
  cases selected : (execute tables (select adversary index [])).1 with
  | none => simp only [selected,Option.map_none] at hit; cases hit
  | some record =>
    have same : record.1 = input := by simpa only [selected,Option.map_some,Option.some.injEq] using hit
    have selectedAt := execution tables adversary index []
    rw [selected] at selectedAt
    have member : record ∈ records (execute tables adversary).2 [] := List.mem_of_getElem? selectedAt.symm
    have fresh := W4ARecords.fresh _ _ record member
    rw [history tables adversary index [] record.1 record.2 selected] at fresh
    simpa only [List.nil_append,same] using fresh

/-- A successful selector's full trace is an actual prefix of the source execution. -/
theorem prefix_of_hit (tables : Tables Password Entropy) (adversary : OracleComp (spec Password Entropy) Result)
    (index : Nat) (input : Input (Password := Password))
    (hit : (execute tables (program adversary index)).1 = some input) :
    (execute tables (program adversary index)).2 <+: (execute tables adversary).2 := by
  rw [program,execute_map] at hit ⊢
  dsimp only at hit ⊢
  cases selected : (execute tables (select adversary index [])).1 with
  | none => simp only [selected,Option.map_none] at hit; cases hit
  | some record =>
    have selectedAt := execution tables adversary index []
    rw [selected] at selectedAt
    have member : record ∈ records (execute tables adversary).2 [] := List.mem_of_getElem? selectedAt.symm
    obtain ⟨before,after,trace,saved⟩ := W4ARecords.prefix_split _ _ record member
    have emitted := history tables adversary index [] record.1 record.2 selected
    simp only [List.nil_append] at emitted saved
    rw [← emitted, saved]
    exact ⟨embedA record.1 :: after,trace.symm⟩

/-- Each queried A point has a selector index below the actual A-call budget. -/
theorem exists_selector (tables : Tables Password Entropy) (adversary : OracleComp (spec Password Entropy) Result)
    (input : Input (Password := Password)) (budget : Nat)
    (queried : embedA input ∈ (execute tables adversary).2)
    (bounded : W4Cache.aCount (execute tables adversary).2 ≤ budget) :
    ∃ index : Fin budget, (execute tables (program adversary index.val)).1 = some input := by
  have member : input ∈ (records (execute tables adversary).2 []).map Prod.fst :=
    (W4ARecords.membership _ [] input).mpr ⟨queried,by simp⟩
  obtain ⟨record,found,same⟩ := List.mem_map.mp member
  obtain ⟨index,within,atIndex⟩ := List.getElem_of_mem found
  have limit := (W4ARecords.length (execute tables adversary).2 []).trans bounded
  refine ⟨⟨index,by omega⟩,?_⟩
  rw [program,execute_map]
  dsimp only
  rw [execution,List.getElem?_eq_getElem within,atIndex]
  simpa only [Option.map_some] using congrArg some same

end W4NthA

/-! Replay-prefix completeness without any table-reading selector or no-Early conditioning. -/
namespace W4KeyCoverage
open Gamma2Model W4KeyReplay G3Fresh
variable {Password Entropy : Type}

theorem embed_injective : Function.Injective (embedA : (AInput Password) → Point Password Entropy) := by
  rintro ⟨r, right⟩ ⟨s, other⟩ equal
  exact Prod.ext (Point.a.inj equal).1 (Point.a.inj equal).2

/-- The late point is absent from both replayed prefixes and the added earlier query. -/
theorem guard (first second : Recorded Password Entropy) (shared : List (Point Password Entropy))
    (p q : (AInput Password)) (firstChosen : first.1 = some p) (secondChosen : second.1 = some q)
    (firstPrefix : first.2 <+: shared) (secondPrefix : second.2 <+: shared)
    (firstFresh : embedA p ∉ first.2) (secondFresh : embedA q ∉ second.2) (different : p ≠ q) :
    ∃ early later, choose first second = some (early, later) ∧
      embedA later ∉ past first second early := by
  have pointsDifferent : (embedA p : Point Password Entropy) ≠ embedA q :=
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

variable [DecidableEq Password] [DecidableEq Entropy] [Inhabited Password]

/-- A genuine key collision passes the causal fresh test regardless of which stop came first. -/
theorem matching_result (tables : Tables Password Entropy)
    (first second : OracleComp (spec Password Entropy) (Option (AInput Password)))
    (shared : List (Point Password Entropy)) (p q : (AInput Password))
    (firstChosen : (execute tables first).1 = some p)
    (secondChosen : (execute tables second).1 = some q)
    (firstPrefix : (execute tables first).2 <+: shared)
    (secondPrefix : (execute tables second).2 <+: shared)
    (firstFresh : embedA p ∉ (execute tables first).2)
    (secondFresh : embedA q ∉ (execute tables second).2) (different : p ≠ q)
    (collision : tables.a p = tables.a q) :
    (execute tables (program first second)).1.2 =
      some (tables.a (execute tables (program first second)).1.1) := by
  obtain ⟨early, later, chosen, fresh⟩ := guard (execute tables first) (execute tables second)
    shared p q firstChosen secondChosen firstPrefix secondPrefix firstFresh secondFresh different
  have equalValues : tables.a early = tables.a later := by
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

end W4KeyCoverage

/-! One unconditional 2^-256 bound for the later of two causally selected key queries. -/
namespace W4KeyProbability
open Gamma2Model G3Programs G3Fresh
open W4KeyReplay OracleProjection FocusedExecution
open OracleTree OptionalFresh EnabledProjection
open TableFactors GameExpectation MomentTools
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy] [Inhabited Password]

def matching (answer : Key) : Finset Key := {answer}

variable (first second : OracleComp (spec Password Entropy) (Option (AInput Password)))

def focusedPair
    (others : OthersA Entropy) :=
  focused (focusA others.1 others.2.1 others.2.2) (program first second)

theorem fresh (others : OthersA Entropy) : EnabledFresh (focusedPair first second others) := by
  apply enabled_fresh (focusA others.1 others.2.1 others.2.2)
    (fun b => (⟨b, others.1, others.2.1, others.2.2⟩ : Tables Password Entropy))
    (by intro table point; cases point <;> rfl) (program first second)
    embedA (identifiesA others)
  intro table
  exact certificate _ first second

def event (tables : Tables Password Entropy) : Bool :=
  rawHit (focusedPair first second (tables.b, tables.h, tables.g)) matching tables.a

theorem result (tables : Tables Password Entropy) :
    (evaluate tables.a (focusedPair first second (tables.b, tables.h, tables.g))).1 =
      (execute tables (program first second)).1 := by
  exact result_eq (focusA tables.b tables.h tables.g) tables.a tables
    (by intro point; cases point <;> rfl) (program first second)

theorem collision_covered (tables : Tables Password Entropy)
    (first second : OracleComp (spec Password Entropy) (Option (AInput Password)))
    (shared : List (Point Password Entropy)) (p q : (AInput Password))
    (firstChosen : (execute tables first).1 = some p)
    (secondChosen : (execute tables second).1 = some q)
    (firstPrefix : (execute tables first).2 <+: shared)
    (secondPrefix : (execute tables second).2 <+: shared)
    (firstFresh : embedA p ∉ (execute tables first).2)
    (secondFresh : embedA q ∉ (execute tables second).2) (different : p ≠ q)
    (collision : tables.a p = tables.a q) : event first second tables = true := by
  have chosen := W4KeyCoverage.matching_result tables first second shared p q
    firstChosen secondChosen firstPrefix secondPrefix firstFresh secondFresh different collision
  simp only [event, rawHit, result]
  rw [chosen]
  simp only [optionalSet, matching, Finset.mem_singleton, decide_true]

variable [Fintype Password] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

/-- No conditioning on no Early: the pair observer always has probability at most 2^-256. -/
theorem probability (first second : OracleComp (spec Password Entropy) (Option (AInput Password))) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if event first second tables then 1 else 0) ≤ (1 : ENNReal) / (2 ^ 256 : ENNReal) := by
  have bound := G3Probability.averaged sampleTables
    (PMF.uniformOfFintype (OthersA Entropy))
    (fun others b => (⟨b, others.1, others.2.1, others.2.2⟩ : Tables Password Entropy)) factor_a
    (focusedPair first second) matching (event first second) (by intro others table; rfl)
    (fresh first second) (fun _ => 1) (by
      intro others table
      cases selected : (evaluate table (focusedPair first second others)).1.2 with
      | none => simp only [optionalSet, Finset.card_empty]; omega
      | some answer => simp only [optionalSet, matching, Finset.card_singleton, le_refl])
  simpa only [G3Probability.card_bits, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, constant] using bound

end W4KeyProbability

/-! Concrete completion times are the latest first-query positions of all chain points. -/
namespace W4Times
variable {Point : Type} [DecidableEq Point]

def time (queries chain : List Point) : Nat := chain.toFinset.sup queries.idxOf

def Complete (queries chain : List Point) : Prop := ∀ point ∈ chain, point ∈ queries

/-- Completion cannot precede any of the chain's first actual queries. -/
theorem query_le (queries chain : List Point) (point : Point) (member : point ∈ chain) :
    queries.idxOf point ≤ time queries chain := Finset.le_sup (f := fun value => queries.idxOf value) (List.mem_toFinset.mpr member)

/-- A nonempty chain's completion is caused by an actual point of that chain. -/
theorem attained (queries chain : List Point) (nonempty : chain ≠ []) :
    ∃ point ∈ chain, time queries chain = queries.idxOf point := by
  have active : chain.toFinset.Nonempty := by
    cases chain with
    | nil => exact False.elim (nonempty rfl)
    | cons point rest => exact ⟨point,List.mem_toFinset.mpr List.mem_cons_self⟩
  have member := (chain.toFinset).sup_mem_of_nonempty (f := fun value => queries.idxOf value) active
  obtain ⟨point,inChain,equal⟩ := member
  exact ⟨point,List.mem_toFinset.mp inChain,equal.symm⟩

/-- Every read of a chain completed earlier lies in the pre-terminal query prefix. -/
theorem earlier_prefix (queries chain : List Point) (limit : Nat)
    (complete : Complete queries chain) (earlier : time queries chain < limit) :
    ∀ point ∈ chain, point ∈ queries.take limit := by
  intro point member
  have before := (query_le queries chain point member).trans_lt earlier
  have queried := complete point member
  have atIndex := List.getElem?_idxOf queried
  have saved : (queries.take limit)[queries.idxOf point]? = some point := by
    rw [List.getElem?_take, if_pos before]
    exact atIndex
  exact List.mem_of_getElem? saved

/-- If two completions happen at the real terminal query, that exact query belongs to the other chain. -/
theorem simultaneous (queries chain : List Point) (terminal : Point) (nonempty : chain ≠ [])
    (complete : Complete queries chain) (queried : terminal ∈ queries)
    (equal : time queries chain = queries.idxOf terminal) : terminal ∈ chain := by
  obtain ⟨point,member,latest⟩ := attained queries chain nonempty
  have sameTime : queries.idxOf point = queries.idxOf terminal := latest.symm.trans equal
  have pAt := List.getElem?_idxOf (complete point member)
  have tAt := List.getElem?_idxOf queried
  rw [sameTime] at pAt
  have same := Option.some.inj (pAt.symm.trans tAt)
  exact same ▸ member

end W4Times

/-! Concrete W4 events use all actual chain points and actual first-query completion times. -/
namespace W4Model
open Gamma2Model G2 W4Times
open scoped Classical
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] finalize

variable (password : Password) (container : State) (tables : Tables Password Entropy)

def chain : List (Point Password Entropy) :=
  (execute tables (finalize password 12 container (by omega))).2

def recovered : State :=
  (execute tables (finalize password 12 container (by omega))).1.1

def completion (adversary : State → OracleComp (spec Password Entropy) Result) : Option Nat :=
  if W4Times.Complete (execute tables (adversary container)).2 (chain password container tables) then
    some (time (execute tables (adversary container)).2 (chain password container tables)) else none

def Collision (adversary : State → OracleComp (spec Password Entropy) Result) : Prop :=
  ∃ other before atReal, other ≠ password ∧ completion other container tables adversary = some before ∧
    completion password container tables adversary = some atReal ∧ before ≤ atReal ∧
    recovered other container tables = recovered password container tables

omit [DecidableEq Password] [DecidableEq Entropy] in
theorem chain_nonempty (password : Password) (container : State) (tables : Tables Password Entropy) :
    chain password container tables ≠ [] := by
  have size := finalize_chain_length tables password 12 container (by omega)
  rw [← finalize_trace] at size
  intro empty
  change (execute tables (finalize password 12 container (by omega))).2 = [] at empty
  rw [empty] at size
  cases size

omit [DecidableEq Password] [DecidableEq Entropy] in
/-- The terminal query is an actual member of the concrete 36-point chain. -/
theorem terminal_member (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (chronologicalRun password container tables adversary).point 35 ∈ chain password container tables := by
  change (chronologicalRun password container tables adversary).point 35 ∈ (execute tables (finalize password 12 container (by omega))).2
  rw [finalize_trace]
  change (chronologicalRun password container tables adversary).point 35 ∈ (outcome password container tables adversary).chain
  change ((outcome password container tables adversary).chain.getD 35 fallbackPoint) ∈ _
  rw [← List.getElem_eq_getD (h := by
    change 35 < (execute tables (finalize password 12 container (by omega))).1.2.length
    rw [finalize_chain_length]
    omega) fallbackPoint]
  exact List.getElem_mem _

/-- On the source guard the full chain is complete; completion occurs exactly at its terminal H0. -/
theorem real_time (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (terminal : Queried (chronologicalRun password container tables adversary) 35) :
    completion password container tables adversary =
      some ((execute tables (adversary container)).2.idxOf ((chronologicalRun password container tables adversary).point 35)) := by
  have all (point : Point Password Entropy) (member : point ∈ chain password container tables) :
      ∃ index, index < 36 ∧ (chronologicalRun password container tables adversary).point index = point := by
    unfold chain at member
    rw [finalize_trace] at member
    obtain ⟨index,within,equal⟩ := List.getElem_of_mem member
    refine ⟨index,?_,?_⟩
    · rw [finalize_chain_length] at within
      exact within
    · change (execute tables (finalize password 12 container (by omega))).1.2.getD index fallbackPoint = point
      rw [← List.getElem_eq_getD (h := within) fallbackPoint]
      exact equal
  have complete : W4Times.Complete (execute tables (adversary container)).2 (chain password container tables) := by
    intro point member
    obtain ⟨index,within,equal⟩ := all point member
    rw [← equal]
    exact (G4Order.queried_iff_mem _ _ index).mp
      (W4Terminal.all_queried password container tables adversary notEarly terminal index within)
  unfold completion
  rw [if_pos complete]
  apply congrArg some
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro point member
    obtain ⟨index,within,equal⟩ := all point (List.mem_toFinset.mp member)
    rw [← equal]
    by_cases last : index = 35
    · rw [last]
    · have order := all_ordered (chronologicalRun password container tables adversary) notEarly index 35 (by omega)
        (by rw [chronologicalRun_count]; omega)
      rw [W4Terminal.queried_time password container tables adversary index
        (W4Terminal.all_queried password container tables adversary notEarly terminal index within),
        W4Terminal.queried_time password container tables adversary 35 terminal] at order
      exact order.le
  · exact query_le _ _ _ (terminal_member password container tables adversary)

end W4Model

/-! Equal completion times force a shared H0 and a collision of distinct actual A inputs. -/
namespace W4Simultaneous
open W4KeyReplay
open Gamma2Model MhfeChain FinalCut G3Fresh
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy] [Inhabited Password]
attribute [local irreducible] prepare finalize

def event (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (index : Nat)
    (tables : Tables Password Entropy) : Bool :=
  W4KeyProbability.event (W4RealA.program password container adversary)
    (W4NthA.program (adversary container) index) tables

/-- The other chain need not have distinct salts, ordered queries, or no Early. -/
theorem covered (password other : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (budget : Nat)
    (different : other ≠ password)
    (notEarly : ¬ G2.Early (chronologicalRun password container tables adversary))
    (terminal : G2.Queried (chronologicalRun password container tables adversary) 35)
    (completeOther : W4Times.Complete (execute tables (adversary container)).2 (W4Model.chain other container tables))
    (sameTime : W4Times.time (execute tables (adversary container)).2 (W4Model.chain other container tables) = (execute tables (adversary container)).2.idxOf ((chronologicalRun password container tables adversary).point 35))
    (bounded : W4Cache.aCount (execute tables (adversary container)).2 ≤ budget) :
    ∃ index : Fin budget, event password container adversary index.val tables = true := by
  let cut := (execute tables (prepare password 11 container (by omega))).1
  let otherCut := (execute tables (prepare other 11 container (by omega))).1
  have terminalQueried := (G4Order.queried_iff_mem _ _ 35).mp terminal
  have shared := W4Times.simultaneous (execute tables (adversary container)).2
    (W4Model.chain other container tables) ((chronologicalRun password container tables adversary).point 35)
    (W4Model.chain_nonempty other container tables) completeOther terminalQueried sameTime
  have shape : W4Model.chain other container tables = otherCut.before ++ [FinalCut.terminal otherCut] := by
    unfold W4Model.chain
    rw [finalize_trace]
    exact G4Terminal.chain_shape other container tables adversary
  rw [G4Terminal.last_point,shape,List.mem_append] at shared
  have sharedTerminal : FinalCut.terminal cut = FinalCut.terminal otherCut := by
    rcases shared with early | last
    · exact False.elim (terminal_absent other tables 11 (by omega) container cut.key cut.state.1 early)
    · exact List.mem_singleton.mp last
  have sameKey : cut.key = otherCut.key := (Point.h.inj sharedTerminal).1
  let p : AInput Password := (password,tables.b (0,cut.state.1))
  let q : AInput Password := (other,tables.b (0,otherCut.state.1))
  have otherQueried : embedA q ∈ (execute tables (adversary container)).2 :=
    completeOther _ (by rw [shape]; exact List.mem_append_left _ (W4CutKey.key_member other tables 11 (by omega) container))
  obtain ⟨index,chosen⟩ := W4NthA.exists_selector tables (adversary container) q budget otherQueried bounded
  have realChosen := W4RealA.covered password container tables adversary notEarly terminal
  change (execute tables (W4RealA.program password container adversary)).1 = some p at realChosen
  have realCert := W4RealA.certificate password container tables adversary p realChosen
  have otherFresh := W4NthA.certificate tables (adversary container) index.val q chosen
  have otherPrefix := W4NthA.prefix_of_hit tables (adversary container) index.val q chosen
  have distinct : p ≠ q := by
    intro equal
    exact different (congrArg Prod.fst equal).symm
  have collision : tables.a p = tables.a q := by
    change tables.a (password,tables.b (0,cut.state.1)) = tables.a (other,tables.b (0,otherCut.state.1))
    exact (W4CutKey.key_value password tables 11 (by omega) container).symm.trans
      (sameKey.trans (W4CutKey.key_value other tables 11 (by omega) container))
  exact ⟨index,W4KeyProbability.collision_covered tables _ _ (execute tables (adversary container)).2
    p q realChosen chosen realCert.2 otherPrefix realCert.1 otherFresh distinct collision⟩

end W4Simultaneous

/-! Causal real-terminal H0 selection with a matching set derived solely from retained past answers. -/
namespace W4MaskProgram
open Gamma2Model MhfeChain G3Fresh OracleProjection
open TableFactors FocusedExecution
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
abbrev Context := Half × W4Cache.Reads (Password := Password) (Entropy := Entropy)
abbrev HInput := Key × Fin 12 × Half

def pick : ((Option (Cursor × List (Point Password Entropy))) × W4Cache.Reads (Password := Password) (Entropy := Entropy)) →
    HInput × Option (Context (Password := Password) (Entropy := Entropy))
  | (some (.mask round state key,_),reads) => if round = 0 then ((key,0,state.1),some (state.2,reads)) else ((0,0,0),none)
  | _ => ((0,0,0),none)

def program (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Password Entropy) (HInput × Option (Context (Password := Password) (Entropy := Entropy))) :=
  pick <$> RetainedAnswers.retaining (W4Terminal.stopped password container adversary)

def matching (container : State) (context : Context (Password := Password) (Entropy := Entropy)) : Finset Half :=
  W4Cache.matching container context.1 context.2

variable (password : Password) (container : State) (tables : Tables Password Entropy)
  (adversary : State → OracleComp (spec Password Entropy) Result)

/-- Retained answer instrumentation has exactly the old monitor trace. -/
theorem execution :
    execute tables (program password container adversary) =
      (pick ((execute tables (W4Terminal.stopped password container adversary)).1,
        RetainedAnswers.answers (answer tables) (W4Terminal.stopped password container adversary)),
        (execute tables (W4Terminal.stopped password container adversary)).2) := by
  rw [program, execute_map]
  have same := RetainedAnswers.retaining_execution (answer tables) (W4Terminal.stopped password container adversary)
  exact congrArg (fun result => (pick result.1,result.2)) same

/-- Successful selection certifies that the real terminal H0 remains unread. -/
theorem certificate (enabled : (execute tables (program password container adversary)).1.2 ≠ none) :
    embedH (execute tables (program password container adversary)).1.1 ∉
      (execute tables (program password container adversary)).2 := by
  rw [execution] at enabled ⊢
  generalize stopped : (execute tables (W4Terminal.stopped password container adversary)).1 = result at enabled ⊢
  cases result with
  | none => exact False.elim (enabled rfl)
  | some value =>
    rcases value with ⟨cursor,history⟩
    cases cursor with
    | salt round state => exact False.elim (enabled rfl)
    | key round state salt => exact False.elim (enabled rfl)
    | mask round state key =>
      by_cases zero : round = 0
      · subst round
        simpa only [pick, if_true, embedH, point] using
          W4Terminal.fresh password container tables adversary (.mask 0 state key) history stopped
      · exact False.elim (enabled (by simp only [pick, if_neg zero]))

/-- No candidate can be added by reading a future table value. -/
theorem size :
    (OptionalFresh.optionalSet (matching container) (execute tables (program password container adversary)).1.2).card ≤
      W4Cache.aCount (execute tables (adversary container)).2 := by
  rw [execution]
  cases stopped : (execute tables (W4Terminal.stopped password container adversary)).1 with
  | none => exact Nat.zero_le _
  | some value =>
    rcases value with ⟨cursor,history⟩
    cases cursor with
    | salt round state => exact Nat.zero_le _
    | key round state salt => exact Nat.zero_le _
    | mask round state key =>
      by_cases zero : round = 0
      · subst round
        simp only [pick, if_true, OptionalFresh.optionalSet, matching]
        have bound := W4Cache.size container state.2
          (RetainedAnswers.answers (answer tables) (W4Terminal.stopped password container adversary))
        rw [RetainedAnswers.answer_points] at bound
        change (W4Cache.matching container state.2
          (RetainedAnswers.answers (answer tables) (W4Terminal.stopped password container adversary))).card ≤
          W4Cache.aCount (execute tables (W4Terminal.stopped password container adversary)).2 at bound
        have info := ChainMonitor.information (machine password) (fun cursor => decide (stage cursor = 35)) tables
          (adversary container) (some (.salt 11 container)) [] (.mask 0 state key) history stopped
        have budget := W4MonitorPrefix.a_budget (machine password) (fun cursor => decide (stage cursor = 35)) tables
          (adversary container) (some (.salt 11 container)) (.mask 0 state key) history stopped
        have trace : (execute tables (W4Terminal.stopped password container adversary)).2 = history := by
          (try simp only [List.nil_append] at info.1.symm ⊢)
          exact info.1.symm
        rw [trace] at bound
        exact bound.trans budget
      · simp only [pick, if_neg zero, OptionalFresh.optionalSet, Finset.card_empty]
        exact Nat.zero_le _

def focused (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (others : G3Programs.OthersH Password Entropy) :=
  FocusedExecution.focused (focusH others.1 others.2.1 others.2.2) (program password container adversary)

theorem fresh (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (others : G3Programs.OthersH Password Entropy) :
    OptionalFresh.EnabledFresh (focused password container adversary others) := by
  apply EnabledProjection.enabled_fresh (focusH others.1 others.2.1 others.2.2)
    (fun h => (⟨others.1,others.2.1,h,others.2.2⟩ : Tables Password Entropy))
    (by intro table point; cases point <;> rfl) (program password container adversary)
    embedH (identifiesH others)
  intro table
  exact certificate password container _ adversary

end W4MaskProgram

/-! Unconditional uniform-H0 estimate for the concrete causal cache-matching event. -/
namespace W4MaskProbability
open Gamma2Model TableFactors G3Programs FocusedExecution
open OracleProjection OptionalFresh OracleTree GameExpectation MomentTools
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

def event (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (tables : Tables Password Entropy) : Bool :=
  rawHit (W4MaskProgram.focused password container adversary (tables.a,tables.b,tables.g))
    (W4MaskProgram.matching container) tables.h

/-- The focused implementation preserves the selected real query and its full cached context. -/
theorem result (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (tables : Tables Password Entropy) :
    (evaluate tables.h (W4MaskProgram.focused password container adversary (tables.a,tables.b,tables.g))).1 =
      (execute tables (W4MaskProgram.program password container adversary)).1 :=
  result_eq (focusH tables.a tables.b tables.g) tables.h tables
    (by intro point; cases point <;> rfl) (W4MaskProgram.program password container adversary)

variable [Fintype Password] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

/-- No conditioning on no Early is used to establish the terminal-H0 hit probability. -/
theorem averaged (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) : moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if event password container adversary tables then 1 else 0) ≤
    moment sampleTables (fun tables => (W4Cache.aCount (execute tables (adversary container)).2 : ENNReal)/(2^128 : ENNReal)) := by
  have bound := G3Probability.averaged sampleTables (PMF.uniformOfFintype (OthersH Password Entropy))
    (fun others h => (⟨others.1,others.2.1,h,others.2.2⟩ : Tables Password Entropy)) factor_h
    (W4MaskProgram.focused password container adversary) (W4MaskProgram.matching container)
    (event password container adversary) (by intro others table; rfl)
    (W4MaskProgram.fresh password container adversary)
    (fun tables => W4Cache.aCount (execute tables (adversary container)).2) (by
      intro others table
      unfold W4MaskProgram.focused
      rw [result_eq (focusH others.1 others.2.1 others.2.2) table
        (⟨others.1,others.2.1,table,others.2.2⟩ : Tables Password Entropy)
        (by intro point; cases point <;> rfl)]
      exact W4MaskProgram.size password container _ adversary)
  simpa only [G3Probability.card_bits, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- A genuine adversary A-query budget yields the exact first summand in W4. -/
theorem probability (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (kA : Nat)
    (budget : ∀ tables, W4Cache.aCount (execute tables (adversary container)).2 ≤ kA) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if event password container adversary tables then 1 else 0) ≤ (kA : ENNReal)/(2^128 : ENNReal) := by
  calc
    _ ≤ moment sampleTables (fun tables => (W4Cache.aCount (execute tables (adversary container)).2 : ENNReal)/(2^128 : ENNReal)) :=
      averaged password container adversary
    _ ≤ moment sampleTables (fun _ => (kA : ENNReal)/(2^128 : ENNReal)) := by
      apply mono
      intro tables
      exact ENNReal.div_le_div_right (by exact_mod_cast budget tables) _
    _ = _ := constant _ _

end W4MaskProbability

/-! The actual earlier-completed collision case is included in the causal terminal-mask hit event. -/
namespace W4Earlier
open Gamma2Model MhfeChain G2 FinalCut
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] finalize prepare

omit [DecidableEq Password] [DecidableEq Entropy] in
/-- Every full inverse chain actually queries A with its own password, regardless of salt repetition. -/
theorem chain_a (password : Password) (container : State) (tables : Tables Password Entropy) :
    Point.a password (tables.b (11,container.1)) ∈ (execute tables (finalize password 12 container (by omega))).2 := by
  rw [finalize_step password tables 11 (by omega) container]
  dsimp only
  exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

omit [DecidableEq Entropy] in
/-- Read history containing one A point contains that point's password in the candidate enumeration. -/
theorem password_member (password : Password) (salt : Half)
    (queries : List (Point Password Entropy)) (member : Point.a password salt ∈ queries) :
    password ∈ W4Cache.passwords queries := by
  unfold W4Cache.passwords
  rw [List.mem_toFinset, List.mem_filterMap]
  exact ⟨.a password salt,member,rfl⟩

/-- Source coverage uses actual completion, actual cached answers and the real recovered state. -/
theorem covered (password other : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (terminal : Queried (chronologicalRun password container tables adversary) 35)
    (completeOther : W4Times.Complete (execute tables (adversary container)).2 (W4Model.chain other container tables))
    (earlier : W4Times.time (execute tables (adversary container)).2 (W4Model.chain other container tables) < (execute tables (adversary container)).2.idxOf ((chronologicalRun password container tables adversary).point 35))
    (collision : W4Model.recovered other container tables = W4Model.recovered password container tables) :
    W4MaskProbability.event password container adversary tables = true := by
  let cut := (execute tables (prepare password 11 container (by omega))).1
  obtain ⟨history,hit⟩ := W4Terminal.covered password container tables adversary notEarly terminal
  rw [W4Cursor.indexed_prepare password container tables adversary] at hit
  change (execute tables (W4Terminal.stopped password container adversary)).1 =
    some (.mask 0 cut.state cut.key,history) at hit
  let reads := RetainedAnswers.answers (answer tables) (W4Terminal.stopped password container adversary)
  have valid : ∀ read ∈ reads, read.2 = answer tables read.1 := RetainedAnswers.consistent _ _
  have info := ChainMonitor.information (machine password) (fun cursor => decide (stage cursor = 35)) tables
    (adversary container) (some (.salt 11 container)) [] (.mask 0 cut.state cut.key) history hit
  have points : reads.map Sigma.fst = history := by
    rw [RetainedAnswers.answer_points]
    change (execute tables (W4Terminal.stopped password container adversary)).2 = history
    (try simp only [List.nil_append] at info.1.symm ⊢)
    exact info.1.symm
  have before := W4MonitorPrefix.before (machine password) (fun cursor => decide (stage cursor = 35)) tables
    (adversary container) (some (.salt 11 container)) (.mask 0 cut.state cut.key) history hit
  have terminalEq : (chronologicalRun password container tables adversary).point 35 = point password (.mask 0 cut.state cut.key) :=
    G4Terminal.last_point password container tables adversary
  rw [terminalEq] at earlier
  have allPresent : ∀ query ∈ (execute tables (finalize other 12 container (by omega))).2, query ∈ reads.map Sigma.fst := by
    intro query member
    rw [points,before]
    exact W4Times.earlier_prefix _ _ _ completeOther earlier query member
  have queried : other ∈ W4Cache.passwords (reads.map Sigma.fst) :=
    password_member other (tables.b (11,container.1)) _ (allPresent _ (chain_a other container tables))
  have equal : (execute tables (finalize other 12 container (by omega))).1.1.1 =
      cut.state.2 ^^^ tables.h (cut.key,0,cut.state.1) := by
    have first := congrArg Prod.fst collision
    exact first.trans (W4Cursor.output password container tables)
  have matching := W4Cache.covered container cut.state.2 (tables.h (cut.key,0,cut.state.1)) reads tables valid other queried allPresent equal
  simp only [W4MaskProbability.event, OptionalFresh.rawHit, W4MaskProbability.result]
  rw [W4MaskProgram.execution, hit]
  simpa only [W4MaskProgram.pick, if_true, OptionalFresh.optionalSet,
    W4MaskProgram.matching, decide_eq_true_eq] using matching

end W4Earlier

/-! The full source collision event is covered by two unconditional causal tests. -/
namespace W4Coverage
open Gamma2Model G2 W4Model
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy] [Inhabited Password]

def test (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) : Bool := by
  classical
  exact decide (Collision password container tables adversary ∧
    ¬ Early (chronologicalRun password container tables adversary) ∧
    Queried (chronologicalRun password container tables adversary) 35)

omit [Inhabited Password] in
theorem completion_some (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (atTime : Nat)
    (hit : completion password container tables adversary = some atTime) :
    W4Times.Complete (execute tables (adversary container)).2 (chain password container tables) ∧
      W4Times.time (execute tables (adversary container)).2 (chain password container tables) = atTime := by
  unfold completion at hit
  split_ifs at hit with complete
  · exact ⟨complete,Option.some.inj hit⟩

/-- This is the source event, with no auxiliary freshness premise on any competing chain. -/
theorem covered (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) (kA : Nat)
    (bounded : W4Cache.aCount (execute tables (adversary container)).2 ≤ kA)
    (hit : test password container tables adversary = true) :
    W4MaskProbability.event password container adversary tables = true ∨
      ∃ index : Fin kA, W4Simultaneous.event password container adversary index.val tables = true := by
  classical
  have details : Collision password container tables adversary ∧
      ¬ Early (chronologicalRun password container tables adversary) ∧
      Queried (chronologicalRun password container tables adversary) 35 := of_decide_eq_true hit
  rcases details with ⟨⟨other,before,atReal,different,otherDone,realDone,earlier,equal⟩,notEarly,terminal⟩
  have realTime := real_time password container tables adversary notEarly terminal
  have actualTime := Option.some.inj (realDone.symm.trans realTime)
  have otherTime := completion_some other container tables adversary before otherDone
  rw [actualTime] at earlier
  rcases lt_or_eq_of_le earlier with strict | same
  · exact Or.inl (W4Earlier.covered password other container tables adversary notEarly terminal
      otherTime.1 (otherTime.2.trans_lt strict) equal)
  · exact Or.inr (W4Simultaneous.covered password other container tables adversary kA different
      notEarly terminal otherTime.1 (otherTime.2.trans same) bounded)

end W4Coverage

/-!
W4: the full source collision event, under real no-Early and queried H0,
has probability at most k_A/2^128 + k_A/2^256 in the ideal-table model.
-/
namespace W4
open Gamma2Model GameExpectation MomentTools G3Sums
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy] [Inhabited Password]
  [Fintype Password] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

/-- Complete deterministic source-event bound, with an actual all-executions A-query budget. -/
theorem conditional_bound (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (kA : Nat)
    (budget : ∀ tables, W4Cache.aCount (execute tables (adversary container)).2 ≤ kA) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if W4Coverage.test password container tables adversary then 1 else 0) ≤
      (kA : ENNReal)/(2^128 : ENNReal) + (kA : ENNReal)/(2^256 : ENNReal) := by
  classical
  calc
    _ ≤ moment sampleTables (fun tables =>
        (if W4MaskProbability.event password container adversary tables then 1 else 0) +
        ∑ index : Fin kA, if W4Simultaneous.event password container adversary index.val tables then 1 else 0) := by
      apply mono
      intro tables
      by_cases enabled : W4Coverage.test password container tables adversary = true
      · rw [enabled]
        rcases W4Coverage.covered password container tables adversary kA (budget tables) enabled with earlier | simultaneous
        · rw [earlier]
          exact le_add_of_nonneg_right (zero_le)
        · exact (one_le_indicator_sum _ simultaneous).trans (le_add_of_nonneg_left (zero_le))
      · simp only [Bool.eq_false_iff.mpr enabled,Bool.false_eq_true,if_false,zero_le]
    _ = moment sampleTables (fun tables => if W4MaskProbability.event password container adversary tables then 1 else 0) +
        ∑ index : Fin kA, moment sampleTables (fun tables =>
          if W4Simultaneous.event password container adversary index.val tables then 1 else 0) := by
      rw [add,finite_sum]
    _ ≤ (kA : ENNReal)/(2^128 : ENNReal) + ∑ _ : Fin kA, (1 : ENNReal)/(2^256 : ENNReal) := by
      apply add_le_add (W4MaskProbability.probability password container adversary kA budget)
      apply Finset.sum_le_sum
      intro index _
      exact W4KeyProbability.probability _ _
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp [div_eq_mul_inv]

/-- Arbitrary independent external context (including wallet tables and coins) may be retained.
The joint law of P,Y,context need not be uniform; only the ideal crypto tables are sampled independently. -/
theorem joint_bound {Context : Type} (worlds : PMF (Password × State × Context))
    (adversary : Context → State → OracleComp (spec Password Entropy) Result) (kA : Nat)
    (budget : ∀ context container tables, W4Cache.aCount (execute tables (adversary context container)).2 ≤ kA) :
    ((worlds.bind fun world => sampleTables.map fun tables =>
      W4Coverage.test world.1 world.2.1 tables (adversary world.2.2)) true) ≤
      (kA : ENNReal)/(2^128 : ENNReal) + (kA : ENNReal)/(2^256 : ENNReal) := by
  rw [PMF.bind_apply]
  change moment worlds (fun world => (sampleTables.map fun tables =>
    W4Coverage.test world.1 world.2.1 tables (adversary world.2.2)) true) ≤ _
  apply bounded
  intro world
  rw [probability]
  exact conditional_bound world.1 world.2.1 (adversary world.2.2) kA (budget world.2.2 world.2.1)

end W4

/-! Removing independent wallet-query events preserves first-occurrence order of crypto points. -/
namespace W4TraceProjection
variable {Crypto Wallet : Type} [DecidableEq Crypto] [DecidableEq Wallet]
local instance : BEq (Crypto ⊕ Wallet) := ⟨fun x y => decide (x = y)⟩
local instance : LawfulBEq (Crypto ⊕ Wallet) where
  eq_of_beq := by intro x y equal; exact of_decide_eq_true equal
  rfl := by intro x; change decide (x = x) = true; simp

def crypto : List (Crypto ⊕ Wallet) → List Crypto
  | [] => []
  | .inl point :: rest => point :: crypto rest
  | .inr _ :: rest => crypto rest

omit [DecidableEq Crypto] [DecidableEq Wallet] in
@[simp] theorem member (queries : List (Crypto ⊕ Wallet)) (point : Crypto) :
    point ∈ crypto queries ↔ Sum.inl point ∈ queries := by
  induction queries with
  | nil => simp [crypto]
  | cons query rest ih => cases query <;> simp [crypto,ih]

/-- Full source times may have gaps; their order is exactly the crypto-only order. -/
theorem first_le (queries : List (Crypto ⊕ Wallet)) (first second : Crypto)
    (firstPresent : Sum.inl first ∈ queries) (secondPresent : Sum.inl second ∈ queries) :
    (crypto queries).idxOf first ≤ (crypto queries).idxOf second ↔
      queries.idxOf (Sum.inl first) ≤ queries.idxOf (Sum.inl second) := by
  induction queries with
  | nil => cases firstPresent
  | cons query rest ih =>
    cases query with
    | inr wallet =>
      have fp : Sum.inl first ∈ rest := by simpa using firstPresent
      have sp : Sum.inl second ∈ rest := by simpa using secondPresent
      simpa [crypto,List.idxOf_cons_ne] using ih fp sp
    | inl point =>
      by_cases firstSame : first = point
      · subst first
        simp [crypto]
      · by_cases secondSame : second = point
        · subst second
          simp [crypto,List.idxOf_cons_ne,Ne.symm firstSame]
        · have fp : Sum.inl first ∈ rest := by simpa [firstSame] using firstPresent
          have sp : Sum.inl second ∈ rest := by simpa [secondSame] using secondPresent
          simpa [crypto,List.idxOf_cons_ne,firstSame,secondSame,Ne.symm firstSame,Ne.symm secondSame] using ih fp sp

/-- Strict order also survives removal of the interspersed wallet queries. -/
theorem first_lt (queries : List (Crypto ⊕ Wallet)) (first second : Crypto)
    (firstPresent : Sum.inl first ∈ queries) (secondPresent : Sum.inl second ∈ queries) :
    (crypto queries).idxOf first < (crypto queries).idxOf second ↔
      queries.idxOf (Sum.inl first) < queries.idxOf (Sum.inl second) := by
  have forward := first_le queries first second firstPresent secondPresent
  have backward := first_le queries second first secondPresent firstPresent
  omega

omit [DecidableEq Crypto] [DecidableEq Wallet] in
/-- A completed chain is completed in both logs, including all 36 typed points. -/
theorem complete (queries : List (Crypto ⊕ Wallet)) (chain : List Crypto) :
    W4Times.Complete (crypto queries) chain ↔
      W4Times.Complete queries (chain.map Sum.inl) := by
  constructor
  · intro found point present
    obtain ⟨original,inside,same⟩ := List.mem_map.mp present
    exact same ▸ ((member queries original).mp (found original inside))
  · intro found point present
    exact (member queries point).mpr (found (Sum.inl point) (List.mem_map.mpr ⟨point,present,rfl⟩))

omit [DecidableEq Crypto] [DecidableEq Wallet] in
@[simp] theorem crypto_append (first second : List (Crypto ⊕ Wallet)) :
    crypto (first ++ second) = crypto first ++ crypto second := by
  induction first with
  | nil => rfl
  | cons query rest ih => cases query <;> simp [crypto,ih]

omit [DecidableEq Crypto] [DecidableEq Wallet] in
@[simp] theorem crypto_map (queries : List Crypto) :
    crypto (queries.map (Sum.inl : Crypto → Crypto ⊕ Wallet)) = queries := by
  induction queries with
  | nil => rfl
  | cons query rest ih => simp [crypto,ih]

omit [DecidableEq Crypto] [DecidableEq Wallet] in
theorem completion_le_witness {Point : Type} [DecidableEq Point] (queries first second : List Point)
    (nonempty : second ≠ []) :
    W4Times.time queries first ≤ W4Times.time queries second ↔
      ∃ last ∈ second, ∀ point ∈ first, queries.idxOf point ≤ queries.idxOf last := by
  constructor
  · intro bounded
    obtain ⟨last,member,attained⟩ := W4Times.attained queries second nonempty
    refine ⟨last,member,?_⟩
    intro point inside
    exact ((W4Times.query_le queries first point inside).trans bounded).trans_eq attained
  · rintro ⟨last,member,bounded⟩
    apply Finset.sup_le
    intro point inside
    exact (bounded point (List.mem_toFinset.mp inside)).trans
      (W4Times.query_le queries second last member)

/-- Thus the <= comparison in Coll_P is unchanged, even with arbitrary interspersed wallet calls. -/
theorem completion_le (queries : List (Crypto ⊕ Wallet)) (first second : List Crypto)
    (nonempty : second ≠ []) (firstComplete : ∀ point ∈ first, Sum.inl point ∈ queries)
    (secondComplete : ∀ point ∈ second, Sum.inl point ∈ queries) :
    W4Times.time (crypto queries) first ≤ W4Times.time (crypto queries) second ↔
      W4Times.time queries (first.map Sum.inl) ≤ W4Times.time queries (second.map Sum.inl) := by
  rw [completion_le_witness _ _ _ nonempty,completion_le_witness _ _ _ (by simpa using nonempty)]
  constructor
  · rintro ⟨last,member,bounded⟩
    refine ⟨Sum.inl last,List.mem_map.mpr ⟨last,member,rfl⟩,?_⟩
    intro point inside
    obtain ⟨original,originalMember,same⟩ := List.mem_map.mp inside
    subst point
    exact (first_le queries original last (firstComplete original originalMember) (secondComplete last member)).mp
      (bounded original originalMember)
  · rintro ⟨last,member,bounded⟩
    obtain ⟨originalLast,lastMember,same⟩ := List.mem_map.mp member
    subst last
    refine ⟨originalLast,lastMember,?_⟩
    intro point inside
    exact (first_le queries point originalLast (firstComplete point inside) (secondComplete originalLast lastMember)).mpr
      (bounded (Sum.inl point) (List.mem_map.mpr ⟨point,inside,rfl⟩))

end W4TraceProjection

/-! Early is invariant under removal of wallet queries, despite the numeric time gaps. -/
namespace W4OrderTransport
open G2
variable {Point Crypto Wallet : Type} [DecidableEq Point] [DecidableEq Crypto] [DecidableEq Wallet]

omit [DecidableEq Crypto] [DecidableEq Wallet] in
theorem no_early_of_adjacent (run : Run Point)
    (ordered : ∀ index, index+1 < run.count → firstTime run index < firstTime run (index+1)) :
    ¬ Early run := by
  have fresh (index : Nat) (within : index < run.count) : definedTime run index ≤ firstTime run index := by
    induction index with
    | zero => exact Nat.zero_le _
    | succ index ih =>
      have previous := ih (by omega)
      have step := ordered index within
      exact max_le (previous.trans step.le) (Nat.succ_le_of_lt step)
  rintro ⟨index,_,within,early⟩
  exact (not_lt_of_ge (fresh index within)) early

omit [DecidableEq Point] in
/-- Both runs have the same chain points; only independent wallet calls are omitted. -/
theorem early_iff (full : Run (Crypto ⊕ Wallet)) (small : Run Crypto)
    (queries : W4TraceProjection.crypto full.queries = small.queries)
    (counts : full.count = small.count)
    (points : ∀ index, index < small.count → full.point index = Sum.inl (small.point index)) :
    Early full ↔ Early small := by
  have times (first second : Nat) (fi : first < small.count) (si : second < small.count) :
      firstTime small first < firstTime small second ↔ firstTime full first < firstTime full second := by
    unfold firstTime
    rw [← queries,points first fi,points second si]
    apply W4TraceProjection.first_lt
    · rw [← points first fi]
      exact full.complete first (by omega)
    · rw [← points second si]
      exact full.complete second (by omega)
  apply not_iff_not.mp
  constructor
  · intro notEarly
    apply no_early_of_adjacent
    intro index within
    exact (times index (index+1) (by omega) within).mpr
      (by simpa only [Nat.add_sub_cancel] using ordered full notEarly (index+1) (by omega) (by omega))
  · intro notEarly
    apply no_early_of_adjacent
    intro index within
    exact (times index (index+1) (by omega) (by omega)).mp
      (by simpa only [Nat.add_sub_cancel] using ordered small notEarly (index+1) (by omega) (by omega))

end W4OrderTransport

/-! The W4 estimate survives actual wallet-query positions in the source transcript. -/
namespace W4Source
open Gamma2Model G2 W4Model W4TraceProjection
open GameExpectation MomentTools
variable {Password Entropy Result Wallet : Type} [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Wallet]
  [Inhabited Password]
attribute [local irreducible] finalize

variable (password : Password) (container : State) (tables : Tables Password Entropy)
  (adversary : State → OracleComp (spec Password Entropy) Result)

omit [DecidableEq Password] [DecidableEq Entropy] [Inhabited Password] in
/-- The model's private returned chain and its emitted chain are identical. -/
theorem chronological_queries :
    (chronologicalRun password container tables adversary).queries =
      (execute tables (adversary container)).2 ++ chain password container tables := by
  change (execute tables (adversary container)).2 ++ (execute tables (finalize password 12 container (by omega))).1.2 = _
  rw [← finalize_trace]
  rfl

/-- An annotated log may insert any number of wallet calls, without adding crypto calls. -/
def extended
    (fullPrefix : List (Point Password Entropy ⊕ Wallet))
    (projection : crypto fullPrefix = (execute tables (adversary container)).2) : Run (Point Password Entropy ⊕ Wallet) where
  queries := fullPrefix ++ (chain password container tables).map Sum.inl
  halt := fullPrefix.length
  halt_le_length := by simp
  point := fun index => Sum.inl ((chronologicalRun password container tables adversary).point index)
  count := (chronologicalRun password container tables adversary).count
  complete := by
    intro index within
    apply (member _ _).mp
    rw [crypto_append,crypto_map,projection]
    have present := (chronologicalRun password container tables adversary).complete index within
    rw [chronological_queries] at present
    exact present

def Collision (password : Password) (container : State) (tables : Tables Password Entropy)
    (fullPrefix : List (Point Password Entropy ⊕ Wallet)) : Prop :=
  ∃ other, other ≠ password ∧
    W4Times.Complete fullPrefix ((chain other container tables).map Sum.inl) ∧
    W4Times.Complete fullPrefix ((chain password container tables).map Sum.inl) ∧
    W4Times.time fullPrefix ((chain other container tables).map Sum.inl) ≤
      W4Times.time fullPrefix ((chain password container tables).map Sum.inl) ∧
    recovered other container tables = recovered password container tables

def test (fullPrefix : List (Point Password Entropy ⊕ Wallet))
    (projection : crypto fullPrefix = (execute tables (adversary container)).2) : Bool := by
  classical
  exact decide (Collision password container tables fullPrefix ∧
    ¬ Early (extended password container tables adversary fullPrefix projection) ∧
    Sum.inl ((chronologicalRun password container tables adversary).point 35) ∈ fullPrefix)

omit [Inhabited Password] in
/-- All source-event conditions, not just the numeric bound, transfer to the crypto projection. -/
theorem covered (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (fullPrefix : List (Point Password Entropy ⊕ Wallet))
    (projection : crypto fullPrefix = (execute tables (adversary container)).2)
    (hit : test password container tables adversary fullPrefix projection = true) :
    W4Coverage.test password container tables adversary = true := by
  classical
  have details : Collision password container tables fullPrefix ∧
      ¬ Early (extended password container tables adversary fullPrefix projection) ∧
      Sum.inl ((chronologicalRun password container tables adversary).point 35) ∈ fullPrefix := of_decide_eq_true hit
  rcases details with ⟨⟨other,different,otherComplete,realComplete,times,equal⟩,notEarly,terminal⟩
  have otherSmall : W4Times.Complete (execute tables (adversary container)).2 (chain other container tables) := by
    rw [← projection]
    exact (complete fullPrefix _).mpr otherComplete
  have realSmall : W4Times.Complete (execute tables (adversary container)).2 (chain password container tables) := by
    rw [← projection]
    exact (complete fullPrefix _).mpr realComplete
  have smallTimes : W4Times.time (execute tables (adversary container)).2 (chain other container tables) ≤
      W4Times.time (execute tables (adversary container)).2 (chain password container tables) := by
    rw [← projection]
    apply (completion_le fullPrefix _ _ (chain_nonempty password container tables) _ _).mpr times
    · intro point inside; exact otherComplete _ (List.mem_map.mpr ⟨point,inside,rfl⟩)
    · intro point inside; exact realComplete _ (List.mem_map.mpr ⟨point,inside,rfl⟩)
  have earlyEquivalent := W4OrderTransport.early_iff
    (extended password container tables adversary fullPrefix projection) (chronologicalRun password container tables adversary)
    (by change crypto (fullPrefix ++ (chain password container tables).map Sum.inl) = _
        rw [crypto_append,crypto_map,projection,chronological_queries]) rfl (by intro _ _; rfl)
  have smallNotEarly : ¬ Early (chronologicalRun password container tables adversary) :=
    fun early => notEarly (earlyEquivalent.mpr early)
  have smallTerminal : Queried (chronologicalRun password container tables adversary) 35 := by
    apply (G4Order.queried_iff_mem _ _ 35).mpr
    change (chronologicalRun password container tables adversary).point 35 ∈ (execute tables (adversary container)).2
    rw [← projection]
    exact (member fullPrefix _).mpr terminal
  apply decide_eq_true
  refine ⟨?_,smallNotEarly,smallTerminal⟩
  refine ⟨other,_,_,different,?_,?_,smallTimes,equal⟩
  · exact if_pos otherSmall
  · exact if_pos realSmall

variable [Fintype Password] [Fintype Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

/-- Numeric source completion times include wallet calls; the exact W4 bound is unchanged. -/
theorem conditional_bound (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (annotated : Tables Password Entropy → List (Point Password Entropy ⊕ Wallet))
    (projection : ∀ tables, crypto (annotated tables) = (execute tables (adversary container)).2)
    (kA : Nat) (budget : ∀ tables, W4Cache.aCount (execute tables (adversary container)).2 ≤ kA) :
    moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun tables =>
      if test password container tables adversary (annotated tables) (projection tables) then 1 else 0) ≤
      (kA : ENNReal)/(2^128 : ENNReal) + (kA : ENNReal)/(2^256 : ENNReal) := by
  calc
    _ ≤ moment sampleTables (fun tables => if W4Coverage.test password container tables adversary then 1 else 0) := by
      apply mono
      intro tables
      by_cases enabled : test password container tables adversary (annotated tables) (projection tables) = true
      · rw [enabled,covered password container tables adversary (annotated tables) (projection tables) enabled]
      · simp only [Bool.eq_false_iff.mpr enabled,Bool.false_eq_true,if_false,zero_le]
    _ ≤ _ := W4.conditional_bound password container adversary kA budget

end W4Source

/-! Partial evaluation of all typed independent wallet oracles preserves actual crypto execution. -/
namespace WalletCryptoCompiler
open Gamma2Model
variable {Password Entropy Wallet Result : Type}

@[reducible] def combinedSpec (walletSpec : OracleSpec Wallet) : OracleSpec (Point Password Entropy ⊕ Wallet)
  | .inl point => spec Password Entropy point
  | .inr point => walletSpec point

def combinedAnswer (walletSpec : OracleSpec Wallet) (tables : Tables Password Entropy)
    (wallet : (point : Wallet) → walletSpec point) :
    (point : Point Password Entropy ⊕ Wallet) → combinedSpec walletSpec point
  | .inl point => answer tables point
  | .inr point => wallet point

/-- No crypto table is passed to this compiler. Adaptive wallet queries use only the fixed external context. -/
def compile (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result) :
    OracleComp (spec Password Entropy) Result :=
  OracleComp.construct (fun result => pure result)
    (fun point _ recurse => match point with
      | .inl point => do
        let value ← ask point
        recurse value
      | .inr point => recurse (wallet point)) program

theorem compile_pure (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (result : Result) : compile (Password := Password) (Entropy := Entropy) walletSpec wallet (pure result) = pure result := rfl

theorem compile_query (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (point : Point Password Entropy ⊕ Wallet)
    (next : combinedSpec walletSpec point → OracleComp (combinedSpec walletSpec) Result) :
    compile walletSpec wallet (TranscriptErasure.ask point >>= next) =
      (match point with
      | .inl point => do
          let value ← ask point
          compile walletSpec wallet (next value)
      | .inr point => compile walletSpec wallet (next (wallet point))) := by
  cases point <;> rfl

attribute [local irreducible] compile

/-- Both result and the complete crypto query log agree, for every full adaptive program and context. -/
theorem execution (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (tables : Tables Password Entropy)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result) :
    execute tables (compile walletSpec wallet program) =
      let full := TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) program
      (full.1,W4TraceProjection.crypto full.2) := by
  induction program using OracleComp.inductionOn with
  | pure result => rw [compile_pure]; rfl
  | query_bind point next ih =>
    change execute tables (compile walletSpec wallet (TranscriptErasure.ask point >>= next)) = _
    rw [compile_query]
    cases point with
    | inl point =>
      change execute tables (ask point >>= fun value => compile walletSpec wallet (next value)) = _
      simp only [execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g]
      rw [ih (answer tables point)]
      rfl
    | inr point =>
      rw [ih (wallet point)]
      rfl

end WalletCryptoCompiler

/-! W4 for the full adaptive crypto+wallet oracle execution and its actual query budget. -/
namespace W4Wallet
open Gamma2Model WalletCryptoCompiler GameExpectation MomentTools
variable {Password Entropy Result Wallet : Type} [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Wallet]

def aQuery : Point Password Entropy ⊕ Wallet → Bool
  | .inl (.a _ _) => true
  | _ => false

def full (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (tables : Tables Password Entropy)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result) :=
  TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) program

omit [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Wallet] in
/-- The budget counts every actual A call, including repeats, and no wallet calls. -/
theorem a_count (queries : List (Point Password Entropy ⊕ Wallet)) :
    W4Cache.aCount (W4TraceProjection.crypto queries) = queries.countP aQuery := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
    cases query with
    | inr query => simpa only [W4TraceProjection.crypto,List.countP_cons,aQuery,Bool.false_eq_true,if_false,Nat.add_zero] using ih
    | inl point => cases point <;> simpa [W4TraceProjection.crypto,W4Cache.aCount,aQuery,List.countP_cons] using ih

omit [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Wallet] in
/-- No projection premise is left to the caller: it follows from the actual full executor. -/
theorem projection (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (tables : Tables Password Entropy)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result) :
    W4TraceProjection.crypto (full walletSpec wallet tables program).2 =
      (execute tables (compile walletSpec wallet program)).2 :=
  (congrArg Prod.snd (execution walletSpec wallet tables program)).symm

def test (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result) : Bool :=
  W4Source.test password container tables (fun state => compile walletSpec wallet (adversary state))
    (full walletSpec wallet tables (adversary container)).2
    (projection walletSpec wallet tables (adversary container))

variable [Fintype Password] [Fintype Entropy] [Inhabited Password]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

theorem conditional_bound (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (password : Password) (container : State)
    (adversary : State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result)
    (kA : Nat) (budget : ∀ tables, (full walletSpec wallet tables (adversary container)).2.countP aQuery ≤ kA) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if test walletSpec wallet password container tables adversary then 1 else 0) ≤
      (kA : ENNReal)/(2^128 : ENNReal) + (kA : ENNReal)/(2^256 : ENNReal) := by
  apply W4Source.conditional_bound password container (fun state => compile walletSpec wallet (adversary state))
    (fun tables => (full walletSpec wallet tables (adversary container)).2)
    (fun tables => projection walletSpec wallet tables (adversary container)) kA
  intro tables
  rw [← projection walletSpec wallet tables (adversary container),a_count]
  exact budget tables

/-- Full wallet context and private coins are retained; only crypto tables are sampled independently. -/
theorem joint_bound {Context : Type} (worlds : PMF (Password × State × Context))
    (walletSpec : OracleSpec Wallet) (wallet : Context → (point : Wallet) → walletSpec point)
    (adversary : Context → State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result)
    (kA : Nat) (budget : ∀ context container tables,
      (full walletSpec (wallet context) tables (adversary context container)).2.countP aQuery ≤ kA) :
    moment (worlds.bind fun world => sampleTables.map fun tables =>
      test walletSpec (wallet world.2.2) world.1 world.2.1 tables (adversary world.2.2))
      (fun hit => if hit then 1 else 0) ≤
      (kA : ENNReal)/(2^128 : ENNReal) + (kA : ENNReal)/(2^256 : ENNReal) := by
  rw [MomentTools.bind]
  apply bounded
  intro world
  rw [moment_map]
  exact conditional_bound walletSpec (wallet world.2.2) world.1 world.2.1 (adversary world.2.2) kA
    (budget world.2.2 world.2.1)

end W4Wallet

end
end MhfeLean
