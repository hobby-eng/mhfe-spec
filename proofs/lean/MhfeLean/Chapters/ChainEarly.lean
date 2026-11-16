import Mathlib.Data.Fintype.Vector
import MhfeLean.Chapters.ChainMonitoring
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.Probability

namespace MhfeLean
noncomputable section

/-! # Lemma G3: probability of premature chain queries
-/

/-!
The 35 stopping programs, grouped into 12 salt, 12 key and 11 mask selections.
Their code takes the other tables as explicit fixed inputs and never receives
the selected table. That table is accessible only through program queries.
-/

namespace G3Programs

open Gamma2Model MhfeChain ChainMonitor
open MhfeMonitorCoverage MatchingSets TableFactors
open OracleTree OracleProjection FocusedExecution

variable {Password Entropy Result : Type}

abbrev History (Password Entropy : Type) := List (Point Password Entropy)
abbrev OthersA (Entropy : Type) := BTable × HTable × GTable Entropy
abbrev OthersB (Password Entropy : Type) := ATable Password × HTable × GTable Entropy
abbrev OthersH (Password Entropy : Type) := ATable Password × BTable × GTable Entropy

/-- Pre-key-query context fixes the next mask query's round and right half. -/
structure KeyContext (Password Entropy : Type) where
  round : Fin 12
  right : Half
  history : History Password Entropy

/-- Pre-mask-query context fixes the next salt query's round and XOR offset. -/
structure MaskContext (Password Entropy : Type) where
  nextRound : Fin 12
  offset : Half
  history : History Password Entropy

/-- Stage of the salt query in inverse round i. -/
def bIndex (round : Fin 12) : Fin 35 := ⟨3 * (11 - round.val), by omega⟩

/-- Stage of the key query in inverse round i. -/
def aIndex (round : Fin 12) : Fin 35 := ⟨3 * (11 - round.val) + 1, by omega⟩

/-- The eleven nonterminal mask rounds, in increasing round order. -/
def hRound (index : Fin 11) : Fin 12 := ⟨index.val + 1, by omega⟩

/-- Stage of a nonterminal mask query. -/
def hIndex (index : Fin 11) : Fin 35 := ⟨3 * (11 - (index.val + 1)) + 2, by omega⟩

/-- Round reached after this nonterminal mask query. -/
def hNext (index : Fin 11) : Fin 12 := ⟨index.val, by omega⟩

/-- Select only a salt cursor; disabled cases have an empty matching context. -/
def pickB : Option (Cursor × History Password Entropy) →
    (Fin 12 × Half) × Option (History Password Entropy)
  | some (.salt round state, history) => ((round, state.1), some history)
  | _ => ((0, 0), none)

/-- Select only a key cursor, retaining the next H query's fixed components. -/
def pickA (password : Password) : Option (Cursor × History Password Entropy) →
    (Password × Half) × Option (KeyContext Password Entropy)
  | some (.key round state salt, history) =>
    ((password, salt), some ⟨round, state.1, history⟩)
  | _ => ((password, 0), none)

/-- Select only a nonterminal mask cursor, retaining the next B query's fixed components. -/
def pickH : Option (Cursor × History Password Entropy) →
    (Key × Fin 12 × Half) × Option (MaskContext Password Entropy)
  | some (.mask round state key, history) =>
    if positive : 0 < round.val then
      ((key, round, state.1), some ⟨⟨round.val - 1, by omega⟩, state.2, history⟩)
    else ((0, 0, 0), none)
  | _ => ((0, 0, 0), none)

/-- Values of a fresh salt that would hit an already cached A query. -/
def matchingB [DecidableEq Password] (password : Password) (history : History Password Entropy) :
    Finset Half := values (saltValue password) history

/-- Values of a fresh key that would hit an already cached H query. -/
def matchingA (context : KeyContext Password Entropy) : Finset Key :=
  values (keyValue context.round context.right) context.history

/-- Values of a fresh mask that would hit an already cached B query. -/
def matchingH (context : MaskContext Password Entropy) : Finset Half :=
  values (maskValue context.nextRound context.offset) context.history

variable [DecidableEq Password] [DecidableEq Entropy]

variable (password : Password) (container : State)
  (adversary : State → OracleComp (spec Password Entropy) Result)

/-- The causal observer, fixed before any selected-table answer is sampled. -/
def stopped (selected : Fin 35) :=
  monitor (machine password) (fun cursor => decide (stage cursor = selected.val))
    (fullProgram password container adversary) (some (.salt 11 container)) []

/-- The typed program preparing a salt selection, with no direct table arguments. -/
def programB (round : Fin 12) :=
  pickB <$> stopped password container adversary (bIndex round)

/-- The typed program preparing a key selection, with no direct table arguments. -/
def programA (round : Fin 12) :=
  pickA password <$> stopped password container adversary (aIndex round)

/-- The typed program preparing a nonterminal mask selection. -/
def programH (index : Fin 11) :=
  pickH <$> stopped password container adversary (hIndex index)

/-- The source salt-hit event, evaluated on the full actual table record. -/
def eventB (round : Fin 12) (tables : Tables Password Entropy) : Bool :=
  let selected := (execute tables (programB password container adversary round)).1
  decide (tables.b selected.1 ∈ OptionalFresh.optionalSet (matchingB password) selected.2)

/-- The source key-hit event, evaluated on the full actual table record. -/
def eventA (round : Fin 12) (tables : Tables Password Entropy) : Bool :=
  let selected := (execute tables (programA password container adversary round)).1
  decide (tables.a selected.1 ∈ OptionalFresh.optionalSet matchingA selected.2)

/-- The source mask-hit event, evaluated on the full actual table record. -/
def eventH (index : Fin 11) (tables : Tables Password Entropy) : Bool :=
  let selected := (execute tables (programH password container adversary index)).1
  decide (tables.h selected.1 ∈ OptionalFresh.optionalSet matchingH selected.2)

end G3Programs

/-!
Enabled stopping outputs are fresh in the actual typed trace and hence in the
focused trace. Programs never receive the selected table as a direct argument.
-/

namespace G3Fresh

open Gamma2Model MhfeChain ChainMonitor
open MhfeMonitorCoverage G3Programs OracleProjection
open EnabledProjection

variable {Password Entropy Result : Type}

/-- Embed a B-table input as its unique typed query point. -/
def embedB (query : Fin 12 × Half) : Point Password Entropy := .b query.1 query.2

/-- Embed an A-table input as its unique typed query point. -/
def embedA (query : Password × Half) : Point Password Entropy := .a query.1 query.2

/-- Embed an H-table input as its unique typed query point. -/
def embedH (query : Key × Fin 12 × Half) : Point Password Entropy := .h query.1 query.2.1 query.2.2

/-- B's projected input identifies one full typed query. -/
theorem identifiesB (others : OthersB Password Entropy) (point : Point Password Entropy)
    (query : Fin 12 × Half)
    (given : delegatedPoint (focusB others.1 others.2.1 others.2.2) point = some query) :
    point = embedB query := by
  rcases query with ⟨round, right⟩
  cases point <;> simp_all [delegatedPoint, focusB, embedB]

/-- A's projected input identifies one full typed query. -/
theorem identifiesA (others : OthersA Entropy) (point : Point Password Entropy)
    (query : Password × Half)
    (given : delegatedPoint (focusA others.1 others.2.1 others.2.2) point = some query) :
    point = embedA query := by
  rcases query with ⟨password, salt⟩
  cases point <;> simp_all [delegatedPoint, focusA, embedA]

/-- H's projected input identifies one full typed query. -/
theorem identifiesH (others : OthersH Password Entropy) (point : Point Password Entropy)
    (query : Key × Fin 12 × Half)
    (given : delegatedPoint (focusH others.1 others.2.1 others.2.2) point = some query) :
    point = embedH query := by
  rcases query with ⟨key, round, right⟩
  cases point <;> simp_all [delegatedPoint, focusH, embedH]

variable [DecidableEq Password] [DecidableEq Entropy]

variable (password : Password) (container : State) (tables : Tables Password Entropy)
  (adversary : State → OracleComp (spec Password Entropy) Result)

/-- Successful actual stops are fresh relative to every query the observer emitted. -/
theorem stopped_fresh (selected : Fin 35) (cursor : Cursor) (history : History Password Entropy)
    (hit : (execute tables (stopped password container adversary selected)).1 = some (cursor, history)) :
    point password cursor ∉ (execute tables (stopped password container adversary selected)).2 := by
  simp only [stopped] at hit ⊢
  have details := information (machine password) (fun node => decide (stage node = selected.val))
    tables (fullProgram password container adversary) (some (.salt 11 container)) [] cursor history hit
  have fresh := details.2.1
  rw [details.1] at fresh
  simpa only [List.nil_append, machine] using fresh

/-- The typed salt-selection program certifies freshness for every enabled output. -/
theorem certificateB (round : Fin 12)
    (enabled : (execute tables (programB password container adversary round)).1.2 ≠ none) :
    embedB (execute tables (programB password container adversary round)).1.1 ∉
      (execute tables (programB password container adversary round)).2 := by
  have mapped : execute tables (programB password container adversary round) =
      (pickB (execute tables (stopped password container adversary (bIndex round))).1,
        (execute tables (stopped password container adversary (bIndex round))).2) := by
    rw [programB, execute_map]
  rw [mapped] at enabled ⊢
  generalize hit : (execute tables (stopped password container adversary (bIndex round))).1 = result at enabled ⊢
  cases result with
  | none => exact False.elim (enabled rfl)
  | some result =>
    rcases result with ⟨cursor, history⟩
    cases cursor with
    | salt selected state =>
      simpa only [pickB, embedB, point] using
        stopped_fresh password container tables adversary (bIndex round) (.salt selected state) history hit
    | key selected state salt => exact False.elim (enabled rfl)
    | mask selected state key => exact False.elim (enabled rfl)

/-- The typed key-selection program certifies freshness for every enabled output. -/
theorem certificateA (round : Fin 12)
    (enabled : (execute tables (programA password container adversary round)).1.2 ≠ none) :
    embedA (execute tables (programA password container adversary round)).1.1 ∉
      (execute tables (programA password container adversary round)).2 := by
  have mapped : execute tables (programA password container adversary round) =
      (pickA password (execute tables (stopped password container adversary (aIndex round))).1,
        (execute tables (stopped password container adversary (aIndex round))).2) := by
    rw [programA, execute_map]
  rw [mapped] at enabled ⊢
  generalize hit : (execute tables (stopped password container adversary (aIndex round))).1 = result at enabled ⊢
  cases result with
  | none => exact False.elim (enabled rfl)
  | some result =>
    rcases result with ⟨cursor, history⟩
    cases cursor with
    | salt selected state => exact False.elim (enabled rfl)
    | key selected state salt =>
      simpa only [pickA, embedA, point] using
        stopped_fresh password container tables adversary (aIndex round) (.key selected state salt) history hit
    | mask selected state key => exact False.elim (enabled rfl)

/-- The typed mask-selection program certifies freshness for every enabled output. -/
theorem certificateH (index : Fin 11)
    (enabled : (execute tables (programH password container adversary index)).1.2 ≠ none) :
    embedH (execute tables (programH password container adversary index)).1.1 ∉
      (execute tables (programH password container adversary index)).2 := by
  have mapped : execute tables (programH password container adversary index) =
      (pickH (execute tables (stopped password container adversary (hIndex index))).1,
        (execute tables (stopped password container adversary (hIndex index))).2) := by
    rw [programH, execute_map]
  rw [mapped] at enabled ⊢
  generalize hit : (execute tables (stopped password container adversary (hIndex index))).1 = result at enabled ⊢
  cases result with
  | none => exact False.elim (enabled rfl)
  | some result =>
    rcases result with ⟨cursor, history⟩
    cases cursor with
    | salt selected state => exact False.elim (enabled rfl)
    | key selected state salt => exact False.elim (enabled rfl)
    | mask selected state key =>
      by_cases positive : 0 < selected.val
      · simpa only [pickH, dif_pos positive, embedH, point] using
          stopped_fresh password container tables adversary (hIndex index) (.mask selected state key) history hit
      · exact False.elim (enabled (by simp only [pickH, dif_neg positive]))

end G3Fresh

/-! Matching-size bounds for the focused stopping programs, with actual final counts. -/
namespace G3Sizes
open Gamma2Model MhfeChain G3Programs
open OracleProjection FocusedExecution OracleTree
open StoppingCounts QueryCounts OptionalFresh
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

variable (password : Password) (container : State) (tables : Tables Password Entropy)
  (adversary : State → OracleComp (spec Password Entropy) Result)

theorem sizeB (round : Fin 12) :
    (optionalSet (matchingB password)
      (execute tables (programB password container adversary round)).1.2).card ≤
      (outcome password container tables adversary).adversaryQueries.countP (aFor password) + (11 - round.val) := by
  rw [programB, execute_map]
  dsimp only
  generalize hit : (execute tables (stopped password container adversary (bIndex round))).1 = chosen
  cases chosen with
  | none => simp only [pickB, optionalSet, Finset.card_empty]; omega
  | some pair =>
    rcases pair with ⟨cursor, history⟩
    cases cursor with
    | salt selected state =>
      have position := selected_stage password container tables adversary (bIndex round) (.salt selected state) history hit
      have equal : selected = round := by apply Fin.ext; change 3 * (11 - selected.val) = 3 * (11 - round.val) at position; have := selected.isLt; have := round.isLt; omega
      subst selected
      exact salt_budget password container tables adversary (bIndex round) round state history hit
    | key selected state salt => simp only [pickB, optionalSet, Finset.card_empty]; omega
    | mask selected state key => simp only [pickB, optionalSet, Finset.card_empty]; omega

theorem sizeA (round : Fin 12) :
    (optionalSet matchingA
      (execute tables (programA password container adversary round)).1.2).card ≤
      (outcome password container tables adversary).adversaryQueries.countP (hFor round) := by
  rw [programA, execute_map]
  dsimp only
  generalize hit : (execute tables (stopped password container adversary (aIndex round))).1 = chosen
  cases chosen with
  | none => simp only [pickA, optionalSet, Finset.card_empty]; omega
  | some pair =>
    rcases pair with ⟨cursor, history⟩
    cases cursor with
    | salt selected state => simp only [pickA, optionalSet, Finset.card_empty]; omega
    | key selected state salt =>
      have position := selected_stage password container tables adversary (aIndex round) (.key selected state salt) history hit
      have equal : selected = round := by apply Fin.ext; change 3 * (11 - selected.val) + 1 = 3 * (11 - round.val) + 1 at position; have := selected.isLt; have := round.isLt; omega
      subst selected
      exact key_budget password container tables adversary (aIndex round) round state salt history hit
    | mask selected state key => simp only [pickA, optionalSet, Finset.card_empty]; omega

theorem sizeH (index : Fin 11) :
    (optionalSet matchingH
      (execute tables (programH password container adversary index)).1.2).card ≤
      (outcome password container tables adversary).adversaryQueries.countP (bFor (hNext index)) := by
  rw [programH, execute_map]
  dsimp only
  generalize hit : (execute tables (stopped password container adversary (hIndex index))).1 = chosen
  cases chosen with
  | none => simp only [pickH, optionalSet, Finset.card_empty]; omega
  | some pair =>
    rcases pair with ⟨cursor, history⟩
    cases cursor with
    | salt selected state => simp only [pickH, optionalSet, Finset.card_empty]; omega
    | key selected state salt => simp only [pickH, optionalSet, Finset.card_empty]; omega
    | mask selected state key =>
      have positive := selected_mask_positive password container tables adversary (hIndex index) selected state key history hit
      have position := selected_stage password container tables adversary (hIndex index) (.mask selected state key) history hit
      have equal : (⟨selected.val - 1, by omega⟩ : Fin 12) = hNext index := by
        apply Fin.ext
        change 3 * (11 - selected.val) + 2 = 3 * (11 - (index.val + 1)) + 2 at position
        have := selected.isLt; have := index.isLt
        change selected.val - 1 = index.val
        omega
      simp only [pickH, dif_pos positive, optionalSet, matchingH]
      rw [← equal]
      exact mask_budget password container tables adversary (hIndex index) selected state key history hit

end G3Sizes

/-! Averaging the exact stopped-table estimates over the other ideal tables. -/
namespace G3Probability
open Gamma2Model G3Programs G3Fresh G3Sizes
open TableFactors OptionalFresh GameExpectation MomentTools
open OracleTree QueryCounts

variable {Domain Answer Context Others TablesType : Type}
variable [Fintype Domain] [Fintype Answer] [Nonempty Answer]
  [DecidableEq Domain] [DecidableEq Answer]

theorem averaged (law : PMF TablesType) (otherLaw : PMF Others)
    (pack : Others → (Domain → Answer) → TablesType)
    (factor : law = otherLaw.bind fun others =>
      (PMF.uniformOfFintype (Domain → Answer)).map (pack others))
    (program : Others → Program Domain Answer (Domain × Option Context))
    (matching : Context → Finset Answer) (event : TablesType → Bool)
    (agrees : ∀ others table, event (pack others table) = rawHit (program others) matching table)
    (fresh : ∀ others, EnabledFresh (program others)) (budget : TablesType → Nat)
    (bounded : ∀ others table,
      (optionalSet matching (evaluate table (program others)).1.2).card ≤ budget (pack others table)) :
    moment law (fun tables => if event tables then 1 else 0) ≤
      moment law (fun tables => (budget tables : ENNReal) / (Fintype.card Answer : ENNReal)) := by
  rw [factor, MomentTools.bind, MomentTools.bind]
  apply mono
  intro others
  rw [moment_map, moment_map]
  change moment (PMF.uniformOfFintype (Domain → Answer))
      (fun table => if event (pack others table) then 1 else 0) ≤ _
  simp_rw [agrees]
  rw [← probability]
  exact hit_bound (program others) matching (fresh others) _ (bounded others)

variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

theorem card_bits (width : Nat) : Fintype.card (BitVec width) = 2 ^ width := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (Lemma3.bitEquivFin width)

theorem salt (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (round : Fin 12) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if eventB password container adversary round tables then 1 else 0) ≤
    moment sampleTables (fun tables =>
      (((outcome password container tables adversary).adversaryQueries.countP (aFor password) +
        (11 - round.val) : Nat) : ENNReal) / (2 ^ 128 : ENNReal)) := by
  have bound := CryptoTablePresentation.hit_bound
    (programB password container adversary round)
    (fun view => embedB view.1.1) (fun view => view.1.2.isSome)
    (fun view => optionalSet (matchingB password) view.1.2)
    (fun table on => certificateB password container table adversary round (by
      intro absent
      try dsimp only at on
      rw [absent] at on
      cases on))
    (fun table => (((outcome password container table adversary).adversaryQueries.countP (aFor password) + (11-round.val) : Nat) : ENNReal) / (2^128 : ENNReal))
    (fun table _ => by
      have cap := sizeB password container table adversary round
      change ((optionalSet (matchingB password)
        (execute table (programB password container adversary round)).1.2).card : ENNReal) /
          (Fintype.card Half : ENNReal) ≤ _
      simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat] using
        ENNReal.div_le_div_right (show ((optionalSet (matchingB password)
          (execute table (programB password container adversary round)).1.2).card : ENNReal) ≤ _ from
          by exact_mod_cast cap) (Fintype.card Half : ENNReal))
  apply le_trans ?_ bound
  apply le_of_eq
  apply congrArg (moment sampleTables)
  funext table
  try dsimp only
  cases selected : (execute table (programB password container adversary round)).1.2 <;>
    simp [eventB, optionalSet, selected, embedB, answer]
  all_goals split_ifs <;> simp_all <;> contradiction

theorem key (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (round : Fin 12) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if eventA password container adversary round tables then 1 else 0) ≤
    moment sampleTables (fun tables =>
      ((outcome password container tables adversary).adversaryQueries.countP (hFor round) : ENNReal) /
        (2 ^ 256 : ENNReal)) := by
  have bound := CryptoTablePresentation.hit_bound
    (programA password container adversary round)
    (fun view => embedA view.1.1) (fun view => view.1.2.isSome)
    (fun view => optionalSet matchingA view.1.2)
    (fun table on => certificateA password container table adversary round (by
      intro absent
      try dsimp only at on
      rw [absent] at on
      cases on))
    (fun table => ((outcome password container table adversary).adversaryQueries.countP (hFor round) : ENNReal) / (2^256 : ENNReal))
    (fun table _ => by
      have cap := sizeA password container table adversary round
      change ((optionalSet matchingA
        (execute table (programA password container adversary round)).1.2).card : ENNReal) /
          (Fintype.card Key : ENNReal) ≤ _
      simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat] using
        ENNReal.div_le_div_right (show ((optionalSet matchingA
          (execute table (programA password container adversary round)).1.2).card : ENNReal) ≤ _ from
          by exact_mod_cast cap) (Fintype.card Key : ENNReal))
  apply le_trans ?_ bound
  apply le_of_eq
  apply congrArg (moment sampleTables)
  funext table
  try dsimp only
  cases selected : (execute table (programA password container adversary round)).1.2 <;>
    simp [eventA, optionalSet, selected, embedA, answer]
  all_goals split_ifs <;> simp_all <;> contradiction

theorem mask (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) (index : Fin 11) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if eventH password container adversary index tables then 1 else 0) ≤
    moment sampleTables (fun tables =>
      ((outcome password container tables adversary).adversaryQueries.countP (bFor (hNext index)) : ENNReal) /
        (2 ^ 128 : ENNReal)) := by
  have bound := CryptoTablePresentation.hit_bound
    (programH password container adversary index)
    (fun view => embedH view.1.1) (fun view => view.1.2.isSome)
    (fun view => optionalSet matchingH view.1.2)
    (fun table on => certificateH password container table adversary index (by
      intro absent
      try dsimp only at on
      rw [absent] at on
      cases on))
    (fun table => ((outcome password container table adversary).adversaryQueries.countP (bFor (hNext index)) : ENNReal) / (2^128 : ENNReal))
    (fun table _ => by
      have cap := sizeH password container table adversary index
      change ((optionalSet matchingH
        (execute table (programH password container adversary index)).1.2).card : ENNReal) /
          (Fintype.card Half : ENNReal) ≤ _
      simpa only [card_bits, Nat.cast_pow, Nat.cast_ofNat] using
        ENNReal.div_le_div_right (show ((optionalSet matchingH
          (execute table (programH password container adversary index)).1.2).card : ENNReal) ≤ _ from
          by exact_mod_cast cap) (Fintype.card Half : ENNReal))
  apply le_trans ?_ bound
  apply le_of_eq
  apply congrArg (moment sampleTables)
  funext table
  try dsimp only
  cases selected : (execute table (programH password container adversary index)).1.2 <;>
    simp [eventH, optionalSet, selected, embedH, answer]
  all_goals split_ifs <;> simp_all <;> contradiction

end G3Probability

/-! The actual source Early event is covered by the focused-table hit events. -/
namespace G3Events
open Gamma2Model MhfeChain G3Programs G3Sizes
open OptionalFresh MatchingSets G2
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

variable (password : Password) (container : State) (tables : Tables Password Entropy)
  (adversary : State → OracleComp (spec Password Entropy) Result)

theorem hitB (round : Fin 12) (state : State) (history : History Password Entropy)
    (hit : (execute tables (stopped password container adversary (bIndex round))).1 = some (.salt round state, history))
    (cached : Point.a password (tables.b (round, state.1)) ∈ history) :
    eventB password container adversary round tables = true := by
  simp only [eventB, programB, execute_map, hit, pickB, optionalSet, matchingB, decide_eq_true_eq]
  exact (salt_membership password history _).mpr cached

theorem hitA (round : Fin 12) (state : State) (salt : Half) (history : History Password Entropy)
    (hit : (execute tables (stopped password container adversary (aIndex round))).1 = some (.key round state salt, history))
    (cached : Point.h (tables.a (password, salt)) round state.1 ∈ history) :
    eventA password container adversary round tables = true := by
  simp only [eventA, programA, execute_map, hit, pickA, optionalSet, matchingA, decide_eq_true_eq]
  exact (key_membership round state.1 history _).mpr cached

theorem hitH (index : Fin 11) (state : State) (key : Key) (history : History Password Entropy)
    (hit : (execute tables (stopped password container adversary (hIndex index))).1 = some (.mask (hRound index) state key, history))
    (cached : Point.b (hNext index) (state.2 ^^^ tables.h (key, hRound index, state.1)) ∈ history) :
    eventH password container adversary index tables = true := by
  simp only [eventH, programH, execute_map, hit, pickH, optionalSet, matchingH,
    hRound, Nat.add_sub_cancel, decide_eq_true_eq]
  exact (mask_membership (hNext index) state.2 history _).mpr cached

theorem coverage (early : Early (chronologicalRun password container tables adversary)) :
    (∃ round, eventB password container adversary round tables = true) ∨
      (∃ round, eventA password container adversary round tables = true) ∨
      (∃ index, eventH password container adversary index tables = true) := by
  obtain ⟨selected, cursor, history, next, position, hit, step, cached⟩ :=
    EarlyHitCoverage.early_covered password container tables adversary early
  cases cursor with
  | salt round state =>
    have equal : selected = bIndex round := Fin.ext position.symm
    subst selected
    simp only [advance, answer, point, Option.some.injEq] at step
    subst next
    exact Or.inl ⟨round, hitB password container tables adversary round state history hit cached⟩
  | key round state salt =>
    have equal : selected = aIndex round := Fin.ext position.symm
    subst selected
    simp only [advance, answer, point, Option.some.injEq] at step
    subst next
    exact Or.inr (Or.inl ⟨round, hitA password container tables adversary round state salt history hit cached⟩)
  | mask round state key =>
    have positive : 0 < round.val := by
      change 3 * (11 - round.val) + 2 = selected.val at position
      have := selected.isLt; have := round.isLt; omega
    let index : Fin 11 := ⟨round.val - 1, by omega⟩
    have sameRound : hRound index = round := by apply Fin.ext; change round.val - 1 + 1 = round.val; omega
    have sameIndex : selected = hIndex index := by
      apply Fin.ext
      change 3 * (11 - round.val) + 2 = selected.val at position
      change selected.val = 3 * (11 - (round.val - 1 + 1)) + 2
      omega
    change (execute tables (stopped password container adversary selected)).1 = _ at hit
    rw [sameIndex] at hit
    have equalNext : (⟨round.val - 1, by omega⟩ : Fin 12) = hNext index := rfl
    simp only [advance, dif_pos positive, answer, point, Option.some.injEq] at step
    subst next
    have cached' : Point.b (hNext index) (state.2 ^^^ tables.h (key, hRound index, state.1)) ∈ history := by
      simpa only [point, equalNext, sameRound, BitVec.xor_eq] using cached
    apply Or.inr; apply Or.inr
    refine ⟨index, hitH password container tables adversary index state key history ?_ cached'⟩
    simpa only [sameRound] using hit

end G3Events

/-! Finite union and count algebra for the 35 G3 stopping events. -/
namespace G3Sums
open Gamma2Model G3Programs QueryCounts
open GameExpectation MomentTools
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

/-- Indicator of the actual chronological Early event, with no no-Early conditioning. -/
def earlyTest (out : Outcome Password Entropy Result) : Bool :=
  by classical exact decide (G2.Early (fromTrace out.adversaryQueries out.chain))

variable (password : Password) (container : State)
  (adversary : State → OracleComp (spec Password Entropy) Result) (tables : Tables Password Entropy)

def bSum : ENNReal :=
  ∑ round, if eventB password container adversary round tables then 1 else 0

def aSum : ENNReal :=
  ∑ round, if eventA password container adversary round tables then 1 else 0

def hSum : ENNReal :=
  ∑ index, if eventH password container adversary index tables then 1 else 0

theorem one_le_indicator_sum {ι : Type} [Fintype ι] (event : ι → Bool)
    (witness : ∃ i, event i = true) : (1 : ENNReal) ≤ ∑ i, if event i then 1 else 0 := by
  obtain ⟨i, found⟩ := witness
  have bound := Finset.single_le_sum
    (f := fun j => (if event j then 1 else 0 : ENNReal))
    (fun j _ => zero_le) (Finset.mem_univ i)
  simpa only [found, Bool.true_eq, ↓reduceIte] using bound

theorem indicator_union (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    (if earlyTest (outcome password container tables adversary) then 1 else 0 : ENNReal) ≤
      bSum password container adversary tables + aSum password container adversary tables +
        hSum password container adversary tables := by
  classical
  by_cases early : G2.Early (chronologicalRun password container tables adversary)
  · have enabled : earlyTest (outcome password container tables adversary) = true := by
      exact decide_eq_true early
    rw [enabled]; simp only [↓reduceIte]
    rcases G3Events.coverage password container tables adversary early with hit | hit | hit
    · exact (one_le_indicator_sum _ hit).trans (le_add_of_nonneg_right (zero_le) |>.trans
        (le_add_of_nonneg_right (zero_le)))
    · exact (one_le_indicator_sum _ hit).trans (le_add_of_nonneg_left (zero_le) |>.trans
        (le_add_of_nonneg_right (zero_le)))
    · exact (one_le_indicator_sum _ hit).trans (le_add_of_nonneg_left (zero_le))
  · have disabled : earlyTest (outcome password container tables adversary) = false := by
      exact decide_eq_false early
    simp only [disabled, Bool.false_eq_true, ↓reduceIte, zero_le]

omit [DecidableEq Password] [DecidableEq Entropy] in
/-- Every nonterminal next-round B count is part of the twelve-round partition. -/
theorem nonterminal_b_count (trace : List (Point Password Entropy)) :
    (∑ index : Fin 11, trace.countP (bFor (hNext index))) ≤ trace.countP isB := by
  rw [← b_partition]
  rw [Fin.sum_univ_castSucc (fun round : Fin 12 => trace.countP (bFor round))]
  change (∑ index : Fin 11, trace.countP (bFor index.castSucc)) ≤
    (∑ index : Fin 11, trace.countP (bFor index.castSucc)) + trace.countP (bFor (Fin.last 11))
  omega

/-- The older-round private terms total exactly 66, not a per-query birthday bound. -/
theorem salt_count_sum (count : Nat) :
    (∑ round : Fin 12, (count + (11 - round.val))) = 12 * count + 66 := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, older_round_count]
  norm_num

theorem div_sum {ι : Type} [Fintype ι] (count : ι → Nat) (denominator : ENNReal) :
    (∑ i, (count i : ENNReal) / denominator) = (∑ i, count i : Nat) / denominator := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Nat.cast_sum]

end G3Sums

/-! Assemble the source G3 probability bound over the actual Gamma2 execution. -/
/-! Keep the nonterminal B sum explicit for K3's extra forward finalization. -/
namespace G3Refined
open Gamma2Model G3Programs G3Sums QueryCounts
open GameExpectation MomentTools
variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

theorem union_counts_refined (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    moment sampleTables (fun tables => if earlyTest (outcome password container tables adversary) then 1 else 0) ≤
    moment sampleTables (fun tables =>
      ((12 * (outcome password container tables adversary).adversaryQueries.countP (aFor password) + 66 : Nat) : ENNReal) /
        (2 ^ 128 : ENNReal) +
      ((outcome password container tables adversary).adversaryQueries.countP isH : ENNReal) / (2 ^ 256 : ENNReal) +
      ((∑ index : Fin 11, (outcome password container tables adversary).adversaryQueries.countP (bFor (hNext index)) : Nat) : ENNReal) /
        (2 ^ 128 : ENNReal)) := by
  calc
    _ ≤ moment sampleTables (fun tables => bSum password container adversary tables +
        aSum password container adversary tables + hSum password container adversary tables) :=
      mono _ _ _ (fun tables => indicator_union password container tables adversary)
    _ = (∑ round : Fin 12, moment sampleTables (fun tables => if eventB password container adversary round tables then 1 else 0)) +
        (∑ round : Fin 12, moment sampleTables (fun tables => if eventA password container adversary round tables then 1 else 0)) +
        (∑ index : Fin 11, moment sampleTables (fun tables => if eventH password container adversary index tables then 1 else 0)) := by
      simp only [bSum, aSum, hSum, MomentTools.add, finite_sum]
    _ ≤ (∑ round : Fin 12, moment sampleTables (fun tables =>
        (((outcome password container tables adversary).adversaryQueries.countP (aFor password) + (11 - round.val) : Nat) : ENNReal) / (2 ^ 128 : ENNReal))) +
        (∑ round : Fin 12, moment sampleTables (fun tables =>
        ((outcome password container tables adversary).adversaryQueries.countP (hFor round) : ENNReal) / (2 ^ 256 : ENNReal))) +
        (∑ index : Fin 11, moment sampleTables (fun tables =>
        ((outcome password container tables adversary).adversaryQueries.countP (bFor (hNext index)) : ENNReal) / (2 ^ 128 : ENNReal))) := by
      apply add_le_add
      · exact add_le_add (Finset.sum_le_sum (fun round _ => G3Probability.salt password container adversary round))
          (Finset.sum_le_sum (fun round _ => G3Probability.key password container adversary round))
      · exact Finset.sum_le_sum (fun index _ => G3Probability.mask password container adversary index)
    _ = moment sampleTables (fun tables =>
        ((12 * (outcome password container tables adversary).adversaryQueries.countP (aFor password) + 66 : Nat) : ENNReal) / (2 ^ 128 : ENNReal) +
        ((outcome password container tables adversary).adversaryQueries.countP isH : ENNReal) / (2 ^ 256 : ENNReal) +
        ((∑ index : Fin 11, (outcome password container tables adversary).adversaryQueries.countP (bFor (hNext index)) : Nat) : ENNReal) / (2 ^ 128 : ENNReal)) := by
      rw [← finite_sum, ← finite_sum, ← finite_sum, ← MomentTools.add, ← MomentTools.add]
      congr 1
      funext tables
      rw [div_sum, div_sum, div_sum, salt_count_sum, h_partition]

end G3Refined

namespace G3Assembly
open Gamma2Model G3Programs G3Sums QueryCounts
open GameExpectation MomentTools
variable {Password Entropy Result : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2 ^ width)) (Lemma3.bitEquivFin width).symm

variable (passwords : PMF Password) (adversary : State → OracleComp (spec Password Entropy) Result)

/-- Lift a bound averaged over tables through the independent password and container sampling. -/
theorem game_transfer (f g : Outcome Password Entropy Result → ENNReal)
    (bound : ∀ password container, moment sampleTables (fun tables => f (outcome password container tables adversary)) ≤ moment sampleTables (fun tables => g (outcome password container tables adversary))) :
    moment (game passwords adversary) f ≤ moment (game passwords adversary) g := by
  simp only [game, MomentTools.bind, moment_map, Function.comp_def]
  apply mono
  intro password
  apply mono
  intro container
  exact bound password container

/-- Arbitrary finite PMF-averages respect pointwise bounds on actual generated outcomes. -/
theorem game_pointwise (f g : Outcome Password Entropy Result → ENNReal)
    (bound : ∀ password container tables, f (outcome password container tables adversary) ≤ g (outcome password container tables adversary)) :
    moment (game passwords adversary) f ≤ moment (game passwords adversary) g := by
  apply game_transfer
  intro password container
  exact mono _ _ _ (bound password container)

/-- Fixed budget bounds transfer to the actual game, even when other record values are arbitrary. -/
theorem game_budget (predicate : Point Password Entropy → Bool) (budget : Nat)
    (bounded : ∀ container tables, (execute tables (adversary container)).2.countP predicate ≤ budget) :
    moment (game passwords adversary)
      (fun out => (out.adversaryQueries.countP predicate : ENNReal)) ≤ (budget : ENNReal) := by
  calc
    _ ≤ moment (game passwords adversary) (fun _ => (budget : ENNReal)) := by
      apply game_pointwise
      intro password container tables
      exact_mod_cast bounded container tables
    _ = _ := constant _ _

/-- Sum the grouped per-table events and their corresponding round-specific counts. -/
theorem union_counts (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    moment sampleTables (fun tables => if earlyTest (outcome password container tables adversary) then 1 else 0) ≤
    moment sampleTables (fun tables =>
      ((12 * (outcome password container tables adversary).adversaryQueries.countP (aFor password) + 66 +
        (outcome password container tables adversary).adversaryQueries.countP isB : Nat) : ENNReal) /
        (2 ^ 128 : ENNReal) +
      ((outcome password container tables adversary).adversaryQueries.countP isH : ENNReal) / (2 ^ 256 : ENNReal)) := by
  apply (G3Refined.union_counts_refined password container adversary).trans
  apply mono
  intro tables
  have bound :
      (((∑ index : Fin 11, (outcome password container tables adversary).adversaryQueries.countP (bFor (hNext index)) : Nat) : ENNReal) / (2 ^ 128 : ENNReal)) ≤
      ((outcome password container tables adversary).adversaryQueries.countP isB : ENNReal) / (2 ^ 128 : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast nonterminal_b_count (outcome password container tables adversary).adversaryQueries) _
  calc
    _ ≤ ((12 * (outcome password container tables adversary).adversaryQueries.countP (aFor password) + 66 : Nat) : ENNReal) / (2 ^ 128 : ENNReal) +
        ((outcome password container tables adversary).adversaryQueries.countP isH : ENNReal) / (2 ^ 256 : ENNReal) +
        ((outcome password container tables adversary).adversaryQueries.countP isB : ENNReal) / (2 ^ 128 : ENNReal) := add_le_add le_rfl bound
    _ = _ := by
      simp only [Nat.cast_add, ENNReal.add_div]
      exact add_right_comm _ _ _

/-- Lemma G3 for the full typed Gamma2 game and any bounded deterministic adaptive adversary. -/
theorem lemma_g3 (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ container tables, (execute tables (adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables, (execute tables (adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables, (execute tables (adversary container)).2.countP isH ≤ qH) :
    ((game passwords adversary).map earlyTest) true ≤
      (12 * p1 * kA + 66 + qB) / (2 ^ 128 : ENNReal) + qH / (2 ^ 256 : ENNReal) := by
  rw [probability]
  calc
    _ ≤ moment (game passwords adversary) (fun out =>
        ((12 * out.adversaryQueries.countP (aFor out.password) + 66 + out.adversaryQueries.countP isB : Nat) : ENNReal) /
          (2 ^ 128 : ENNReal) + (out.adversaryQueries.countP isH : ENNReal) / (2 ^ 256 : ENNReal)) := by
      apply game_transfer
      exact fun password container => union_counts password container adversary
    _ = (12 * moment (game passwords adversary)
        (fun out => (out.adversaryQueries.countP (aFor out.password) : ENNReal)) + 66 +
        moment (game passwords adversary) (fun out => (out.adversaryQueries.countP isB : ENNReal))) /
        (2 ^ 128 : ENNReal) +
        moment (game passwords adversary) (fun out => (out.adversaryQueries.countP isH : ENNReal)) / (2 ^ 256 : ENNReal) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, MomentTools.add, div_const, constant]
      have scaled := mul_const (game passwords adversary)
        (fun out => (out.adversaryQueries.countP (aFor out.password) : ENNReal)) 12
      simpa only [mul_comm] using congrArg (fun x =>
        (x + 66 + moment (game passwords adversary) (fun out => (out.adversaryQueries.countP isB : ENNReal))) /
          (2 ^ 128 : ENNReal) + moment (game passwords adversary)
            (fun out => (out.adversaryQueries.countP isH : ENNReal)) / (2 ^ 256 : ENNReal)) scaled
    _ ≤ _ := by
      apply add_le_add
      · apply ENNReal.div_le_div_right
        apply add_le_add
        · apply add_le_add _ le_rfl
          simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_left
            (gamma2_password_count passwords adversary p1 largest kA budgetA) 12
        · exact game_budget passwords adversary isB qB budgetB
      · exact ENNReal.div_le_div_right (game_budget passwords adversary isH qH budgetH) _

end G3Assembly

/-!
Lemma G3, including randomized adaptive adversaries. Random coins select a
fixed deterministic oracle program independently of the password and tables.
The finite password-domain premise covers the specification's bounded byte
encodings; no finite dictionary or uniform password distribution is assumed.
-/
namespace G3
open Gamma2Model G3Sums G3Assembly
open GameExpectation MomentTools QueryCounts

/-- A finite superset of normalized encodings: at most 1024 bytes. -/
abbrev BoundedEncoding := { bytes : List (Fin 256) // bytes.length ≤ 1024 }

/-- Length and the complete byte vector retain the encoding without padding ambiguity. -/
def sizedEncoding (encoding : BoundedEncoding) :
    Σ length : Fin 1025, List.Vector (Fin 256) length.val :=
  ⟨⟨encoding.val.length, by have := encoding.property; omega⟩, ⟨encoding.val, rfl⟩⟩

theorem sizedEncoding_injective : Function.Injective sizedEncoding := by
  intro first second equal
  apply Subtype.ext
  exact congrArg (fun (encoded : Σ length : Fin 1025, List.Vector (Fin 256) length.val) => encoded.2.val) equal

instance : Fintype BoundedEncoding := Fintype.ofInjective sizedEncoding sizedEncoding_injective

variable {Password Entropy Result Strategy : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]

/-- Full random-coin execution: coins are selected independently before the oracle game. -/
def randomizedGame (coins : PMF Strategy) (passwords : PMF Password)
    (adversary : Strategy → State → OracleComp (spec Password Entropy) Result) :
    PMF (Outcome Password Entropy Result) :=
  coins.bind fun strategy => game passwords (adversary strategy)

/-- Source Lemma G3 for arbitrary independently randomized bounded adaptive programs. -/
theorem lemma_g3 (coins : PMF Strategy) (passwords : PMF Password)
    (adversary : Strategy → State → OracleComp (spec Password Entropy) Result) (p1 : ENNReal)
    (largest : ∀ password, passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ strategy container tables, (execute tables (adversary strategy container)).2.countP isA ≤ kA)
    (budgetB : ∀ strategy container tables, (execute tables (adversary strategy container)).2.countP isB ≤ qB)
    (budgetH : ∀ strategy container tables, (execute tables (adversary strategy container)).2.countP isH ≤ qH) :
    ((randomizedGame coins passwords adversary).map earlyTest) true ≤
      (12 * p1 * kA + 66 + qB) / (2 ^ 128 : ENNReal) + qH / (2 ^ 256 : ENNReal) := by
  rw [probability, randomizedGame, MomentTools.bind]
  apply bounded
  intro strategy
  rw [← probability]
  exact G3Assembly.lemma_g3 passwords (adversary strategy) p1 largest kA qB qH
    (budgetA strategy) (budgetB strategy) (budgetH strategy)

end G3

end
end MhfeLean
