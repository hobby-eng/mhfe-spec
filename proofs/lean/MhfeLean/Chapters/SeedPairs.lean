/- long: useful seed-query counting and both pair-search bounds share one experiment. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Data.Finset.Max
import MhfeLean.Chapters.ChainCompletion
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.KnownPairBound
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.PasswordPairs
import MhfeLean.Chapters.Probability
import MhfeLean.Chapters.ShortSources
import MhfeLean.Chapters.WalletCollision

namespace MhfeLean
noncomputable section

/-! # Seed queries, completed-password assignments and pair bounds
-/

/-! Retain only selected query metadata while preserving the entire actual execution. -/
namespace QueryCollector
variable {Point Metadata Result : Type} {spec : OracleSpec Point}

/-- Collection is observational: it makes exactly the same primitive queries and preserves their answers. -/
def collect (extract : Point → Option Metadata) (program : OracleComp spec Result) :
    OracleComp spec (Result × List Metadata) :=
  OracleComp.construct (fun result => pure (result,[]))
    (fun point _ recurse => do
      let answer ← TranscriptErasure.ask point
      let later ← recurse answer
      pure (later.1,(extract point).toList ++ later.2)) program

/-- The retained metadata is exactly filterMap of the genuine full query log, including repeated queries. -/
theorem execution (extract : Point → Option Metadata) (table : TranscriptErasure.Table spec)
    (program : OracleComp spec Result) :
    TranscriptErasure.execute table (collect extract program) =
      (((TranscriptErasure.execute table program).1,
        (TranscriptErasure.execute table program).2.filterMap extract),
       (TranscriptErasure.execute table program).2) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih =>
    change TranscriptErasure.execute table
      (do let answer ← TranscriptErasure.ask point
          let later ← collect extract (next answer)
          pure (later.1,(extract point).toList ++ later.2)) =
      (((TranscriptErasure.execute table (TranscriptErasure.ask point >>= next)).1,
        (TranscriptErasure.execute table (TranscriptErasure.ask point >>= next)).2.filterMap extract),
       (TranscriptErasure.execute table (TranscriptErasure.ask point >>= next)).2)
    simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,
      TranscriptErasure.execute_pure,ih,List.append_nil,List.singleton_append]
    cases selected : extract point <;> simp [selected]

/-- A query contributes one metadata entry exactly when its selector returns some value. -/
theorem count (extract : Point → Option Metadata) (queries : List Point) :
    (queries.filterMap extract).length = queries.countP (fun point => (extract point).isSome) := by
  induction queries with
  | nil => rfl
  | cons point rest ih => cases selected : extract point <;> simp [selected,ih]

end QueryCollector

/-! Seed-query metadata retained from the actual combined crypto/wallet trace. -/
namespace SeedQueryMetadata
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Wallet Result : Type}

/-- Crypto queries never contribute a wallet seed pair. -/
def extract (selector : Wallet → Option (Entropy × Passphrase)) :
    Point Password Entropy ⊕ Wallet → Option (Entropy × Passphrase)
  | .inl _ => none
  | .inr query => selector query

/-- Fixing independent wallet functions only partially evaluates their queries. -/
def retained (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (selector : Wallet → Option (Entropy × Passphrase))
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result) :=
  compile walletSpec wallet (QueryCollector.collect (extract selector) program)

/-- Every retained pair comes from the genuine trace, and every crypto query is preserved. -/
theorem execution (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
    (selector : Wallet → Option (Entropy × Passphrase)) (tables : Tables Password Entropy)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result) :
    execute tables (retained walletSpec wallet selector program) =
      let full := TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) program
      ((full.1,full.2.filterMap (extract selector)),W4TraceProjection.crypto full.2) := by
  rw [retained,WalletCryptoCompiler.execution,QueryCollector.execution]

/-- Repeated seed calls count repeatedly toward the resource budget. -/
theorem count (selector : Wallet → Option (Entropy × Passphrase))
    (queries : List (Point Password Entropy ⊕ Wallet)) :
    (queries.filterMap (extract selector)).length =
      queries.countP (fun point => (extract selector point).isSome) :=
  QueryCollector.count (extract selector) queries

end SeedQueryMetadata

/-! Typed S, T and wallet-data oracles of the wallet-check experiment. -/
namespace SeedWalletModel
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}

inductive Point (Entropy Passphrase Seed : Type)
  | s (entropy : Entropy) (phrase : Passphrase)
  | t (seed : Seed)
  | omega (seed : Seed)
  deriving DecidableEq

@[reducible] def spec (Entropy Passphrase Seed Check Tail Data : Type) :
    OracleSpec (Point Entropy Passphrase Seed)
  | .s _ _ => Seed
  | .t _ => Check × Tail
  | .omega _ => Data

structure Tables (Entropy Passphrase Seed Check Tail Data : Type) where
  s : Entropy × Passphrase → Seed
  t : Seed → Check × Tail
  omega : Seed → Data

def answer (tables : Tables Entropy Passphrase Seed Check Tail Data) :
    (point : Point Entropy Passphrase Seed) → spec Entropy Passphrase Seed Check Tail Data point
  | .s entropy phrase => tables.s (entropy,phrase)
  | .t seed => tables.t seed
  | .omega seed => tables.omega seed

def seedPair : Point Entropy Passphrase Seed → Option (Entropy × Passphrase)
  | .s entropy phrase => some (entropy,phrase)
  | _ => none

def blindSeed : Gamma2Model.Point Password Entropy ⊕ Point Entropy Passphrase Seed → Option Seed
  | .inr (.t seed) => some seed
  | .inr (.omega seed) => some seed
  | _ => none

def isT : Gamma2Model.Point Password Entropy ⊕ Point Entropy Passphrase Seed → Bool
  | .inr (.t _) => true
  | _ => false

def isOmega : Gamma2Model.Point Password Entropy ⊕ Point Entropy Passphrase Seed → Bool
  | .inr (.omega _) => true
  | _ => false

variable (queries : List (Gamma2Model.Point Password Entropy ⊕ Point Entropy Passphrase Seed))

/-- S entries are only the entropy/passphrase pairs actually submitted by the program. -/
def seedPairs :=
  queries.filterMap (SeedQueryMetadata.extract seedPair)

def blindSeeds :=
  queries.filterMap blindSeed

/-- Every T and Omega lookup contributes once, even at a previously queried seed. -/
theorem blind_count : (blindSeeds queries).length=queries.countP isT+queries.countP isOmega := by
  induction queries with
  | nil => rfl
  | cons point rest ih =>
    simp only [blindSeeds] at ih ⊢
    cases point with
    | inl point => simpa [blindSeed,isT,isOmega,List.filterMap_cons,List.countP_cons] using ih
    | inr point => cases point <;> simp [blindSeed,isT,isOmega,List.filterMap_cons,List.countP_cons] <;> omega

/-- The blind-test set is bounded by the two cheap query budgets, with no distinctness assumption. -/
theorem blind_bound [DecidableEq Seed]
    (queries : List (Gamma2Model.Point Password Entropy ⊕ Point Entropy Passphrase Seed))
    (qT qOmega : Nat) (tBudget : queries.countP isT ≤ qT)
    (omegaBudget : queries.countP isOmega ≤ qOmega) : (blindSeeds queries).toFinset.card ≤ qT+qOmega := by
  apply (List.toFinset_card_le _).trans
  rw [blind_count]
  omega

end SeedWalletModel

/-! Assign each seed query to the earliest completed eligible password, breaking ties by rank. -/
namespace PairAssignment
variable {N : Nat} {Value Passphrase : Type} [DecidableEq Value] [DecidableEq Passphrase]

def candidates (rows : Finset (Fin N)) (complete : Fin N → Prop) (value : Fin N → Value)
    (target : Value) : Finset (Fin N) := by
  classical
  exact rows.filter (fun password => complete password ∧ value password=target)

/-- Multiplication by N+1 encodes lexicographic order of completion time and password rank. -/
def score (time : Fin N → Nat) (password : Fin N) : Nat := time password*(N+1)+password.val

def selected (rows : Finset (Fin N)) (complete : Fin N → Prop) (value : Fin N → Value)
    (time : Fin N → Nat) (target : Value) : Option (Fin N) := by
  classical
  exact if present : (candidates rows complete value target).Nonempty then
    some (Classical.choose (Finset.exists_min_image (candidates rows complete value target) (score time) present)) else none

omit [DecidableEq Value] [DecidableEq Passphrase] in
theorem time_le (time : Fin N → Nat) (first second : Fin N)
    (ordered : score time first ≤ score time second) : time first ≤ time second := by
  unfold score at ordered
  by_contra notLe
  have gap : time second+1 ≤ time first := by omega
  have product := Nat.mul_le_mul_right (N+1) gap
  have rank := second.isLt
  nlinarith

omit [DecidableEq Passphrase] in
theorem selected_details (rows : Finset (Fin N)) (complete : Fin N → Prop) (value : Fin N → Value)
    (time : Fin N → Nat) (target : Value) (password : Fin N)
    (chosen : selected rows complete value time target=some password) :
    password ∈ rows ∧ complete password ∧ value password=target := by
  classical
  unfold selected at chosen
  split_ifs at chosen with present
  · have equal := Option.some.inj chosen
    have member := (Classical.choose_spec
      (Finset.exists_min_image (candidates rows complete value target) (score time) present)).1
    rw [equal] at member
    exact (Finset.mem_filter.mp member).1 |> fun row => ⟨row,(Finset.mem_filter.mp member).2⟩

omit [DecidableEq Passphrase] in
theorem selected_exists (rows : Finset (Fin N)) (complete : Fin N → Prop) (value : Fin N → Value)
    (time : Fin N → Nat) (target : Value) (real : Fin N) (eligible : real ∈ rows)
    (done : complete real) (agrees : value real=target) :
    ∃ other, selected rows complete value time target=some other ∧
      other ∈ rows ∧ complete other ∧ value other=target ∧ time other ≤ time real := by
  classical
  have member : real ∈ candidates rows complete value target := Finset.mem_filter.mpr ⟨eligible,done,agrees⟩
  have present : (candidates rows complete value target).Nonempty := ⟨real,member⟩
  let other := Classical.choose (Finset.exists_min_image (candidates rows complete value target) (score time) present)
  have specification := Classical.choose_spec
    (Finset.exists_min_image (candidates rows complete value target) (score time) present)
  have chosen : selected rows complete value time target=some other := by rw [selected,dif_pos present]
  have details := selected_details rows complete value time target other chosen
  exact ⟨other,chosen,details.1,details.2.1,details.2.2,time_le time other real (specification.2 real member)⟩

variable (rows : Finset (Fin N)) (complete : Fin N → Prop) (value : Fin N → Value)
  (time : Fin N → Nat) (queries : List (Value × Passphrase))

/-- At most one password is assigned to each actual seed-query pair. -/
def assigned : Finset (Fin N × Passphrase) :=
  (queries.filterMap (fun pair => (selected rows complete value time pair.1).map (fun password => (password,pair.2)))).toFinset

theorem pair_count : (assigned rows complete value time queries).card ≤ queries.length := by
  exact (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem row_subset : (assigned rows complete value time queries).image Prod.fst ⊆ rows := by
  intro password present
  obtain ⟨pair,member,equal⟩ := Finset.mem_image.mp present
  obtain ⟨query,_,chosen⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp member)
  cases selection : selected rows complete value time query.1 with
  | none => simp only [selection,Option.map_none] at chosen; cases chosen
  | some other =>
    simp only [selection,Option.map_some,Option.some.injEq] at chosen
    have details := selected_details rows complete value time query.1 other selection
    have same : other=password := (congrArg Prod.fst chosen).trans equal
    exact same ▸ details.1

/-- A real completed query is assigned to the real password, or to a colliding chain completed no later. -/
theorem covered (real : Fin N) (phrase : Passphrase) (eligible : real ∈ rows) (done : complete real)
    (queried : (value real,phrase) ∈ queries) :
    (real,phrase) ∈ assigned rows complete value time queries ∨
      ∃ other,other ≠ real ∧ complete other ∧ time other ≤ time real ∧ value other=value real := by
  obtain ⟨other,chosen,_,otherDone,equal,earlier⟩ := selected_exists rows complete value time (value real) real eligible done rfl
  by_cases same : other=real
  · left
    subst other
    apply List.mem_toFinset.mpr
    apply List.mem_filterMap.mpr
    exact ⟨(value real,phrase),queried,by rw [chosen]; rfl⟩
  · exact Or.inr ⟨other,same,otherDone,earlier,equal⟩

end PairAssignment

/-! Seed-query assignment instantiated with actual MHFE inverse chains and their completion times. -/
namespace ActualPairAssignment
open Gamma2Model QueryCounts G2 W4Model
variable {N : Nat} {Entropy Passphrase Result : Type} [DecidableEq Entropy] [DecidableEq Passphrase]

/-- Removing wallet reads preserves completion order, by W4TraceProjection.completion_le. -/
def assigned (source : State → Entropy) (container : State) (tables : Tables (Fin N) Entropy)
    (queries : List (Point (Fin N) Entropy)) (pairs : List (Entropy × Passphrase)) :=
  PairAssignment.assigned (CompletedPasswords.chosen queries)
    (fun password => W4Times.Complete queries (chain password container tables))
    (fun password => source (recovered password container tables))
    (fun password => W4Times.time queries (chain password container tables)) pairs

/-- Counts use actual multiplicities, so repeated salts never create a free eligible row. -/
theorem counts (source : State → Entropy) (container : State) (tables : Tables (Fin N) Entropy)
    (queries : List (Point (Fin N) Entropy)) (pairs : List (Entropy × Passphrase)) (kA kS : Nat)
    (budgetA : queries.countP isA ≤ kA) (budgetS : pairs.length ≤ kS) :
    ((assigned source container tables queries pairs).image Prod.fst).card ≤ kA/12 ∧
      (assigned source container tables queries pairs).card ≤ kS := by
  constructor
  · exact (Finset.card_le_card (PairAssignment.row_subset ..)).trans
      (CompletedPasswords.count queries kA budgetA)
  · exact (PairAssignment.pair_count ..).trans budgetS

attribute [local irreducible] finalize FinalCut.prepare

/-- Every real queried seed pair is assigned to the real password or to the precise W4 collision event. -/
theorem covered (source : State → Entropy) (injective : Function.Injective source) (real : Fin N)
    (phrase : Passphrase) (container : State) (tables : Tables (Fin N) Entropy)
    (adversary : State → OracleComp (spec (Fin N) Entropy) Result)
    (pairs : List (Entropy × Passphrase))
    (queried : (source (recovered real container tables),phrase) ∈ pairs)
    (notEarly : ¬ Early (chronologicalRun real container tables adversary))
    (terminal : Queried (chronologicalRun real container tables adversary) 35) :
    (real,phrase) ∈ assigned source container tables (execute tables (adversary container)).2 pairs ∨
      W4Coverage.test real container tables adversary=true := by
  classical
  have aComplete : G4Order.Complete (chronologicalRun real container tables adversary) := by
    by_contra missing
    have absent := G4Terminal.not_queried real container tables adversary notEarly missing
    have present := (G4Order.queried_iff_mem _ _ 35).mp terminal
    change (chronologicalRun real container tables adversary).point 35 ∈ (execute tables (adversary container)).2 at present
    rw [G4Terminal.last_point] at present
    exact absent present
  have eligible : real ∈ CompletedPasswords.chosen (execute tables (adversary container)).2 := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,G5.twelve_queries real container tables adversary notEarly aComplete⟩
  have realTime := real_time real container tables adversary notEarly terminal
  have realComplete := (W4Coverage.completion_some real container tables adversary _ realTime).1
  have assignment := PairAssignment.covered (CompletedPasswords.chosen (execute tables (adversary container)).2)
    (fun password => W4Times.Complete (execute tables (adversary container)).2 (chain password container tables))
    (fun password => source (recovered password container tables))
    (fun password => W4Times.time (execute tables (adversary container)).2 (chain password container tables))
    pairs real phrase eligible realComplete queried
  rcases assignment with member | collision
  · exact Or.inl member
  · right
    obtain ⟨other,different,otherComplete,earlier,equal⟩ := collision
    apply decide_eq_true
    refine ⟨?_,notEarly,terminal⟩
    refine ⟨other,_,_,different,?_,?_,earlier,injective equal⟩
    · exact if_pos otherComplete
    · exact if_pos realComplete

end ActualPairAssignment

/-! Actual H0 cut with a returned seed-query list, independent of the hidden passphrase. -/
namespace PairFreshPrograms
open Gamma2Model FinalCut G3Programs
open OracleProjection FocusedExecution OracleTree
open FreshSampling GameExpectation MomentTools
variable {Password Entropy Result Passphrase : Type} [DecidableEq Passphrase]
abbrev Context (Entropy Passphrase : Type) := Half × List (Entropy × Passphrase)

/-- Truncation only bounds off-budget contexts; it is redundant on real budget-respecting runs. -/
def matching (firstHalf : Entropy → Half) (kS : Nat) (context : Context Entropy Passphrase) :
    Finset (Half × Passphrase) :=
  (((context.2.take kS).map (fun pair => (context.1 ^^^ firstHalf pair.1,pair.2))).toFinset)

theorem size (firstHalf : Entropy → Half) (kS : Nat) (context : Context Entropy Passphrase) :
    (matching firstHalf kS context).card ≤ kS := by
  exact (List.toFinset_card_le _).trans (by rw [List.length_map]; exact List.length_take_le ..)

/-- Metadata is produced by the adversary's observable queries, not by a lookup of the hidden Q. -/
def program (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) (Result × List (Entropy × Passphrase))) :
    OracleComp (spec Password Entropy) ((Key × Fin 12 × Half) × Context Entropy Passphrase) := do
  let before ← adversary container
  let cut ← prepare password 11 container (by omega)
  pure ((cut.key,0,cut.state.1),(cut.state.2,before.2))

def focusedProgram (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) (Result × List (Entropy × Passphrase)))
    (others : OthersH Password Entropy) :=
  focused (focusH others.1 others.2.1 others.2.2) (program password container adversary)

omit [DecidableEq Passphrase] in
theorem execution (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) (Result × List (Entropy × Passphrase))) :
    execute tables (program password container adversary) =
      let before := execute tables (adversary container)
      let cut := (execute tables (prepare password 11 container (by omega))).1
      (((cut.key,0,cut.state.1),(cut.state.2,before.1.2)),before.2 ++ cut.before) := by
  simp only [program,execute_bind,execute_pure,List.append_nil,FinalCut.trace]

def event (firstHalf : Entropy → Half) (kS : Nat) (phrase : Passphrase) (password : Password)
    (container : State)
    (adversary : State → OracleComp (spec Password Entropy) (Result × List (Entropy × Passphrase)))
    (tables : Tables Password Entropy) : Bool :=
  FreshPairHit.hit (matching firstHalf kS) phrase
    (observedTable (focusedProgram password container adversary (tables.a,tables.b,tables.g)) tables.h)

local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

/-- The stopped mask and independent Q together give the factor s1, with no fresh-event conditioning. -/
theorem conditional_bound (firstHalf : Entropy → Half) (kS : Nat) (phrases : PMF Passphrase)
    (s1 : ENNReal) (largest : ∀ phrase,phrases phrase ≤ s1)
    (password : Password) (container : State)
    (adversary : State → OracleComp (spec Password Entropy) (Result × List (Entropy × Passphrase)))
    (others : OthersH Password Entropy) :
    moment (ProbabilityTools.independentPair phrases (PMF.uniformOfFintype (Key × Fin 12 × Half → Half)))
      (fun pair => if event firstHalf kS pair.1 password container adversary ⟨others.1,others.2.1,pair.2,others.2.2⟩ then 1 else 0) ≤
        s1*kS/(2^128:ENNReal) := by
  have bound := FreshPairHit.bound (focusedProgram password container adversary others) phrases
    (matching firstHalf kS) s1 largest kS (size firstHalf kS)
  rw [probability] at bound
  (try simp only [ProbabilityTools.independentPair,MomentTools.bind,moment_map, PMF.map_comp,Function.comp_def,event,G3Probability.card_bits,Nat.cast_pow,Nat.cast_ofNat] at bound ⊢)
  exact bound

end PairFreshPrograms

/-! The actual inverse source-half hit implies the weighted fresh-mask event. -/
namespace PairFreshHit
open Gamma2Model FinalCut PairFreshPrograms
open OracleTree OracleProjection FocusedExecution
open FreshSampling G3Fresh
variable {Password Entropy Result Passphrase : Type} [DecidableEq Passphrase]
attribute [local irreducible] prepare finalize

/-- A tested entropy/passphrase pair fixes a unique candidate for the unknown terminal mask. -/
theorem matching_has (firstHalf : Entropy → Half) (kS : Nat) (offset mask : Half)
    (queries : List (Entropy × Passphrase)) (entropy : Entropy) (phrase : Passphrase)
    (budget : queries.length ≤ kS) (queried : (entropy,phrase) ∈ queries)
    (agrees : firstHalf entropy=offset ^^^ mask) :
    (mask,phrase) ∈ matching firstHalf kS (offset,queries) := by
  unfold matching
  rw [List.take_of_length_le budget]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨(entropy,phrase),queried,?_⟩
  simp only [agrees,← BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]

set_option maxHeartbeats 1000000 in
/-- Only actual returned query metadata is used; the program itself never receives the hidden phrase. -/
theorem covered (firstHalf : Entropy → Half) (kS : Nat) (phrase : Passphrase)
    (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) (Result × List (Entropy × Passphrase)))
    (budget : (execute tables (adversary container)).1.2.length ≤ kS)
    (bad : ∃ entropy,(entropy,phrase) ∈ (execute tables (adversary container)).1.2 ∧
      firstHalf entropy=(outcome password container tables adversary).recovered.1)
    (notQueried : terminal (execute tables (prepare password 11 container (by omega))).1 ∉
      (execute tables (adversary container)).2) :
    event firstHalf kS phrase password container adversary tables=true := by
  let cut := (execute tables (prepare password 11 container (by omega))).1
  have cutResult := finalized password tables 11 (by omega) container
  obtain ⟨entropy,queried,sourceHalf⟩ := bad
  have recovered : (outcome password container tables adversary).recovered=finish tables cut := by
    dsimp only [outcome]
    with_reducible exact congrArg (fun output : State × List (Point Password Entropy) => output.1) cutResult
  have half : firstHalf entropy=cut.state.2 ^^^ tables.h (cut.key,0,cut.state.1) :=
    sourceHalf.trans (congrArg Prod.fst recovered)
  have isMatching := matching_has firstHalf kS cut.state.2 (tables.h (cut.key,0,cut.state.1))
    (execute tables (adversary container)).1.2 entropy phrase budget queried half
  have typedFresh : terminal cut ∉ (execute tables (program password container adversary)).2 := by
    rw [execution]
    simp only [List.mem_append,not_or]
    exact ⟨notQueried,terminal_absent password tables 11 (by omega) container cut.key cut.state.1⟩
  have focusedFresh := fresh_of_typed (focusH tables.a tables.b tables.g) tables.h tables
    (by intro point; cases point <;> rfl) (program password container adversary)
    (terminal cut) (cut.key,0,cut.state.1)
    (fun point found => identifiesH (tables.a,tables.b,tables.g) point (cut.key,0,cut.state.1) found) typedFresh
  have result := result_eq (focusH tables.a tables.b tables.g) tables.h tables
    (by intro point; cases point <;> rfl) (program password container adversary)
  rw [execution] at result
  have freshActual :
      (evaluate tables.h (focused (focusH tables.a tables.b tables.g) (program password container adversary))).1.1 ∉
      (evaluate tables.h (focused (focusH tables.a tables.b tables.g) (program password container adversary))).2 := by
    rw [result]
    exact focusedFresh
  unfold event observedTable selectFresh focusedProgram
  rw [if_neg freshActual]
  simp only [Option.map_some,FreshPairHit.hit,result]
  exact decide_eq_true isMatching

end PairFreshHit

/-! Weighted unknown-source seed hits for the actual combined wallet/crypto execution. -/
namespace PairFreshWallet
open Gamma2Model FinalCut WalletCryptoCompiler
open GameExpectation MomentTools ProbabilityTools
variable {Password Entropy Passphrase Wallet Result : Type} [DecidableEq Passphrase]
attribute [local irreducible] prepare finalize

/-- The hidden phrase is used only by the winning test, never supplied to the program. -/
def test (firstHalf : Entropy → Half) (walletSpec : OracleSpec Wallet)
    (wallet : (point : Wallet) → walletSpec point) (selector : Wallet → Option (Entropy × Passphrase))
    (phrase : Passphrase) (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result) : Bool := by
  classical
  let before := TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) (adversary container)
  let source := (execute tables (finalize password 12 container (by omega))).1.1
  exact decide ((∃ entropy,(entropy,phrase) ∈ before.2.filterMap (SeedQueryMetadata.extract selector) ∧
    firstHalf entropy=source.1) ∧
    terminal (execute tables (prepare password 11 container (by omega))).1 ∉ W4TraceProjection.crypto before.2)

/-- The actual full trace, including repeated S queries, supplies the bounded matching set. -/
theorem indicator_bound (firstHalf : Entropy → Half) (walletSpec : OracleSpec Wallet)
    (wallet : (point : Wallet) → walletSpec point) (selector : Wallet → Option (Entropy × Passphrase))
    (phrase : Passphrase) (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result)
    (kS : Nat) (budget :
      ((TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) (adversary container)).2.filterMap
        (SeedQueryMetadata.extract selector)).length ≤ kS) :
    (if test firstHalf walletSpec wallet selector phrase password container tables adversary then 1 else 0 : ENNReal) ≤
    if PairFreshPrograms.event firstHalf kS phrase password container
      (fun state => SeedQueryMetadata.retained walletSpec wallet selector (adversary state)) tables then 1 else 0 := by
  classical
  by_cases enabled : test firstHalf walletSpec wallet selector phrase password container tables adversary=true
  · have details :
        (∃ entropy,(entropy,phrase) ∈
          (TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) (adversary container)).2.filterMap
            (SeedQueryMetadata.extract selector) ∧
          firstHalf entropy=(execute tables (finalize password 12 container (by omega))).1.1.1) ∧
        terminal (execute tables (prepare password 11 container (by omega))).1 ∉
          W4TraceProjection.crypto
            (TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) (adversary container)).2 :=
        of_decide_eq_true enabled
    have hit := PairFreshHit.covered firstHalf kS phrase password container tables
      (fun state => SeedQueryMetadata.retained walletSpec wallet selector (adversary state))
      (by rw [SeedQueryMetadata.execution]; exact budget)
      (by
        obtain ⟨entropy,queried,agrees⟩ := details.1
        refine ⟨entropy,?_,agrees⟩
        rw [SeedQueryMetadata.execution]
        exact queried)
      (by rw [SeedQueryMetadata.execution]; exact details.2)
    simp only [enabled,hit,le_refl]
  · simp only [Bool.eq_false_iff.mpr enabled,Bool.false_eq_true,if_false,zero_le]

variable [Fintype Password] [DecidableEq Password] [Fintype Entropy] [DecidableEq Entropy]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

/-- Independent Q is guessed as well as the fresh 128-bit mask, in the real adaptive program. -/
theorem conditional_bound (firstHalf : Entropy → Half) (walletSpec : OracleSpec Wallet)
    (wallet : (point : Wallet) → walletSpec point) (selector : Wallet → Option (Entropy × Passphrase))
    (phrases : PMF Passphrase) (s1 : ENNReal) (largest : ∀ phrase,phrases phrase ≤ s1)
    (password : Password) (container : State)
    (adversary : State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) walletSpec) Result)
    (kS : Nat) (budget : ∀ tables,
      ((TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) (adversary container)).2.filterMap
        (SeedQueryMetadata.extract selector)).length ≤ kS) :
    moment (independentPair phrases (sampleTables (Password := Password) (Entropy := Entropy)))
      (fun pair => if test firstHalf walletSpec wallet selector pair.1 password container pair.2 adversary then 1 else 0) ≤
      s1*kS/(2^128:ENNReal) := by
  unfold independentPair
  rw [MomentTools.bind]
  simp only [moment_map]
  rw [TableFactors.factor_h]
  simp only [MomentTools.bind,moment_map]
  rw [MomentCommute.commute phrases (PMF.uniformOfFintype
    (TableFactors.ATable Password × TableFactors.BTable × TableFactors.GTable Entropy))]
  apply bounded
  intro others
  calc
    _ ≤ moment phrases (fun phrase => moment (PMF.uniformOfFintype TableFactors.HTable)
        (fun h => if PairFreshPrograms.event firstHalf kS phrase password container
          (fun state => SeedQueryMetadata.retained walletSpec wallet selector (adversary state))
          ⟨others.1,others.2.1,h,others.2.2⟩ then 1 else 0)) := by
      apply mono
      intro phrase
      apply mono
      intro h
      exact indicator_bound firstHalf walletSpec wallet selector phrase password container _ adversary kS (budget _)
    _ = moment (independentPair phrases (PMF.uniformOfFintype TableFactors.HTable))
        (fun pair => if PairFreshPrograms.event firstHalf kS pair.1 password container
          (fun state => SeedQueryMetadata.retained walletSpec wallet selector (adversary state))
          ⟨others.1,others.2.1,pair.2,others.2.2⟩ then 1 else 0) := by
      rw [independentPair,MomentTools.bind]
      simp only [moment_map,Function.comp_def]
    _ ≤ _ := PairFreshPrograms.conditional_bound firstHalf kS phrases s1 largest password container
      (fun state => SeedQueryMetadata.retained walletSpec wallet selector (adversary state)) others

end PairFreshWallet

/-! Actual Theta2 seed-query events share one independent public/oracle input law. -/
namespace SeedQueryRun
open Gamma2Model GameExpectation ProbabilityTools
open WalletCryptoCompiler
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase]
attribute [local irreducible] finalize FinalCut.prepare

abbrev WalletPoint := SeedWalletModel.Point Entropy Passphrase Seed
abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev WalletTables := SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data
abbrev Program := State → OracleComp (combinedSpec (Password := Fin N) (Entropy := Entropy)
  (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result
abbrev Input := State × Tables (Fin N) Entropy
abbrev World := (Fin N × Passphrase) × Input (N := N) (Entropy := Entropy)

local notation "WalletProgram" => Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data)

def compiled (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram) :=
  fun state => compile WalletSpec (SeedWalletModel.answer wallet) (adversary state)

def full (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram) (input : Input (N := N) (Entropy := Entropy)) :=
  TranscriptErasure.execute (combinedAnswer WalletSpec input.2 (SeedWalletModel.answer wallet)) (adversary input.1)

def pairs (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram) (input : Input (N := N) (Entropy := Entropy)) :=
  SeedWalletModel.seedPairs (full wallet adversary input).2

def assigned (source : State → Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram) (input : Input (N := N) (Entropy := Entropy)) :=
  ActualPairAssignment.assigned source input.1 input.2
    (execute input.2 (compiled wallet adversary input.1)).2 (pairs wallet adversary input)

def bad (source : State → Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram) (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase)) : Bool :=
  decide ((source (W4Model.recovered world.1.1 world.2.1 world.2.2),world.1.2) ∈ pairs wallet adversary world.2)

def early (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram) (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase)) : Bool :=
  G3Sums.earlyTest (outcome world.1.1 world.2.1 world.2.2 (compiled wallet adversary))

def collision (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram) (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase)) : Bool :=
  W4Coverage.test world.1.1 world.2.1 world.2.2 (compiled wallet adversary)

def fresh (firstHalf : Entropy → Half)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram) (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase)) : Bool :=
  PairFreshWallet.test firstHalf WalletSpec (SeedWalletModel.answer wallet)
    SeedWalletModel.seedPair world.1.2 world.1.1 world.2.1 world.2.2 adversary

/-- No-Early and a queried terminal H0 force assignment; otherwise use the unconditional fresh-half event. -/
theorem covered (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : WalletProgram)
    (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase))
    (hit : bad source wallet adversary world=true) :
    world.1 ∈ assigned source wallet adversary world.2 ∨ early wallet adversary world=true ∨
      fresh firstHalf wallet adversary world=true ∨ collision wallet adversary world=true := by
  classical
  have queried : (source (W4Model.recovered world.1.1 world.2.1 world.2.2),world.1.2) ∈
      pairs wallet adversary world.2 := of_decide_eq_true hit
  by_cases earlyCase : G2.Early (chronologicalRun world.1.1 world.2.1 world.2.2 (compiled wallet adversary))
  · exact Or.inr (Or.inl (decide_eq_true earlyCase))
  · by_cases terminalCase : FinalCut.terminal
        (execute world.2.2 (FinalCut.prepare world.1.1 11 world.2.1 (by omega))).1 ∈
          (execute world.2.2 (compiled wallet adversary world.2.1)).2
    · have terminal : G2.Queried (chronologicalRun world.1.1 world.2.1 world.2.2 (compiled wallet adversary)) 35 := by
        apply (G4Order.queried_iff_mem _ _ 35).mpr
        change (chronologicalRun world.1.1 world.2.1 world.2.2 (compiled wallet adversary)).point 35 ∈ _
        rw [G4Terminal.last_point]
        exact terminalCase
      rcases ActualPairAssignment.covered source injective world.1.1 world.1.2 world.2.1 world.2.2
        (compiled wallet adversary) (pairs wallet adversary world.2) queried earlyCase terminal with main | coll
      · exact Or.inl main
      · exact Or.inr (Or.inr (Or.inr coll))
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      unfold fresh PairFreshWallet.test
      simp only [decide_eq_true_eq]
      constructor
      · refine ⟨source (W4Model.recovered world.1.1 world.2.1 world.2.2),queried,projects _⟩
      · have projection := congrArg Prod.snd (WalletCryptoCompiler.execution WalletSpec
          (SeedWalletModel.answer wallet) world.2.2 (adversary world.2.1))
        dsimp only at projection
        rw [← projection]
        exact terminalCase

end SeedQueryRun

/-! Exact expectation identities for two hidden secrets and their independent run. -/
namespace PairViewMoments
open GameExpectation MomentTools ProbabilityTools

theorem without_second {First Second View : Type} (first : PMF First) (second : PMF Second)
    (views : PMF View) (value : First → View → ENNReal) :
    moment (independentPair (independentPair first second) views) (fun world => value world.1.1 world.2) =
      moment (independentPair first views) (fun world => value world.1 world.2) := by
  simp only [independentPair,MomentTools.bind,moment_map,Function.comp_def,constant]

theorem expand {First Second View : Type} (first : PMF First) (second : PMF Second)
    (views : PMF View) (value : (First × Second) × View → ENNReal) :
    moment (independentPair (independentPair first second) views) value =
      moment first (fun a => moment second (fun b => moment views (fun view => value ((a,b),view)))) := by
  simp only [independentPair,MomentTools.bind,moment_map,Function.comp_def]

end PairViewMoments

/-! W4 cache records and the shared primitive-query budgets count the same A calls. -/
namespace QueryCountBridge
open Gamma2Model

theorem a_count {Password Entropy : Type} (queries : List (Point Password Entropy)) :
    W4Cache.aCount queries=queries.countP QueryCounts.isA := by
  induction queries with
  | nil => rfl
  | cons point rest ih =>
    simp only [W4Cache.aCount] at ih ⊢
    cases point <;> simp [QueryCounts.isA,List.countP_cons] <;> omega

end QueryCountBridge

/-! The separate Theta2 event bounds are instantiated on the same actual full wallet program. -/
namespace SeedQueryBounds
open Gamma2Model GameExpectation MomentTools ProbabilityTools
open SeedQueryRun QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [Fintype Entropy] [DecidableEq Entropy] [DecidableEq Passphrase]
local instance (width : Nat) : Fintype (BitVec width) :=
  Fintype.ofEquiv (Fin (2^width)) (Lemma3.bitEquivFin width).symm

/-- Public Y and ideal crypto functions are independent of both secrets. -/
def views : PMF (Input (N := N) (Entropy := Entropy)) :=
  (PMF.uniformOfFintype State).bind fun container => sampleTables.map fun tables => (container,tables)

def worlds (passwords : PMF (Fin N)) (phrases : PMF Passphrase) :=
  independentPair (independentPair passwords phrases) (views (N := N) (Entropy := Entropy))

theorem inputs_equal (adversary : State → OracleComp (spec (Fin N) Entropy) Result) :
    inputsLaw adversary=views := by
  simp only [inputsLaw,adversaryView,PMF.map_bind,PMF.map_comp,Function.comp_def,views]

/-- Assignment size is counted on every run before applying independence of (P,Q). -/
theorem main_bound (source : State → Entropy) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data)) (kA kS : Nat)
    (budgetA : ∀ input : Input (N := N) (Entropy := Entropy),
      (execute input.2 (compiled wallet adversary input.1)).2.countP isA ≤ kA)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS) :
    moment (worlds passwords phrases) (fun world => if world.1 ∈ assigned source wallet adversary world.2 then 1 else 0) ≤
      W1.top2 passwords phrases (kA/12) kS := by
  apply PairMass.bounded passwords phrases sorted views (assigned source wallet adversary) (kA/12) kS
  · intro input
    exact (ActualPairAssignment.counts source input.1 input.2 _ _ kA kS (budgetA input) (budgetS input)).1
  · intro input
    exact (ActualPairAssignment.counts source input.1 input.2 _ _ kA kS (budgetA input) (budgetS input)).2

omit [DecidableEq Passphrase] in
/-- G3 carries over by partial evaluation of independent wallet functions, with identical crypto calls. -/
theorem early_bound (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isH ≤ qH) :
    moment (worlds passwords phrases) (fun world => if early wallet adversary world then 1 else 0) ≤
      (12*p1*kA+66+qB)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  change moment (independentPair (independentPair passwords phrases) views)
    (fun world => if G3Sums.earlyTest (outcome world.1.1 world.2.1 world.2.2 (compiled wallet adversary)) then 1 else 0) ≤ _
  rw [PairViewMoments.without_second passwords phrases views
    (fun password input => if G3Sums.earlyTest (outcome password input.1 input.2 (compiled wallet adversary)) then 1 else 0)]
  have bound := G3Assembly.lemma_g3 passwords (compiled wallet adversary) p1 largest kA qB qH budgetA budgetB budgetH
  rw [probability,game_as_input_map,moment_map,inputs_equal] at bound
  simpa only [Function.comp_def] using bound

/-- Q is sampled independently of every fixed wallet function and every stage of real finalization. -/
theorem fresh_bound (firstHalf : Entropy → Half) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (s1 : ENNReal) (largest : ∀ phrase,phrases phrase ≤ s1) (kS : Nat)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS) :
    moment (worlds passwords phrases) (fun world => if fresh firstHalf wallet adversary world then 1 else 0) ≤
      s1*kS/(2^128:ENNReal) := by
  rw [worlds,PairViewMoments.expand]
  apply bounded
  intro password
  simp only [views,MomentTools.bind,moment_map,Function.comp_def]
  rw [MomentCommute.commute phrases (PMF.uniformOfFintype State)]
  apply bounded
  intro container
  have bound := PairFreshWallet.conditional_bound firstHalf WalletSpec
    (SeedWalletModel.answer wallet) SeedWalletModel.seedPair phrases s1 largest password container adversary kS
    (fun tables => budgetS (container,tables))
  (try simp only [independentPair,MomentTools.bind,moment_map,Function.comp_def,fresh] at bound ⊢)
  exact bound

variable [Inhabited (Fin N)]

omit [DecidableEq Passphrase] in
/-- W4 needs freshness only for the real chain, regardless of salt reuse in other chains. -/
theorem collision_bound (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data)) (kA : Nat)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA) :
    moment (worlds passwords phrases) (fun world => if collision wallet adversary world then 1 else 0) ≤
      (kA:ENNReal)/(2^128:ENNReal)+(kA:ENNReal)/(2^256:ENNReal) := by
  change moment (independentPair (independentPair passwords phrases) views)
    (fun world => if W4Coverage.test world.1.1 world.2.1 world.2.2 (compiled wallet adversary) then 1 else 0) ≤ _
  rw [PairViewMoments.without_second passwords phrases views
    (fun password input => if W4Coverage.test password input.1 input.2 (compiled wallet adversary) then 1 else 0)]
  simp only [independentPair,views,MomentTools.bind,moment_map,Function.comp_def]
  apply bounded
  intro password
  apply bounded
  intro container
  exact W4.conditional_bound password container (compiled wallet adversary) kA
    (fun tables => by rw [QueryCountBridge.a_count]; exact budgetA container tables)

end SeedQueryBounds

/-! One shared pointwise and probabilistic error envelope for the two Theta2 output games. -/
namespace SeedQueryEnvelope
open Gamma2Model GameExpectation MomentTools
open SeedQueryRun SeedQueryBounds QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase]

def errors (firstHalf : Entropy → Half)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase)) : ENNReal :=
  (if early wallet adversary world then 1 else 0)+(if fresh firstHalf wallet adversary world then 1 else 0)+
    (if collision wallet adversary world then 1 else 0)

/-- The candidate row is separated from all three unconditional exceptional-event bounds. -/
theorem pointwise (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase)) :
    (if bad source wallet adversary world then 1 else 0 : ENNReal) ≤
      (if world.1 ∈ assigned source wallet adversary world.2 then 1 else 0)+errors firstHalf wallet adversary world := by
  classical
  by_cases hit : bad source wallet adversary world=true
  · rw [hit]
    rcases covered source injective firstHalf projects wallet adversary world hit with main | e | f | c
    · rw [if_pos main]; exact le_add_of_nonneg_right (zero_le)
    · unfold errors
      rw [e]
      simp only [← add_assoc]
      exact ((le_add_of_nonneg_left (zero_le)).trans (le_add_of_nonneg_right (zero_le))).trans
        (le_add_of_nonneg_right (zero_le))
    · unfold errors
      rw [f]
      simp only [← add_assoc]
      exact (le_add_of_nonneg_left (zero_le)).trans (le_add_of_nonneg_right (zero_le))
    · unfold errors
      rw [c]
      simp only [← add_assoc]
      exact le_add_of_nonneg_left (zero_le)
  · simp only [Bool.eq_false_iff.mpr hit,Bool.false_eq_true,if_false,zero_le]

/-- An output guess is absorbed into the main set, rather than added as an exceptional event. -/
theorem with_extra (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (candidates : Input (N := N) (Entropy := Entropy) → Finset (Fin N × Passphrase))
    (contains : ∀ input,assigned source wallet adversary input ⊆ candidates input)
    (extra : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) → Bool)
    (extraCovered : ∀ world,extra world=true → world.1 ∈ candidates world.2)
    (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase)) :
    (if bad source wallet adversary world || extra world then 1 else 0 : ENNReal) ≤
      (if world.1 ∈ candidates world.2 then 1 else 0)+errors firstHalf wallet adversary world := by
  classical
  by_cases added : extra world=true
  · have member := extraCovered world added
    simp only [added,Bool.or_true,if_pos member]
    exact le_add_of_nonneg_right (zero_le)
  · simp only [Bool.eq_false_iff.mpr added,Bool.or_false]
    apply (pointwise source injective firstHalf projects wallet adversary world).trans
    apply add_le_add
    · by_cases member : world.1 ∈ assigned source wallet adversary world.2
      · rw [if_pos member,if_pos (contains world.2 member)]
      · rw [if_neg member]; exact zero_le
    · exact le_refl _

variable [Fintype Entropy] [Inhabited (Fin N)]

/-- These are exactly the core error terms in epsilon_W, before blind seed guesses and game transfers. -/
theorem bound (firstHalf : Entropy → Half) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH : Nat)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isH ≤ qH)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS) :
    moment (worlds passwords phrases) (errors firstHalf wallet adversary) ≤
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal) := by
  unfold errors
  rw [MomentTools.add,MomentTools.add]
  apply (add_le_add
    (add_le_add (early_bound passwords phrases wallet adversary p1 largestP kA qB qH budgetA budgetB budgetH)
      (fresh_bound firstHalf passwords phrases wallet adversary s1 largestQ kS budgetS))
    (collision_bound passwords phrases wallet adversary kA budgetA)).trans_eq
  simp only [add_mul,one_mul,ENNReal.add_div]
  abel

end SeedQueryEnvelope

/-! Full actual Theta2 Bad_S bound, before the hidden-seed, generation and refusal transfers. -/
namespace SeedQueryAssembly
open Gamma2Model GameExpectation MomentTools
open SeedQueryRun SeedQueryBounds QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [Fintype Entropy] [DecidableEq Entropy] [DecidableEq Passphrase] [Inhabited (Fin N)]

/-- The main term counts tested pairs, with one real-chain freshness/collision error budget. -/
theorem bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH : Nat)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isH ≤ qH)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS) :
    moment (worlds passwords phrases) (fun world => if bad source wallet adversary world then 1 else 0) ≤
      W1.top2 passwords phrases (kA/12) kS +
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal) := by
  classical
  have included :
      moment (worlds passwords phrases) (fun world => if bad source wallet adversary world then 1 else 0) ≤
      moment (worlds passwords phrases) (fun world => if world.1 ∈ assigned source wallet adversary world.2 then 1 else 0)+
      moment (worlds passwords phrases) (SeedQueryEnvelope.errors firstHalf wallet adversary) := by
    rw [← MomentTools.add]
    apply mono
    intro world
    exact SeedQueryEnvelope.pointwise source injective firstHalf projects wallet adversary world
  have main := main_bound source passwords phrases sorted wallet adversary kA kS
    (fun input => budgetA input.1 input.2) budgetS
  have errors := SeedQueryEnvelope.bound firstHalf passwords phrases wallet adversary p1 s1 largestP largestQ
    kA kS qB qH budgetA budgetB budgetH budgetS
  apply included.trans
  apply (add_le_add main errors).trans_eq
  abel

end SeedQueryAssembly

/-! Queries and final guesses cannot identify a uniform secret unused by the entire run. -/
namespace BlindTarget
open GameExpectation MomentTools ProbabilityTools
variable {View Target : Type} [DecidableEq Target] [Fintype Target] [Nonempty Target]

/-- The complete adaptive run is independent of the hidden target, not merely each separate query. -/
theorem bound (views : PMF View) (chosen : View → Finset Target) (limit : Nat)
    (size : ∀ view,(chosen view).card ≤ limit) :
    moment (independentPair views (PMF.uniformOfFintype Target))
      (fun world => if world.2 ∈ chosen world.1 then 1 else 0) ≤
      (limit:ENNReal)/(Fintype.card Target:ENNReal) := by
  rw [independentPair,MomentTools.bind]
  apply bounded
  intro view
  rw [moment_map]
  calc
    _ = ((chosen view).card:ENNReal)/(Fintype.card Target:ENNReal) := by
      have law := FreshSampling.uniform_hit_probability (chosen view)
      rw [probability] at law
      simpa only [Function.comp_def,decide_eq_true_eq] using law
    _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast size view) _

end BlindTarget

/-! Eliminating an independent hidden value unused by an event. -/
namespace PairMarginalMoment
open GameExpectation MomentTools ProbabilityTools

theorem ignore_second {First Second : Type} (first : PMF First) (second : PMF Second)
    (value : First → ENNReal) :
    moment (independentPair first second) (fun pair => value pair.1)=moment first value := by
  simp only [independentPair,MomentTools.bind,moment_map,Function.comp_def,constant]

end PairMarginalMoment

/-! One union argument for an independently hidden seed and run-dependent candidate sets. -/
namespace IndependentSeedUnion
open GameExpectation MomentTools ProbabilityTools
variable {View Seed : Type} [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]

/-- All interaction is inside the run; the target is sampled independently and used only by the test. -/
theorem bound (views : PMF View) (event : View → Bool) (chosen : View → Finset Seed)
    (test : View × Seed → Bool) (limit : Nat) (size : ∀ view,(chosen view).card ≤ limit)
    (main : ENNReal) (mainBound : moment views (fun view => if event view then 1 else 0) ≤ main)
    (covered : ∀ sample,test sample=true → event sample.1=true ∨ sample.2 ∈ chosen sample.1) :
    moment (independentPair views (PMF.uniformOfFintype Seed)) (fun sample => if test sample then 1 else 0) ≤
      main+(limit:ENNReal)/(Fintype.card Seed:ENNReal) := by
  have included :
      moment (independentPair views (PMF.uniformOfFintype Seed)) (fun sample => if test sample then 1 else 0) ≤
      moment (independentPair views (PMF.uniformOfFintype Seed)) (fun sample => if event sample.1 then 1 else 0)+
      moment (independentPair views (PMF.uniformOfFintype Seed)) (fun sample => if sample.2 ∈ chosen sample.1 then 1 else 0) := by
    rw [← MomentTools.add]
    apply mono
    intro sample
    by_cases hit : test sample=true
    · rw [hit]
      rcases covered sample hit with exceptional | member
      · rw [exceptional]; exact le_add_of_nonneg_right (zero_le)
      · rw [if_pos member]; exact le_add_of_nonneg_left (zero_le)
    · simp only [Bool.eq_false_iff.mpr hit,Bool.false_eq_true,if_false,zero_le]
  rw [PairMarginalMoment.ignore_second views (PMF.uniformOfFintype Seed)
    (fun view => if event view then 1 else 0)] at included
  exact included.trans (add_le_add mainBound (BlindTarget.bound views chosen limit size))

end IndependentSeedUnion

/-! Complete seed-output win-or-Bad bound in Theta2, before the generation/refusal coupling. -/
namespace Theta2SeedBound
open Gamma2Model GameExpectation MomentTools ProbabilityTools
open SeedQueryRun SeedQueryBounds QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [Fintype Entropy] [DecidableEq Entropy] [DecidableEq Passphrase] [Inhabited (Fin N)]
  [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]

def winOrBad (source : State → Entropy) (seedOutput : Result → Seed)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (sample : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) : Bool :=
  decide (seedOutput (full wallet adversary sample.1.2).1=sample.2 ∨ bad source wallet adversary sample.1=true ∨
    sample.2 ∈ SeedWalletModel.blindSeeds (full wallet adversary sample.1.2).2)

/-- T and Omega queries, plus the final seed output, target an independently sampled 512-bit seed. -/
theorem bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (seedOutput : Result → Seed)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isH ≤ qH)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS)
    (budgetT : ∀ input : Input (N := N) (Entropy := Entropy),(full wallet adversary input).2.countP SeedWalletModel.isT ≤ qT)
    (budgetOmega : ∀ input : Input (N := N) (Entropy := Entropy),(full wallet adversary input).2.countP SeedWalletModel.isOmega ≤ qOmega) :
    moment (independentPair (worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if winOrBad source seedOutput wallet adversary sample then 1 else 0) ≤
      W1.top2 passwords phrases (kA/12) kS +
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+
      (qT+qOmega)/(2^512:ENNReal)+(2^512:ENNReal)⁻¹ := by
  classical
  let chosen := fun world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) =>
    insert (seedOutput (full wallet adversary world.2).1)
      (SeedWalletModel.blindSeeds (full wallet adversary world.2).2).toFinset
  have seedQueries := SeedQueryAssembly.bound source injective firstHalf projects passwords phrases sorted
    wallet adversary p1 s1 largestP largestQ kA kS qB qH budgetA budgetB budgetH budgetS
  have estimate := IndependentSeedUnion.bound (worlds passwords phrases) (bad source wallet adversary) chosen
    (winOrBad source seedOutput wallet adversary) (qT+qOmega+1)
    (fun world => (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
      (SeedWalletModel.blind_bound _ qT qOmega (budgetT world.2) (budgetOmega world.2)) 1))
    _ seedQueries (fun sample hit => by
      have details := of_decide_eq_true hit
      rcases details with wins | badS | query
      · exact Or.inr (Finset.mem_insert.mpr (Or.inl wins.symm))
      · exact Or.inl badS
      · exact Or.inr (Finset.mem_insert_of_mem (List.mem_toFinset.mpr query)))
  apply estimate.trans_eq
  rw [seedWidth]
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,ENNReal.add_div,one_div]
  abel

end Theta2SeedBound

/-! The two exact final-pair-guess allowances in Theorem 5(b). -/
namespace PairOutputMass
open GameExpectation MomentTools ProbabilityTools
variable {N : Nat} {Passphrase View : Type} [DecidableEq Passphrase]

/-- A guess selected from the independent run has probability at most p1*s1. -/
theorem guess_bound (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (views : PMF View)
    (guess : View → Fin N × Passphrase) (p1 s1 : ENNReal)
    (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1) :
    moment (independentPair (independentPair passwords phrases) views)
      (fun world => if world.1=guess world.2 then 1 else 0) ≤ p1*s1 := by
  have identity := PairMass.exact_adaptive passwords phrases views (fun view => {guess view})
  simp only [Finset.mem_singleton] at identity
  rw [identity]
  apply bounded
  intro view
  simp only [W1.mass,Finset.sum_singleton]
  exact mul_le_mul' (largestP _) (largestQ _)

/-- The main candidate set and one free final guess give both bounds inside the stated minimum. -/
theorem bound (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (views : PMF View) (chosen : View → Finset (Fin N × Passphrase)) (guess : View → Fin N × Passphrase)
    (rows pairs : Nat) (rowBound : ∀ view,((chosen view).image Prod.fst).card ≤ rows)
    (pairBound : ∀ view,(chosen view).card ≤ pairs) (p1 s1 : ENNReal)
    (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1) :
    moment (independentPair (independentPair passwords phrases) views)
      (fun world => if world.1 ∈ insert (guess world.2) (chosen world.2) then 1 else 0) ≤
      min (W1.top2 passwords phrases (rows+1) (pairs+1))
        (W1.top2 passwords phrases rows pairs+p1*s1) := by
  classical
  apply le_min
  · apply PairMass.bounded passwords phrases sorted views
      (fun view => insert (guess view) (chosen view)) (rows+1) (pairs+1)
    · intro view
      rw [Finset.image_insert]
      exact (Finset.card_insert_le _ _).trans (by have := rowBound view; omega)
    · intro view
      exact (Finset.card_insert_le _ _).trans (by have := pairBound view; omega)
  · have included :
        moment (independentPair (independentPair passwords phrases) views)
          (fun world => if world.1 ∈ insert (guess world.2) (chosen world.2) then 1 else 0) ≤
        moment (independentPair (independentPair passwords phrases) views)
          (fun world => if world.1 ∈ chosen world.2 then 1 else 0) +
        moment (independentPair (independentPair passwords phrases) views)
          (fun world => if world.1=guess world.2 then 1 else 0) := by
      rw [← MomentTools.add]
      apply mono
      intro world
      by_cases member : world.1 ∈ insert (guess world.2) (chosen world.2)
      · rw [if_pos member]
        rcases Finset.mem_insert.mp member with equal | inside
        · rw [if_pos equal]; exact le_add_of_nonneg_left (zero_le)
        · rw [if_pos inside]; exact le_add_of_nonneg_right (zero_le)
      · rw [if_neg member]; exact zero_le
    exact included.trans (add_le_add
      (PairMass.bounded passwords phrases sorted views chosen rows pairs rowBound pairBound)
      (guess_bound passwords phrases views guess p1 s1 largestP largestQ))

end PairOutputMass

/-! Both final-pair allowances on the actual Theta2 program and completed-chain assignment. -/
namespace PairQueryBound
open Gamma2Model GameExpectation MomentTools
open SeedQueryRun SeedQueryBounds QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [Fintype Entropy] [DecidableEq Entropy] [DecidableEq Passphrase] [Inhabited (Fin N)]

def event (source : State → Entropy) (pairOutput : Result → Fin N × Passphrase)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase)) : Bool :=
  bad source wallet adversary world || decide (world.1=pairOutput (full wallet adversary world.2).1)

/-- The final output is a guess from the run, so it is counted in the main term instead of twice. -/
theorem bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (pairOutput : Result → Fin N × Passphrase)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH : Nat)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isH ≤ qH)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS) :
    moment (worlds passwords phrases) (fun world => if event source pairOutput wallet adversary world then 1 else 0) ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal) := by
  classical
  let guess := fun input : Input (N := N) (Entropy := Entropy) => pairOutput (full wallet adversary input).1
  let candidates := fun input => insert (guess input) (assigned source wallet adversary input)
  have envelope := fun world => SeedQueryEnvelope.with_extra source injective firstHalf projects wallet adversary
    candidates (fun _ => Finset.subset_insert _ _)
    (fun sample => decide (sample.1=guess sample.2))
    (fun sample correct => Finset.mem_insert.mpr (Or.inl (of_decide_eq_true correct))) world
  have included :
      moment (worlds passwords phrases) (fun world => if event source pairOutput wallet adversary world then 1 else 0) ≤
      moment (worlds passwords phrases) (fun world => if world.1 ∈ candidates world.2 then 1 else 0)+
      moment (worlds passwords phrases) (SeedQueryEnvelope.errors firstHalf wallet adversary) := by
    rw [← MomentTools.add]
    exact mono _ _ _ envelope
  have main := PairOutputMass.bound passwords phrases sorted views (assigned source wallet adversary) guess
    (kA/12) kS
    (fun input => (ActualPairAssignment.counts source input.1 input.2 _ _ kA kS (budgetA input.1 input.2) (budgetS input)).1)
    (fun input => (ActualPairAssignment.counts source input.1 input.2 _ _ kA kS (budgetA input.1 input.2) (budgetS input)).2)
    p1 s1 largestP largestQ
  have errors := SeedQueryEnvelope.bound firstHalf passwords phrases wallet adversary p1 s1 largestP largestQ
    kA kS qB qH budgetA budgetB budgetH budgetS
  apply included.trans
  apply (add_le_add main errors).trans_eq
  abel

end PairQueryBound

/-! Complete pair-output win-or-Bad bound in Theta2, before the generation/refusal coupling. -/
namespace Theta2PairBound
open Gamma2Model GameExpectation MomentTools ProbabilityTools
open SeedQueryRun SeedQueryBounds QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [Fintype Entropy] [DecidableEq Entropy] [DecidableEq Passphrase] [Inhabited (Fin N)]
  [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]

def winOrBad (source : State → Entropy) (pairOutput : Result → Fin N × Passphrase)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (sample : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) : Bool :=
  decide (pairOutput (full wallet adversary sample.1.2).1=sample.1.1 ∨ bad source wallet adversary sample.1=true ∨
    sample.2 ∈ SeedWalletModel.blindSeeds (full wallet adversary sample.1.2).2)

/-- The pair-output game counts a free pair guess but no free seed guess. -/
theorem bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (pairOutput : Result → Fin N × Passphrase)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isH ≤ qH)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS)
    (budgetT : ∀ input : Input (N := N) (Entropy := Entropy),(full wallet adversary input).2.countP SeedWalletModel.isT ≤ qT)
    (budgetOmega : ∀ input : Input (N := N) (Entropy := Entropy),(full wallet adversary input).2.countP SeedWalletModel.isOmega ≤ qOmega) :
    moment (independentPair (worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if winOrBad source pairOutput wallet adversary sample then 1 else 0) ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+
      (qT+qOmega)/(2^512:ENNReal) := by
  classical
  let chosen := fun world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) =>
    (SeedWalletModel.blindSeeds (full wallet adversary world.2).2).toFinset
  have pairQueries := PairQueryBound.bound source injective firstHalf projects passwords phrases sorted pairOutput
    wallet adversary p1 s1 largestP largestQ kA kS qB qH budgetA budgetB budgetH budgetS
  have estimate := IndependentSeedUnion.bound (worlds passwords phrases)
    (PairQueryBound.event source pairOutput wallet adversary) chosen
    (winOrBad source pairOutput wallet adversary) (qT+qOmega)
    (fun world => SeedWalletModel.blind_bound _ qT qOmega (budgetT world.2) (budgetOmega world.2))
    _ pairQueries (fun sample hit => by
      have details := of_decide_eq_true hit
      rcases details with wins | badS | query
      · left
        apply Bool.or_eq_true_iff.mpr
        exact Or.inr (decide_eq_true wins.symm)
      · left
        apply Bool.or_eq_true_iff.mpr
        exact Or.inl badS
      · exact Or.inr (List.mem_toFinset.mpr query))
  apply estimate.trans_eq
  rw [seedWidth]
  simp only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]

end Theta2PairBound

end
end MhfeLean
