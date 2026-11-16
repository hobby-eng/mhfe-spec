import Mathlib.Data.List.OfFn
import MhfeLean.Chapters.ChainCompletion
import MhfeLean.Chapters.CreationRefusal
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.PasswordPairs
import MhfeLean.Chapters.ShortSources
import MhfeLean.Chapters.WalletCollision

namespace MhfeLean
noncomputable section

/-! Typed fixed-batch queries can be reordered without changing their returned answer cache. -/
namespace BatchFetch
open TranscriptErasure
variable {Point : Type} [DecidableEq Point] {spec : OracleSpec Point}

/-- Fetch all listed points; the cache hides unqueried points behind its given initial values. -/
def fetch : List Point → Table spec → OracleComp spec (Table spec)
  | [],cache => pure cache
  | point::rest,cache => do
      let value ← ask (spec := spec) point
      fetch rest (Function.update cache point value)

/-- The cache records exactly the batch's oracle answers, including consistent repeated reads. -/
def filled (table : Table spec) (points : List Point) (initial : Table spec) : Table spec :=
  fun point => if point ∈ points then table point else initial point

/-- This identity retains both the exact reply cache and every query multiplicity. -/
theorem execution (table : Table spec) (points : List Point) (initial : Table spec) :
    execute table (fetch points initial)=(filled table points initial,points) := by
  induction points generalizing initial with
  | nil => rfl
  | cons point rest ih =>
    simp only [fetch,execute_bind,execute_ask]
    rw [ih]
    apply Prod.ext
    · funext query
      by_cases member : query ∈ rest
      · simp only [filled,member,List.mem_cons,or_true,if_true]
      · by_cases same : query=point
        · subst query
          simp only [filled,member,List.mem_cons,true_or,if_true,if_false,Function.update_self]
        · simp only [filled,member,List.mem_cons,same,false_or,if_false,Function.update_of_ne same]
    · rfl

/-- A permutation changes only request order; the adversary receives the same cache. -/
theorem reordered (table : Table spec) (points reorderedPoints : List Point)
    (permutation : points.Perm reorderedPoints) (initial : Table spec) :
    (execute table (fetch points initial)).1=(execute table (fetch reorderedPoints initial)).1 := by
  rw [execution,execution]
  funext point
  simp only [filled,permutation.mem_iff]

end BatchFetch

/-! An adaptive batch adversary commits each complete request list before receiving any of its replies. -/
namespace BatchProgram
open TranscriptErasure
variable {Point : Type} [DecidableEq Point] {spec : OracleSpec.{0,0} Point}

/-- The continuation receives answers only after the entire batch has been chosen. -/
inductive Program (spec : OracleSpec.{0,0} Point) (Result : Type) where
  | pure : Result → Program spec Result
  | batch : List Point → (Table spec → Program spec Result) → Program spec Result

/-- Stable partition places one oracle kind first without dropping duplicates. -/
def order (priority : Point → Bool) (points : List Point) : List Point :=
  points.filter priority ++ points.filter (fun point => !priority point)

def serialize (priority : Point → Bool) (batches : List (List Point)) : List Point := batches.flatMap (order priority)

/-- Full fixed-table batch execution retains the original batch boundaries and ordering. -/
def run (table initial : Table spec) : Program spec Result → Result × List (List Point)
  | .pure result => (result,[])
  | .batch points next =>
      let rest := run table initial (next (BatchFetch.filled table points initial))
      (rest.1,points::rest.2)

/-- A sequential oracle program restores the same reply cache before resuming the adversary. -/
def compile (priority : Point → Bool) (initial : Table spec) : Program spec Result → OracleComp spec Result
  | .pure result => pure result
  | .batch points next => do
      let replies ← BatchFetch.fetch (order priority points) initial
      compile priority initial (next replies)

private theorem filled_order (table initial : Table spec) (priority : Point → Bool)
    (points : List Point) :
    BatchFetch.filled table (order priority points) initial = BatchFetch.filled table points initial := by
  have equal := BatchFetch.reordered table (order priority points) points
    (List.filter_append_perm priority points) initial
  simpa only [BatchFetch.execution] using equal

/-- Serialization preserves every actual result for every table and records exactly the reordered queries. -/
theorem execution (table initial : Table spec) (priority : Point → Bool)
    (program : Program spec Result) :
    execute table (compile priority initial program) =
      ((run table initial program).1,serialize priority (run table initial program).2) := by
  induction program with
  | pure result => rfl
  | batch points next ih =>
    simp only [compile,execute_bind,BatchFetch.execution]
    rw [filled_order,ih]
    rfl

omit [DecidableEq Point] in
/-- Stable partition preserves all repeated queries across all batches. -/
theorem permutation (priority : Point → Bool) (batches : List (List Point)) :
    (serialize priority batches).Perm batches.flatten := by
  induction batches with
  | nil => exact List.Perm.refl _
  | cons batch rest ih =>
    exact (List.filter_append_perm priority batch).append ih

/-- Each individual oracle budget is unchanged; only scheduling within a committed batch changes. -/
theorem counts (table initial : Table spec) (priority kind : Point → Bool)
    (program : Program spec Result) :
    (execute table (compile priority initial program)).2.countP kind =
      (run table initial program).2.flatten.countP kind := by
  rw [execution]
  exact (permutation priority (run table initial program).2).countP_eq kind

end BatchProgram

/-! Count contiguous A groups after A-first serialization; deleting queries cannot increase this count. -/
namespace BatchRuns

/-- A true flag starts a new group exactly when the previous flag was false. -/
def runs : Bool → List Bool → Nat
  | _,[] => 0
  | previous,true::rest => (if previous then 0 else 1)+runs true rest
  | _,false::rest => runs false rest

/-- The initial preceding flag changes the count by at most one. -/
theorem start (flags : List Bool) :
    runs true flags ≤ runs false flags ∧ runs false flags ≤ runs true flags+1 := by
  cases flags with
  | nil => simp [runs]
  | cons value rest => cases value <;> (dsimp [runs]; omega)

/-- Inserting one flag never reduces the number of groups in the complete sequence. -/
theorem prepend (previous value : Bool) (flags : List Bool) :
    runs previous flags ≤ runs previous (value::flags) := by
  have estimate := start flags
  cases previous <;> cases value <;> dsimp [runs] <;> omega

/-- A chain embedded in the query transcript cannot have more A groups than that transcript. -/
theorem sublist {smaller larger : List Bool} (included : smaller.Sublist larger) (previous : Bool) :
    runs previous smaller ≤ runs previous larger := by
  induction included generalizing previous with
  | slnil => exact le_rfl
  | cons value included ih => exact (ih previous).trans (prepend previous value _)
  | cons_cons value included ih =>
    have beforeFalse := ih false
    have beforeTrue := ih true
    cases previous <;> cases value <;> dsimp [runs] <;> omega

/-- Concatenation may merge two adjacent groups but cannot create additional ones. -/
theorem append_bound (previous : Bool) (first second : List Bool) :
    runs previous (first++second) ≤ runs previous first+runs false second := by
  induction first generalizing previous with
  | nil =>
    simp only [List.nil_append,runs,zero_add]
    cases previous
    · exact le_rfl
    · exact (start second).1
  | cons value rest ih =>
    have beforeFalse := ih false
    have beforeTrue := ih true
    cases previous <;> cases value <;> dsimp [runs] <;> omega

private theorem zeros (previous : Bool) (count : Nat) : runs previous (List.replicate count false)=0 := by
  induction count generalizing previous with
  | zero => rfl
  | succ count ih => simpa only [List.replicate_succ,runs] using ih false

private theorem append_zeros (previous : Bool) (flags : List Bool) (count : Nat) :
    runs previous (flags++List.replicate count false)=runs previous flags := by
  induction flags generalizing previous with
  | nil => exact zeros previous count
  | cons value rest ih => cases value <;> simp only [List.cons_append,runs,ih]

private theorem ones_seen (count : Nat) : runs true (List.replicate count true)=0 := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [List.replicate_succ,runs] using ih

private theorem ones (count : Nat) : runs false (List.replicate count true)=(if count=0 then 0 else 1) := by
  cases count with
  | zero => rfl
  | succ count => simp [List.replicate_succ,runs,ones_seen]

/-- One serialized batch contributes exactly one A group if it has any A requests. -/
theorem batch (priority : Point → Bool) (points : List Point) :
    runs false ((BatchProgram.order priority points).map priority)=
      if (points.filter priority).length=0 then 0 else 1 := by
  have first : (points.filter priority).map priority=List.replicate (points.filter priority).length true := by
    apply List.map_eq_replicate_iff.mpr
    intro point member
    exact (List.mem_filter.mp member).2
  have second : (points.filter (fun point => !priority point)).map priority=
      List.replicate (points.filter (fun point => !priority point)).length false := by
    apply List.map_eq_replicate_iff.mpr
    intro point member
    have opposite := (List.mem_filter.mp member).2
    cases value : priority point <;> simp_all
  rw [BatchProgram.order,List.map_append,first,second,append_zeros,ones]

/-- Only batches with an A request count toward the depth constraint. -/
def occupied (priority : Point → Bool) (batches : List (List Point)) : Nat :=
  (batches.map (fun points => if (points.filter priority).length=0 then 0 else 1)).sum

/-- Arbitrarily many cheap-only batches do not increase the A-group bound. -/
theorem serialized (priority : Point → Bool) (batches : List (List Point)) :
    runs false ((BatchProgram.serialize priority batches).map priority) ≤ occupied priority batches := by
  induction batches with
  | nil => exact le_rfl
  | cons points rest ih =>
    change runs false (((BatchProgram.order priority points)++BatchProgram.serialize priority rest).map priority) ≤ _
    rw [List.map_append]
    apply (append_bound false _ _).trans
    rw [batch]
    exact Nat.add_le_add_left ih _

end BatchRuns

/-! The fixed-batch compiler instantiated on MHFE's actual four typed crypto oracles. -/
namespace BatchCrypto
open Gamma2Model QueryCounts
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

/-- Unqueried cache values are fixed zeros and carry no hidden oracle-table data. -/

def initial : TranscriptErasure.Table (spec Password Entropy)
  | .a _ _ => (0 : Key)
  | .b _ _ => (0 : Half)
  | .h _ _ _ => (0 : Half)
  | .g _ => (0 : Hash)

abbrev Adversary := State → BatchProgram.Program (spec Password Entropy) Result

local notation "WalletAdversary" => Adversary (Password := Password) (Entropy := Entropy) (Result := Result)

/-- The entire list is already committed before this compiler starts answering its A prefix. -/
def compiled (adversary : WalletAdversary) :=
  fun container => BatchProgram.compile isA initial (adversary container)

def batches (tables : Tables Password Entropy)
    (adversary : WalletAdversary) (container : State) :=
  (BatchProgram.run (answer tables) initial (adversary container)).2

/-- The actual MHFE oracle execution has exactly the original batch result and serialized query trace. -/
theorem execution (tables : Tables Password Entropy)
    (adversary : WalletAdversary) (container : State) :
    execute tables (compiled adversary container)=
      ((BatchProgram.run (answer tables) initial (adversary container)).1,
        BatchProgram.serialize isA (batches tables adversary container)) := by
  exact BatchProgram.execution (answer tables) initial isA (adversary container)

/-- All hard oracle caps transfer from the actual batch transcript, including every repeated query. -/
theorem counts (tables : Tables Password Entropy)
    (adversary : WalletAdversary)
    (container : State) (kind : Point Password Entropy → Bool) :
    (execute tables (compiled adversary container)).2.countP kind=
      (batches tables adversary container).flatten.countP kind := by
  exact BatchProgram.counts (answer tables) initial isA kind (adversary container)

/-- Cheap-only batches do not contribute to the resulting bound on expensive-query groups. -/
theorem a_groups (tables : Tables Password Entropy)
    (adversary : WalletAdversary) (container : State) :
    BatchRuns.runs false ((execute tables (compiled adversary container)).2.map isA) ≤
      BatchRuns.occupied isA (batches tables adversary container) := by
  rw [execution]
  exact BatchRuns.serialized isA (batches tables adversary container)

end BatchCrypto

/-! A no-Early completed chain embeds its first 35 points into the actual adversary transcript. -/
namespace ChainPrefix
open Gamma2Model G2 G4Order
variable {Point : Type} [DecidableEq Point]

omit [DecidableEq Point] in
/-- Strictly increasing matching positions give a genuine sublist, not only set membership. -/
theorem by_positions {n : Nat} (points : Fin n → Point) (queries : List Point)
    (position : Fin n → Fin queries.length) (ordered : StrictMono position)
    (agree : ∀ index,queries[(position index).val]=points index) :
    (List.ofFn points).Sublist queries := by
  have indices := List.map_getElem_sublist (l := queries) (is := List.ofFn position)
    (List.pairwise_ofFn.mpr ordered)
  simpa only [List.map_ofFn,Function.comp_def,Fin.getElem_fin,agree] using indices

variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] finalize

/-- The last A point suffices; the adversary need not query the terminal H0. -/
theorem all_queried (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (complete : Complete (chronologicalRun password container tables adversary)) (index : Nat)
    (within : index < 35) : Queried (chronologicalRun password container tables adversary) index := by
  have shape := G5.a_point password container tables adversary (⟨11,by omega⟩ : Fin 12)
  obtain ⟨salt,shape⟩ := shape
  change (chronologicalRun password container tables adversary).point 34=Point.a password salt at shape
  have last : Queried (chronologicalRun password container tables adversary) 34 :=
    complete 34 (by rw [chronologicalRun_count]; omega) (by rw [shape]; rfl)
  by_cases same : index=34
  · simpa only [same] using last
  · exact (all_ordered _ notEarly index 34 (by omega) (by rw [chronologicalRun_count]; omega)).trans last

/-- All retained positions refer to public adversary queries, before private finalization. -/
theorem actual (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (complete : Complete (chronologicalRun password container tables adversary)) :
    (List.ofFn (fun index : Fin 35 => (chronologicalRun password container tables adversary).point index.val)).Sublist
      (execute tables (adversary container)).2 := by
  let run := chronologicalRun password container tables adversary
  let queries := (execute tables (adversary container)).2
  have queried : ∀ index : Fin 35,Queried run index.val :=
    fun index => all_queried password container tables adversary notEarly complete index.val index.isLt
  let position : Fin 35 → Fin queries.length := fun index => ⟨firstTime run index.val,queried index⟩
  have ordered : StrictMono position := by
    intro first second before
    exact all_ordered run notEarly first.val second.val before (by rw [chronologicalRun_count]; have := second.isLt; omega)
  apply by_positions _ queries position ordered
  intro index
  have time : firstTime run index.val=queries.idxOf (run.point index.val) :=
    W4Terminal.queried_time password container tables adversary index.val (queried index)
  have member : run.point index.val ∈ queries := (queried_iff_mem _ _ index.val).mp (queried index)
  have lookup : queries[queries.idxOf (run.point index.val)]'(List.idxOf_lt_length_iff.mpr member)=run.point index.val :=
    List.getElem_idxOf (List.idxOf_lt_length_iff.mpr member)
  simpa only [position,time] using lookup

end ChainPrefix

/-! The actual completed inverse chain has twelve A groups separated by non-A queries. -/
namespace ChainRuns
open Gamma2Model G2 G4Order QueryCounts

/-- The indexed prefix agrees exactly with take, including its original point values. -/
theorem initial_segment {Value : Type} (values : List Value) (fallback : Value) (count : Nat)
    (within : count ≤ values.length) :
    List.ofFn (fun index : Fin count => values.getD index.val fallback)=values.take count := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take,Nat.min_eq_left within]
  · intro index left right
    simp only [List.getElem_ofFn,List.getElem_take]
    exact (List.getElem_eq_getD (h := lt_of_lt_of_le (by simpa only [List.length_ofFn] using left) within) fallback).symm

variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] finalize

/-- This is computed from the checked actual B/A/H chain labels, not assumed as a trace shape. -/
theorem twelve (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result) :
    BatchRuns.runs false
      ((List.ofFn (fun index : Fin 35 => (chronologicalRun password container tables adversary).point index.val)).map isA)=12 := by
  have size : (outcome password container tables adversary).chain.length=36 :=
    chronologicalRun_count password container tables adversary
  change BatchRuns.runs false
    ((List.ofFn (fun index : Fin 35 => (outcome password container tables adversary).chain.getD index.val fallbackPoint)).map isA)=12
  rw [initial_segment _ _ 35 (by omega)]
  have labels := congrArg (fun values => BatchRuns.runs false ((values.take 35).map ChainMetadata.isLabelA))
    (ChainMetadata.full_labels password container tables adversary)
  have kinds : (fun point : Point Password Entropy => ChainMetadata.isLabelA (ChainMetadata.label point))=isA := by
    funext point
    cases point <;> rfl
  simp only [List.map_take,List.map_map,Function.comp_def,kinds] at labels
  rw [List.map_take]
  apply labels.trans
  decide

/-- Existing sequential no-Early forces twelve separated A groups before finalization. -/
theorem lower (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : State → OracleComp (spec Password Entropy) Result)
    (notEarly : ¬ Early (chronologicalRun password container tables adversary))
    (complete : Complete (chronologicalRun password container tables adversary)) :
    12 ≤ BatchRuns.runs false ((execute tables (adversary container)).2.map isA) := by
  have included := (ChainPrefix.actual password container tables adversary notEarly complete).map isA
  have estimate := BatchRuns.sublist included false
  rw [twelve] at estimate
  exact estimate

end ChainRuns

/-! Completion in at most eleven A batches forces ordinary sequential Early in the actual A-first compiler. -/
namespace BatchDepth
open Gamma2Model G2 G4Order QueryCounts
variable {Password Entropy Result : Type} [DecidableEq Password] [DecidableEq Entropy]

/-- No assumption of distinct salts or keys is needed; repeated points are already covered by G2. -/
theorem forced (password : Password) (container : State) (tables : Tables Password Entropy)
    (adversary : BatchCrypto.Adversary (Password := Password) (Entropy := Entropy) (Result := Result))
    (depth : BatchRuns.occupied isA (BatchCrypto.batches tables adversary container) ≤ 11)
    (complete : Complete (chronologicalRun password container tables (BatchCrypto.compiled adversary))) :
    Early (chronologicalRun password container tables (BatchCrypto.compiled adversary)) := by
  by_contra notEarly
  have lower := ChainRuns.lower password container tables (BatchCrypto.compiled adversary) notEarly complete
  have upper := BatchCrypto.a_groups tables adversary container
  have impossible := lower.trans (upper.trans depth)
  omega

end BatchDepth

/-! G7 probability assembly for a sequential program whose real completion forces Early. -/
namespace DepthAssembly
open Gamma2Model G2 G4Order QueryCounts
open GameExpectation MomentTools ProbabilityTools

/-- An adaptive guess from an independent run cannot exceed the largest secret point mass. -/
theorem independent_guess {Password View : Type} [DecidableEq Password]
    (passwords : PMF Password) (views : PMF View) (guess : View → Password)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) :
    moment (independentPair passwords views) (fun world => if world.1=guess world.2 then 1 else 0) ≤ p1 := by
  have reversed : independentPair passwords views=views.bind fun view => passwords.map fun password => (password,view) :=
    PMF.bind_comm _ _ _
  rw [reversed,MomentTools.bind]
  apply bounded
  intro view
  rw [moment_map]
  change moment passwords (fun password => if password=guess view then 1 else 0) ≤ p1
  have singleton := PairMass.finite_membership passwords {guess view}
  simp only [Finset.mem_singleton,Finset.sum_singleton] at singleton
  rw [singleton]
  exact largest _

variable {N : Nat} {Entropy : Type} [DecidableEq Entropy] [Fintype Entropy]

def wins (out : Outcome (Fin N) Entropy (Fin N)) : Bool := decide (out.result=out.password)

/-- This counts one final guess and does not credit completed chains as an extra main term. -/
theorem guess_bound (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) : ((game passwords adversary).map wins) true ≤ p1 := by
  rw [probability,game_as_input_map,moment_map]
  simp only [Function.comp_def,wins,outcome,decide_eq_true_eq]
  simpa only [eq_comm] using
    independent_guess passwords (inputsLaw adversary)
      (fun inputs => (execute inputs.2 (adversary inputs.1)).1) p1 largest

/-- The actual compiler will discharge depth; the remaining probability terms are the existing G3/G4 bounds. -/
theorem bound (source : State → Entropy) (firstHalf : Entropy → Half)
    (projects : ∀ state,firstHalf (source state)=state.1) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N))
    (depth : ∀ password container tables,Complete (chronologicalRun password container tables adversary) → Early (chronologicalRun password container tables adversary))
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP isH ≤ qH)
    (budgetG : ∀ container tables,(execute tables (adversary container)).2.countP G4Programs.isG ≤ qG) :
    ((game passwords adversary).map (Theorem3Assembly.winOrBad source)) true ≤
      p1+(qG+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  classical
  have included : ((game passwords adversary).map (Theorem3Assembly.winOrBad source)) true ≤
      ((game passwords adversary).map wins) true+
      ((game passwords adversary).map G3Sums.earlyTest) true+
      ((game passwords adversary).map (G4.sourceTest source)) true := by
    rw [probability,probability,probability,probability,← MomentTools.add,← MomentTools.add]
    apply G3Assembly.game_pointwise
    intro password container tables
    by_cases hit : Theorem3Assembly.winOrBad source (outcome password container tables adversary)=true
    · rw [hit]
      have details := of_decide_eq_true hit
      rcases details with win | bad
      · have main : wins (outcome password container tables adversary)=true := decide_eq_true win
        rw [main]
        exact (le_add_of_nonneg_right (zero_le)).trans (le_add_of_nonneg_right (zero_le))
      · by_cases early : Early (chronologicalRun password container tables adversary)
        · have exceptional : G3Sums.earlyTest (outcome password container tables adversary)=true := decide_eq_true early
          rw [exceptional]
          exact (le_add_of_nonneg_left (zero_le)).trans (le_add_of_nonneg_right (zero_le))
        · have missing : ¬ Complete (chronologicalRun password container tables adversary) := fun complete => early (depth _ _ _ complete)
          have sourceBad : G4.sourceTest source (outcome password container tables adversary)=true :=
            decide_eq_true ⟨bad,missing,early⟩
          rw [sourceBad]
          exact le_add_of_nonneg_left (zero_le)
    · simp only [Bool.eq_false_iff.mpr hit,Bool.false_eq_true,if_false,zero_le]
  have estimate := add_le_add
    (add_le_add (guess_bound passwords adversary p1 largest)
      (G3Assembly.lemma_g3 passwords adversary p1 largest kA qB qH budgetA budgetB budgetH))
    (G4.lemma_g4_source source firstHalf projects passwords adversary qG budgetG)
  apply included.trans
  apply estimate.trans_eq
  simp only [ENNReal.add_div]
  abel

end DepthAssembly

/-! G7's source-game bound through an exact A-first batch compiler and the checked sequential G3/G4. -/
namespace G7
open Gamma2Model QueryCounts
variable {N : Nat} {E V R : Type} [DecidableEq E] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- The exact compiler retains batch answers/results; at most eleven A batches leave only the final guess and explicit exceptions. -/
theorem bound (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy state input)=input.1)
    (passwords : PMF (Fin N))
    (adversary : BatchCrypto.Adversary (Password := Fin N) (Entropy := E) (Result := Fin N))
    (depth : ∀ container tables,BatchRuns.occupied isA (BatchCrypto.batches tables adversary container) ≤ 11)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(BatchCrypto.batches tables adversary container).flatten.countP isA ≤ kA)
    (budgetB : ∀ container tables,(BatchCrypto.batches tables adversary container).flatten.countP isB ≤ qB)
    (budgetH : ∀ container tables,(BatchCrypto.batches tables adversary container).flatten.countP isH ≤ qH)
    (budgetG : ∀ container tables,(BatchCrypto.batches tables adversary container).flatten.countP G4Programs.isG ≤ qG) :
    (Theorem3.original state hash passwords (BatchCrypto.compiled adversary)) true ≤
      p1+(qG+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  apply (Theorem3.transfer state hash passwords (BatchCrypto.compiled adversary)).trans
  apply DepthAssembly.bound (Theorem3.entropy state) firstHalf projects passwords
    (BatchCrypto.compiled adversary)
    (fun password container tables => BatchDepth.forced password container tables adversary (depth container tables))
    p1 largest kA qB qH qG
  · intro container tables
    rw [BatchCrypto.counts]
    exact budgetA container tables
  · intro container tables
    rw [BatchCrypto.counts]
    exact budgetB container tables
  · intro container tables
    rw [BatchCrypto.counts]
    exact budgetH container tables
  · intro container tables
    rw [BatchCrypto.counts]
    exact budgetG container tables

end G7

/-! The numerical G7 bound retains the exact first creation-refusal allowance. -/
namespace G7Refused
open Gamma2Model QueryCounts
variable {N : Nat} {E V R : Type} [DecidableEq E] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- Only the first refusal contributes; the later owner response may be arbitrary. -/
theorem bound (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy state input)=input.1)
    (passwords : PMF (Fin N))
    (adversary : BatchCrypto.Adversary (Password := Fin N) (Entropy := E) (Result := Fin N))
    (later : ShortSourceEnvironment.Context (N := N) (E := E) × TableFactors.HTable → PMF Bool)
    (depth : ∀ container tables,BatchRuns.occupied isA (BatchCrypto.batches tables adversary container) ≤ 11)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(BatchCrypto.batches tables adversary container).flatten.countP isA ≤ kA)
    (budgetB : ∀ container tables,(BatchCrypto.batches tables adversary container).flatten.countP isB ≤ qB)
    (budgetH : ∀ container tables,(BatchCrypto.batches tables adversary container).flatten.countP isH ≤ qH)
    (budgetG : ∀ container tables,(BatchCrypto.batches tables adversary container).flatten.countP G4Programs.isG ≤ qG) :
    (ShortSourceRefusal.game state hash passwords (BatchCrypto.compiled adversary)
      (fun password _ result => decide (result=password)) later) true ≤
      p1+(qG+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal)+(2^256:ENNReal)⁻¹ := by
  have base := G7.bound state hash firstHalf projects passwords adversary depth p1 largest kA qB qH qG
    budgetA budgetB budgetH budgetG
  rw [ShortSourceEnvironment.password_original] at base
  exact ShortSourceRefusal.bound state hash passwords (BatchCrypto.compiled adversary) _ later _ base

end G7Refused

/-! Independent private coins preserve G7 with hard batch-depth and query caps for every strategy. -/
namespace G7Randomized
open Gamma2Model QueryCounts
variable {Strategy : Type} {N : Nat} {E V R : Type} [DecidableEq E] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- Query and depth constraints hold pathwise, not merely in expectation over the coins. -/
theorem bound (coins : PMF Strategy) (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy state input)=input.1)
    (passwords : PMF (Fin N))
    (adversary : Strategy → BatchCrypto.Adversary (Password := Fin N) (Entropy := E) (Result := Fin N))
    (later : Strategy → ShortSourceEnvironment.Context (N := N) (E := E) × TableFactors.HTable → PMF Bool)
    (depth : ∀ strategy container tables,BatchRuns.occupied isA (BatchCrypto.batches tables (adversary strategy) container) ≤ 11)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ strategy container tables,(BatchCrypto.batches tables (adversary strategy) container).flatten.countP isA ≤ kA)
    (budgetB : ∀ strategy container tables,(BatchCrypto.batches tables (adversary strategy) container).flatten.countP isB ≤ qB)
    (budgetH : ∀ strategy container tables,(BatchCrypto.batches tables (adversary strategy) container).flatten.countP isH ≤ qH)
    (budgetG : ∀ strategy container tables,(BatchCrypto.batches tables (adversary strategy) container).flatten.countP G4Programs.isG ≤ qG) :
    (coins.bind fun strategy => ShortSourceRefusal.game state hash passwords (BatchCrypto.compiled (adversary strategy))
      (fun password _ result => decide (result=password)) (later strategy)) true ≤
      p1+(qG+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal)+(2^256:ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact G7Refused.bound state hash firstHalf projects passwords (adversary strategy) (later strategy)
    (depth strategy) p1 largest kA qB qH qG (budgetA strategy) (budgetB strategy) (budgetH strategy) (budgetG strategy)

end G7Randomized

end
end MhfeLean
