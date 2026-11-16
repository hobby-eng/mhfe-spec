/- long: the exact generation comparison is kept with its probability estimates. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Tactic.Linarith
import MhfeLean.Chapters.GenerationCoupling
import MhfeLean.Chapters.GenerationSampling
import MhfeLean.Chapters.GenerationSurvival
import MhfeLean.Chapters.PasswordPairs

namespace MhfeLean
noncomputable section

/-! # Lemma W2: the full generation-distance bound
-/

/-! Each actual generation seed is retained in its following check-query point. -/
namespace GenerationLog
open WalletGeneration TranscriptErasure RejectedIndices
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]

/-- Even with repeated inputs, index 2i+1 of the actual loop log is T(S(e_i,q)). -/
theorem check_point (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (target : Check) (trials : List Entropy) (index : Nat)
    (within : index < count table q target trials) (e : Entropy) (atIndex : trials[index]? = some e) :
    (execute table (loop q target trials)).2[2*index+1]? = some (Point.t (table (Point.s e q))) := by
  induction trials generalizing index with
  | nil => simp only [List.getElem?_nil] at atIndex; cases atIndex
  | cons first rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
      subst e
      rw [execution_cons]
      dsimp only
      split_ifs <;> rfl
    | succ index =>
      simp only [List.getElem?_cons_succ] at atIndex
      rw [StoppedPrefix.count_cons] at within
      split_ifs at within with passed
      · omega
      · have next : index < count table q target rest := by omega
        rw [execution_cons]
        dsimp only
        rw [if_neg passed]
        have arithmetic : 2*(index+1)+1 = (2*index+1)+2 := by omega
        rw [arithmetic]
        have simpaTerm := ih index next atIndex
        (try simp only [List.getElem?_cons_succ, List.singleton_append] at simpaTerm ⊢)
        exact simpaTerm

end GenerationLog

/-! Erasure identities retaining the generation log and its indexed rejected seeds. -/
namespace GenerationErasure
open WalletGeneration WalletFinite WalletLaws TranscriptErasure
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]
abbrev Trace := Option (Selected Entropy Seed Tail) × List (Point Entropy Passphrase Seed)

def selectedContext (fallback : Selected Entropy Seed Tail)
    (trace : Trace (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail)) :
    RejectedSeedModel.Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) :=
  ((trace.2.length/2,trace.1.isSome),trace.1.getD fallback)

def seedPoint : Option (Point Entropy Passphrase Seed) → Option Seed
  | some (.t seed) => some seed
  | _ => none

def seedObservation {limit : Nat} (index : Fin limit) (fallback : Selected Entropy Seed Tail)
    (trace : Trace (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail)) :
    RejectedSeedModel.Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) × Option Seed :=
  let context := selectedContext fallback trace
  (context, if RejectedSeedModel.enabled index context then seedPoint trace.2[2*index.val+1]? else none)

/-- Rejected seeds depend only on the retained query log, with no unrecorded table lookup. -/
theorem seed_observation {limit : Nat} (q : Passphrase) (target : Check) (index : Fin limit)
    (raw : WalletErasureLaw.RawSeed (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) limit) :
    seedObservation index raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) =
      RejectedSeedModel.observe q target index raw := by
  have ctx : selectedContext raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) =
      WalletJointLaw.joint q target raw := rfl
  unfold seedObservation RejectedSeedModel.observe
  rw [ctx]
  dsimp only
  split_ifs with active
  · have countBound : index.val < RejectedIndices.count raw.1 q target (List.ofFn raw.2.1) := by
      have later := active.2
      change index.val+1 < RejectedIndices.count raw.1 q target (List.ofFn raw.2.1) at later
      omega
    have indexed : (List.ofFn raw.2.1)[index.val]? = some (raw.2.1 index) := by
      rw [List.getElem?_ofFn, dif_pos index.isLt]
    rw [GenerationLog.check_point raw.1 q target (List.ofFn raw.2.1) index.val countBound _ indexed]
    rfl
  · rfl

noncomputable section
variable [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

omit [Nonempty Entropy] in
/-- The entire retained generation trace may appear in the postprocessing of the erasure law. -/
theorem retained_erasure {Output : Type} (q : Passphrase) (target : Check) (trials : List Entropy)
    (postprocess : Trace (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) →
      WalletTables → Output) :
    (PMF.uniformOfFintype (WalletTables ×
      WalletTables)).map
      (fun tables => postprocess (execute tables.1 (loop q target trials)) (exchanged (loop q target trials) tables).2) =
    (PMF.uniformOfFintype (WalletTables ×
      WalletTables)).map
      (fun tables => postprocess (execute tables.1 (loop q target trials)) tables.2) :=
  erased_distribution (loop q target trials) postprocess

/-- Context contains trial vector and fallback; only private trace data are retained. -/
theorem sampled_erasure {Output : Type} (limit : Nat) (q : Passphrase) (target : Check)
    (postprocess : (Fin limit → Entropy) → Selected Entropy Seed Tail →
      Trace (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) →
      WalletTables → Output) :
    (PMF.uniformOfFintype (WalletErasureLaw.Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit)).bind
      (fun context => (PMF.uniformOfFintype (WalletTables ×
        WalletTables)).map
      (fun tables => postprocess context.1 context.2 (execute tables.1 (loop q target (List.ofFn context.1)))
        (exchanged (loop q target (List.ofFn context.1)) tables).2)) =
    (PMF.uniformOfFintype (WalletErasureLaw.Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit)).bind
      (fun context => (PMF.uniformOfFintype (WalletTables ×
        WalletTables)).map
      (fun tables => postprocess context.1 context.2 (execute tables.1 (loop q target (List.ofFn context.1))) tables.2)) := by
  congr 1
  funext context
  exact retained_erasure q target (List.ofFn context.1) (postprocess context.1 context.2)

end
end GenerationErasure

/-! The retained erasure law in the actual generator's raw-product sampling order. -/
namespace ErasureRawLaw
open WalletGeneration WalletFinite TranscriptErasure
open ProbabilityTools GenerationErasure
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)
abbrev Raws (limit : Nat) := WalletErasureLaw.RawSeed (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) limit
abbrev Contexts (limit : Nat) := WalletErasureLaw.Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

/-- All retained private log data are preserved when public read points are rerandomized. -/
theorem law {Output : Type} (limit : Nat) (q : Passphrase) (target : Check)
    (postprocess : (Fin limit → Entropy) → Selected Entropy Seed Tail →
      Trace (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) →
      WalletTables → Output) :
    (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).bind
      (fun raw => (PMF.uniformOfFintype (WalletTables)).map
      (fun fresh => postprocess raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1)))
        (exchanged (loop q target (List.ofFn raw.2.1)) (raw.1,fresh)).2)) =
    (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).bind
      (fun raw => (PMF.uniformOfFintype (WalletTables)).map
      (fun fresh => postprocess raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh)) := by
  let tablesLaw := PMF.uniformOfFintype (WalletTables)
  let contextsLaw := PMF.uniformOfFintype (Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit)
  have rawLaw : PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit) =
    independentPair tablesLaw contextsLaw := uniform_product
  have pairLaw : PMF.uniformOfFintype (WalletTables ×
    WalletTables) =
      independentPair tablesLaw tablesLaw := uniform_product
  have swapped (read : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit →
      WalletTables →
      WalletTables → Output) :
      (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).bind
        (fun raw => tablesLaw.map (fun fresh => read raw.2 raw.1 fresh)) =
      contextsLaw.bind (fun context => (PMF.uniformOfFintype (WalletTables ×
        WalletTables)).map
          (fun tables => read context tables.1 tables.2)) := by
    rw [rawLaw, pairLaw]
    simp only [independentPair, PMF.bind_map, PMF.bind_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact PMF.bind_comm tablesLaw contextsLaw _
  rw [swapped (fun context original fresh => postprocess context.1 context.2
    (execute original (loop q target (List.ofFn context.1)))
      (exchanged (loop q target (List.ofFn context.1)) (original,fresh)).2),
    swapped (fun context original fresh => postprocess context.1 context.2
      (execute original (loop q target (List.ofFn context.1))) fresh)]
  exact sampled_erasure limit q target postprocess

end ErasureRawLaw

/-! Every generation-read point is selected or belongs to an actual earlier trial. -/
namespace GenerationCoverage
open WalletGeneration TranscriptErasure RejectedTrials RejectedIndices
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]

theorem point_cases (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (target : Check) (trials : List Entropy) (chosen : Selected Entropy Seed Tail)
    (success : (execute table (loop q target trials)).1 = some chosen)
    (point : Point Entropy Passphrase Seed)
    (member : point ∈ (execute table (loop q target trials)).2) :
    point = Point.s chosen.entropy q ∨ point = Point.t chosen.seed ∨
      ∃ index e, trials[index]? = some e ∧ index+1 < count table q target trials ∧
        (point = Point.s e q ∨ point = Point.t (table (Point.s e q))) := by
  obtain ⟨rejected, rest, shape, trace, _⟩ := decomposition table q target trials chosen success
  have countEq : count table q target trials = rejected.length+1 := by
    unfold count
    rw [trace, log_length]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have selected := selected_values table q target trials chosen success
  rw [trace] at member
  obtain ⟨e, occurs, atTrial⟩ := List.mem_flatMap.mp member
  rcases List.mem_append.mp occurs with earlier | last
  · obtain ⟨index, inside, equal⟩ := List.mem_iff_getElem.mp earlier
    refine Or.inr (Or.inr ⟨index,e,?_,?_,?_⟩)
    · rw [shape, List.getElem?_append_left inside, List.getElem?_eq_getElem inside, equal]
    · omega
    · simpa only [trialLog, List.mem_cons, List.not_mem_nil, or_false] using atTrial
  · have same : e = chosen.entropy := by simpa only [List.mem_singleton] using last
    subst e
    have alternatives : point = Point.s chosen.entropy q ∨ point = Point.t chosen.seed := by
      simpa only [trialLog, List.mem_cons, List.not_mem_nil, or_false, selected.1] using atTrial
    rcases alternatives with first | second
    · exact Or.inl first
    · exact Or.inr (Or.inl second)

end GenerationCoverage

/-! Actual and erased oracle executions coincide off rejected-point intersections. -/
namespace ErasedAgreement
open WalletGeneration TranscriptErasure RejectedIndices
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

def publicTable (q : Passphrase) (target : Check) (trials : List Entropy)
    (chosen : Selected Entropy Seed Tail)
    (original fresh : WalletTables) :
    WalletTables :=
  restore q target (some chosen) (exchanged (loop q target trials) (original,fresh)).2

/-- Outside the erased generator-read points the public table is still the original one. -/
theorem point_agree (q : Passphrase) (target : Check) (trials : List Entropy)
    (chosen : Selected Entropy Seed Tail)
    (original fresh : WalletTables)
    (success : (execute original (loop q target trials)).1 = some chosen)
    (point : Point Entropy Passphrase Seed)
    (clean : point ∈ (execute original (loop q target trials)).2 →
      point = Point.s chosen.entropy q ∨ point = Point.t chosen.seed) :
    publicTable q target trials chosen original fresh point = original point := by
  have selected := selected_values original q target trials chosen success
  cases point with
  | s e v =>
    by_cases selectedPoint : e = chosen.entropy ∧ v = q
    · rcases selectedPoint with ⟨rfl,rfl⟩
      simpa only [publicTable, restore, and_self, if_true] using selected.1.symm
    · have unread : Point.s e v ∉ (execute original (loop q target trials)).2 := by
        intro read
        rcases clean read with same | impossible
        · cases same
          exact selectedPoint ⟨rfl,rfl⟩
        · cases impossible
      simp only [publicTable, restore, selectedPoint, if_false, exchanged, unread]
  | t seed =>
    by_cases selectedPoint : seed = chosen.seed
    · subst seed
      simpa only [publicTable, restore, if_true] using selected.2.symm
    · have unread : Point.t seed ∉ (execute original (loop q target trials)).2 := by
        intro read
        rcases clean read with impossible | same
        · cases impossible
        · cases same
          exact selectedPoint rfl
      simp only [publicTable, restore, selectedPoint, if_false, exchanged, unread]

/-- Avoiding each actual rejected pair of points suffices for identical complete adversary views. -/
theorem execution_agree (q : Passphrase) (target : Check) (trials : List Entropy)
    (chosen : Selected Entropy Seed Tail)
    (original fresh : WalletTables)
    (success : (execute original (loop q target trials)).1 = some chosen)
    (adversary : OracleComp (spec Entropy Passphrase Seed Check Tail) Result)
    (avoids : ∀ index e, trials[index]? = some e → index+1 < count original q target trials →
      Point.s e q ∉ (execute (publicTable q target trials chosen original fresh) adversary).2 ∧
      Point.t (original (Point.s e q)) ∉ (execute (publicTable q target trials chosen original fresh) adversary).2) :
    execute original adversary = execute (publicTable q target trials chosen original fresh) adversary := by
  apply execute_agree
  intro point queried
  apply (point_agree q target trials chosen original fresh success point ?_).symm
  intro read
  rcases GenerationCoverage.point_cases original q target trials chosen success point read with
    first | second | ⟨index, e, atIndex, earlier, rfl | rfl⟩
  · exact Or.inl first
  · exact Or.inr second
  · exact absurd queried (avoids index e atIndex earlier).1
  · exact absurd queried (avoids index e atIndex earlier).2

end ErasedAgreement

/-! Actual and erased capped experiments with the concrete adversary's entire result and query log. -/
namespace WalletExperiments
open WalletGeneration WalletFinite TranscriptErasure WalletLaws
open GenerationErasure GenerationRaw GameExpectation MomentTools
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)
abbrev Raws (limit : Nat) := GenerationRaw.Raws (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) limit
abbrev Adversary := Selected Entropy Seed Tail → OracleComp (spec Entropy Passphrase Seed Check Tail) Result

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)
local notation "WalletAdversary" => Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)

/-- An enlarged proof interface may depend on the chosen triple but never on private rejected trials. -/
def traceView (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (fallback : Selected Entropy Seed Tail)
    (trace : Trace (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail))
    (fresh : WalletTables) :=
  let chosen := trace.1.getD fallback
  (chosen,execute (restore q target (some chosen) fresh) (adversary chosen))

def traceBad (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (trials : Fin limit → Entropy) (fallback : Selected Entropy Seed Tail)
    (trace : Trace (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail))
    (fresh : WalletTables) : Bool :=
  let context := selectedContext fallback trace
  let queries := (execute (restore q target (some context.2) fresh) (adversary context.2)).2
  trace.1.isNone || decide (∃ index : Fin limit,
    (RejectedEntropyModel.enabled index context ∧ trials index ∈ WalletQuerySets.sSet q queries) ∨
    FiberMembership.test (fun _ : Unit => WalletQuerySets.tSet queries)
      ((),(seedObservation index fallback trace).2) = true)

/-- The concrete Bad indicator is trace-measurable, so its full probability transfers through erasure. -/
theorem bad_erasure (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).bind
      (fun raw => (PMF.uniformOfFintype (WalletTables)).map
      (fun fresh => traceBad limit q target adversary raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1)))
        (exchanged (loop q target (List.ofFn raw.2.1)) (raw.1,fresh)).2)) =
    (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).bind
      (fun raw => (PMF.uniformOfFintype (WalletTables)).map
      (fun fresh => traceBad limit q target adversary raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh)) :=
  ErasureRawLaw.law limit q target (traceBad limit q target adversary)

omit [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- Outside Bad the complete concrete adversary executions agree. -/
theorem same_off_bad (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (raw : Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)
    (fresh : WalletTables)
    (clean : traceBad limit q target adversary raw.2.1 raw.2.2
      (execute raw.1 (loop q target (List.ofFn raw.2.1)))
      (exchanged (loop q target (List.ofFn raw.2.1)) (raw.1,fresh)).2 = false) :
    let chosen := observe q target raw
    (chosen,execute raw.1 (adversary chosen)) =
      traceView q target adversary raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1)))
        (exchanged (loop q target (List.ofFn raw.2.1)) (raw.1,fresh)).2 := by
  have hasChoice : (execute raw.1 (loop q target (List.ofFn raw.2.1))).1.isNone = false := by
    have flags := Bool.or_eq_false_iff.mp clean
    exact flags.1
  cases selected : (execute raw.1 (loop q target (List.ofFn raw.2.1))).1 with
  | none => simp only [selected, Option.isNone_none] at hasChoice; cases hasChoice
  | some chosen =>
    have noHits : ¬ ∃ index : Fin limit,
      (RejectedEntropyModel.enabled index (WalletJointLaw.joint q target raw) ∧
        raw.2.1 index ∈ WalletQuerySets.sSet q
          (execute (ErasedAgreement.publicTable q target (List.ofFn raw.2.1) chosen raw.1 fresh) (adversary chosen)).2) ∨
      FiberMembership.test (fun _ : Unit => WalletQuerySets.tSet
          (execute (ErasedAgreement.publicTable q target (List.ofFn raw.2.1) chosen raw.1 fresh) (adversary chosen)).2)
        ((),(RejectedSeedModel.observe q target index raw).2) = true := by
      simp only [traceBad] at clean
      have originalFlags := (Bool.or_eq_false_iff.mp clean).2
      rw [decide_eq_false_iff_not] at originalFlags
      simpa only [selectedContext, WalletJointLaw.joint, WalletJointLaw.context, observe,
        selected, Option.getD_some, ErasedAgreement.publicTable,
        seed_observation] using originalFlags
    have agrees := ErasedAgreement.execution_agree q target (List.ofFn raw.2.1) chosen raw.1 fresh selected
      (adversary chosen) (by
        intro n e atIndex earlier
        have inside : n < limit := by
          have lengthBound := StoppedPrefix.count_bound raw.1 q target (List.ofFn raw.2.1)
          rw [List.length_ofFn] at lengthBound
          omega
        let index : Fin limit := ⟨n,inside⟩
        have candidate : raw.2.1 index = e := by
          rw [List.getElem?_ofFn, dif_pos inside] at atIndex
          exact Option.some.inj atIndex
        have active : RejectedEntropyModel.enabled index (WalletJointLaw.joint q target raw) := by
          constructor
          · change (execute raw.1 (loop q target (List.ofFn raw.2.1))).1.isSome = true
            rw [selected]; rfl
          · exact earlier
        constructor
        · intro member
          apply noHits
          refine ⟨index,Or.inl ⟨active,?_⟩⟩
          rw [WalletQuerySets.s_mem, candidate]
          exact member
        · intro member
          apply noHits
          refine ⟨index,Or.inr ?_⟩
          simp only [RejectedSeedModel.observe, RejectedSeedModel.enabled,
            RejectedEntropyModel.enabled] at active ⊢
          erw [if_pos active]
          simp only [FiberMembership.test, Option.any_some, decide_eq_true_eq,
            WalletQuerySets.t_mem]
          change Point.t (raw.1 (Point.s (raw.2.1 index) q)) ∈
            (execute (ErasedAgreement.publicTable q target (List.ofFn raw.2.1) chosen raw.1 fresh) (adversary chosen)).2
          rw [candidate]
          exact member)
    have simpaTerm := congrArg (fun result => (chosen,result)) agrees
    (try simp only [traceView, observe, selected, Option.getD_some] at simpaTerm ⊢)
    exact simpaTerm

end WalletExperiments

/-! Bound the actual fresh-representation Bad event by the two query budgets and the capped mean. -/
namespace WalletFreshHits
open WalletGeneration WalletFinite TranscriptErasure GameExpectation MomentTools
open WalletExperiments
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Contexts := GenerationHits.Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail)

local notation "WalletAdversary" => Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)
local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

def sMatching (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (fresh : WalletTables)
    (context : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail)) : Finset Entropy :=
  WalletQuerySets.sSet q (execute (restore q target (some context.2) fresh) (adversary context.2)).2

def tMatching (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (fresh : WalletTables)
    (context : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail)) : Finset Seed :=
  WalletQuerySets.tSet (execute (restore q target (some context.2) fresh) (adversary context.2)).2

omit [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- The fresh-representation Bad event is exactly cutoff or one of the two rejected-point unions. -/
theorem event_eq (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (fresh : WalletTables)
    (raw : Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit) :
    traceBad limit q target adversary raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh =
      (decide ((execute raw.1 (loop q target (List.ofFn raw.2.1))).1 = none) ||
        (decide (∃ index : Fin limit, GenerationHits.entropyEvent q target (sMatching q target adversary fresh) index raw = true) ||
        decide (∃ index : Fin limit, GenerationHits.seedEvent q target (tMatching q target adversary fresh) index raw = true))) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [traceBad, Bool.or_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none]
  simp only [GenerationHits.entropyEvent, GenerationHits.seedEvent,
    GenerationErasure.seed_observation]
  have entropyEvent (index : Fin limit) :
      FiberMembership.test (sMatching q target adversary fresh)
        (RejectedEntropyModel.observe q target index raw) = true ↔
      RejectedEntropyModel.enabled index (WalletJointLaw.joint q target raw) ∧
        raw.2.1 index ∈ sMatching q target adversary fresh (WalletJointLaw.joint q target raw) := by
    unfold RejectedEntropyModel.observe
    dsimp only
    split_ifs with active <;> simp [FiberMembership.test, active]
  simp only [entropyEvent, exists_or]
  rfl

private theorem indicators (first second third : Bool) :
    (if first || (second || third) then (1 : ENNReal) else 0) ≤
      (if first then 1 else 0) + (if second then 1 else 0) + (if third then 1 else 0) := by
  cases first <;> cases second <;> cases third <;> simp

/-- The fixed fresh table is independent of the entire raw generation, not just its selected triple. -/
theorem bound (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (fresh : WalletTables)
    (largeE : 2 ≤ Fintype.card Entropy) (largeD : 2 ≤ Fintype.card Seed)
    (kS qT : Nat) (sBudget : ∀ context, (sMatching q target adversary fresh context).card ≤ kS)
    (tBudget : ∀ context, (tMatching q target adversary fresh context).card ≤ qT) :
    (((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => traceBad limit q target adversary raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh)) true) ≤
      (GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target limit) true +
      ((kS : ENNReal)/((Fintype.card Entropy-1 : Nat) : ENNReal)) *
        GenerationCount.mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target +
      ((qT : ENNReal)/((Fintype.card Seed-1 : Nat) : ENNReal)) *
        GenerationCount.mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target := by
  let prior := PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)
  have indicatorBound :
      (prior.map (fun raw => traceBad limit q target adversary raw.2.1 raw.2.2
        (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh)) true ≤
      (prior.map (fun raw => decide ((execute raw.1 (loop q target (List.ofFn raw.2.1))).1 = none))) true +
      (prior.map (fun raw => decide (∃ index : Fin limit, GenerationHits.entropyEvent q target (sMatching q target adversary fresh) index raw = true))) true +
      (prior.map (fun raw => decide (∃ index : Fin limit, GenerationHits.seedEvent q target (tMatching q target adversary fresh) index raw = true))) true := by
    simp_rw [probability]
    rw [← MomentTools.add, ← MomentTools.add]
    apply MomentTools.mono
    intro raw
    rw [event_eq]
    exact indicators _ _ _
  have eBound := GenerationHits.entropy_union limit q target largeE (sMatching q target adversary fresh) kS sBudget
  have dBound := GenerationHits.seed_union limit q target largeD (tMatching q target adversary fresh) qT tBudget
  have combined := indicatorBound.trans (add_le_add (add_le_add le_rfl eBound) dBound)
  simpa only [prior, GenerationRaw.failure_law] using combined

end WalletFreshHits

/-! Complete whole-view comparison for the actually capped generation experiment. -/
namespace WalletCapped
open WalletGeneration WalletFinite TranscriptErasure WalletLaws
open WalletExperiments ProbabilityTools GameExpectation MomentTools
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev View := Selected Entropy Seed Tail × (Result × List (Point Entropy Passphrase Seed))

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)
local notation "WalletAdversary" => Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)

def actual (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    PMF (View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)) :=
  (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
    (fun raw => let chosen := observe q target raw; (chosen, execute raw.1 (adversary chosen)))

def planted (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    PMF (View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)) :=
  (PMF.uniformOfFintype (Selected Entropy Seed Tail)).bind fun chosen =>
    (PMF.uniformOfFintype (WalletTables)).map
      (fun fresh => (chosen,execute (restore q target (some chosen) fresh) (adversary chosen)))

/-- The entire erased view equals the programmed experiment, including its selected triple. -/
theorem erased_planted (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).bind
      (fun raw => (PMF.uniformOfFintype (WalletTables)).map
      (fun fresh => traceView q target adversary raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1)))
        (exchanged (loop q target (List.ofFn raw.2.1)) (raw.1,fresh)).2)) = planted q target adversary := by
  classical
  rw [ErasureRawLaw.law limit q target (fun _ fallback trace fresh => traceView q target adversary fallback trace fresh)]
  let kernel := fun chosen : Selected Entropy Seed Tail =>
    (PMF.uniformOfFintype (WalletTables)).map
      (fun fresh => (chosen,execute (restore q target (some chosen) fresh) (adversary chosen)))
  calc
    _ = (WalletLaws.law (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target).bind kernel := by
      simp only [WalletLaws.law, PMF.bind_map, Function.comp_def, kernel, traceView, observe]
    _ = _ := by rw [selected_uniform]; rfl

/-- The full capped experiment pays only the two actual query budgets and its genuine cutoff probability. -/
theorem close (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (largeE : 2 ≤ Fintype.card Entropy) (largeD : 2 ≤ Fintype.card Seed)
    (kS qT : Nat)
    (sBudget : ∀ chosen table, (WalletQuerySets.sSet q (execute table (adversary chosen)).2).card ≤ kS)
    (tBudget : ∀ chosen table, (WalletQuerySets.tSet (execute table (adversary chosen)).2).card ≤ qT) :
    StatisticalClose.Close (actual limit q target adversary) (planted q target adversary)
      ((GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target limit) true +
      ((kS : ENNReal)/((Fintype.card Entropy-1 : Nat) : ENNReal)) *
        GenerationCount.mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target +
      ((qT : ENNReal)/((Fintype.card Seed-1 : Nat) : ENNReal)) *
        GenerationCount.mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target) := by
  let rawLaw := PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)
  let tableLaw := PMF.uniformOfFintype (WalletTables)
  let prior := independentPair rawLaw tableLaw
  let original := fun pair : Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit ×
      WalletTables =>
    let chosen := observe q target pair.1
    (chosen,execute pair.1.1 (adversary chosen))
  let erased := fun pair : Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit ×
      WalletTables =>
    traceView q target adversary pair.1.2.2 (execute pair.1.1 (loop q target (List.ofFn pair.1.2.1)))
      (exchanged (loop q target (List.ofFn pair.1.2.1)) (pair.1.1,pair.2)).2
  let bad := fun pair : Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit ×
      WalletTables =>
    traceBad limit q target adversary pair.1.2.1 pair.1.2.2 (execute pair.1.1 (loop q target (List.ofFn pair.1.2.1)))
      (exchanged (loop q target (List.ofFn pair.1.2.1)) (pair.1.1,pair.2)).2
  have coupled := StatisticalClose.coupling prior original erased bad
    (fun pair clean => same_off_bad limit q target adversary pair.1 pair.2 clean)
  have originalLaw : prior.map original = actual limit q target adversary := by
    simp only [prior, independentPair, original, PMF.map_bind, PMF.map_comp, Function.comp_def]
    have drop (raw : Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit) :
      tableLaw.map (fun _ => (observe q target raw, execute raw.1 (adversary (observe q target raw)))) =
        PMF.pure (observe q target raw, execute raw.1 (adversary (observe q target raw))) := PMF.map_const _ _
    simp_rw [drop]
    rfl
  have erasedLaw : prior.map erased = planted q target adversary := by
    simpa only [prior, independentPair, erased, rawLaw, tableLaw, PMF.map_bind, PMF.map_comp, Function.comp_def] using
      erased_planted limit q target adversary
  rw [originalLaw, erasedLaw] at coupled
  apply StatisticalClose.mono _ _ _ _ coupled
  have law := bad_erasure limit q target adversary
  have freshLaw : prior.map bad = rawLaw.bind (fun raw => tableLaw.map
      (fun fresh => traceBad limit q target adversary raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh)) := by
    simpa only [prior, independentPair, bad, rawLaw, tableLaw, PMF.map_bind, PMF.map_comp, Function.comp_def] using law
  rw [freshLaw]
  have swapped : rawLaw.bind (fun raw => tableLaw.map
      (fun fresh => traceBad limit q target adversary raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh)) =
      tableLaw.bind (fun fresh => rawLaw.map (fun raw => traceBad limit q target adversary raw.2.1 raw.2.2
        (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh)) := by
    have simpaTerm := PMF.bind_comm rawLaw tableLaw (fun raw fresh => PMF.pure (traceBad limit q target adversary raw.2.1 raw.2.2 (execute raw.1 (loop q target (List.ofFn raw.2.1))) fresh))
    (try simp only [PMF.map] at simpaTerm ⊢)
    exact simpaTerm
  rw [swapped, PMF.bind_apply]
  apply MomentTools.bounded tableLaw
  intro fresh
  exact WalletFreshHits.bound limit q target adversary fresh largeE largeD kS qT
    (fun context => sBudget context.2 _) (fun context => tBudget context.2 _)

end WalletCapped

/-! Replacing only the fallback of a failed finite search changes whole output by at most its failure probability. -/
namespace CompletionCoupling
open StatisticalClose GameExpectation MomentTools
variable {Context Value Output : Type}

theorem universal (first second : PMF Output) : Close first second 1 := by
  intro test
  exact ⟨(PMF.coe_le_one _ _).trans (le_add_self), (PMF.coe_le_one _ _).trans (le_add_self)⟩

/-- No relationship between the two fallback distributions is required. -/
theorem local_bound (choice : Option Value) (first second : PMF Value) (view : Value → Output) :
    Close (first.map (fun fallback => view (choice.getD fallback)))
      (second.map (fun fallback => view (choice.getD fallback))) (if choice.isNone then 1 else 0) := by
  cases choice with
  | none => exact universal _ _
  | some value =>
    have drop (distribution : PMF Value) : distribution.map (fun fallback => view ((some value).getD fallback)) = PMF.pure (view value) :=
      PMF.map_const distribution (view value)
    rw [drop, drop]
    exact of_eq _ _ rfl

/-- Retaining the entire context and any later view is permitted in this comparison. -/
theorem bound (prior : PMF Context) (choice : Context → Option Value)
    (first second : Context → PMF Value) (view : Context → Value → Output) :
    Close (prior.bind (fun context => (first context).map (fun fallback => view context ((choice context).getD fallback))))
      (prior.bind (fun context => (second context).map (fun fallback => view context ((choice context).getD fallback))))
      ((prior.map (fun context => (choice context).isNone)) true) := by
  rw [probability]
  exact CloseComposition.bind prior _ _ _ (fun context => local_bound (choice context) (first context) (second context) (view context))

end CompletionCoupling

/-! Exact first-success completion and the whole-view cutoff comparison. -/
namespace WalletUnbounded
open WalletGeneration WalletFinite TranscriptErasure
open WalletExperiments ProbabilityTools
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev View := WalletCapped.View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)
local notation "WalletAdversary" => Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)

abbrev Context := WalletTables × List Entropy

def prefixPrior (limit : Nat) : PMF (Context (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) :=
  (PMF.uniformOfFintype (WalletTables)).bind fun table =>
    (RandomTrialLists.law (Entropy := Entropy) limit).map (fun trials => (table,trials))

def choice (q : Passphrase) (target : Check)
    (context : Context (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) :=
  (execute context.1 (loop q target context.2)).1

def view (adversary : WalletAdversary)
    (context : Context (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))
    (chosen : Selected Entropy Seed Tail) : View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result) :=
  (chosen,execute context.1 (adversary chosen))

def real (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    PMF (View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)) :=
  (PMF.uniformOfFintype (WalletTables)).bind fun table =>
    (WalletCompletion.real table q target).map (fun chosen => (chosen,execute table (adversary chosen)))

/-- A fresh independent fallback has exactly the raw experiment's existing fallback law. -/
theorem actual_eq (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    (prefixPrior (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit).bind
      (fun context => (PMF.uniformOfFintype (Selected Entropy Seed Tail)).map
        (fun fallback => view adversary context ((choice q target context).getD fallback))) =
      WalletCapped.actual limit q target adversary := by
  unfold WalletCapped.actual
  rw [uniform_product, uniform_product]
  simp only [prefixPrior, RandomTrialLists.law, independentPair, PMF.bind_map, PMF.bind_bind,
    PMF.map_bind, PMF.map_comp, Function.comp_def, view, choice, WalletLaws.observe]

/-- Completion uses the same table, including on the exponentially rare empty-set branch. -/
theorem completed_eq (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    (prefixPrior (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit).bind
      (fun context => (WalletCompletion.real context.1 q target).map
        (fun fallback => view adversary context ((choice q target context).getD fallback))) = real q target adversary := by
  simp only [prefixPrior, PMF.bind_map, PMF.bind_bind, Function.comp_def, view, choice, real]
  congr 1
  funext table
  have pointwise (trials : List Entropy) :
      (WalletCompletion.real table q target).map
        (fun fallback => ((execute table (loop q target trials)).1.getD fallback,
          execute table (adversary ((execute table (loop q target trials)).1.getD fallback)))) =
      (match (execute table (loop q target trials)).1 with
        | none => WalletCompletion.real table q target
        | some chosen => PMF.pure chosen).map (fun chosen => (chosen,execute table (adversary chosen))) := by
    cases chosen : (execute table (loop q target trials)).1 with
    | none => rfl
    | some value =>
      simp only [Option.getD_some, PMF.pure_map]
      exact PMF.map_const _ _
  simp_rw [pointwise]
  rw [← PMF.map_bind]
  exact congrArg (fun distribution : PMF (Selected Entropy Seed Tail) =>
    distribution.map (fun chosen => (chosen,execute table (adversary chosen))))
    (WalletCompletion.completed_loop limit table q target)

/-- The cutoff cost is the actual source survival probability under the original table prior. -/
theorem abort_law (limit : Nat) (q : Passphrase) (target : Check) : (prefixPrior (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit).map
      (fun context => (choice q target context).isNone) =
    GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target limit := by
  have flag (table : WalletTables)
      (trials : List Entropy) : (execute table (loop q target trials)).1.isNone = FailureTests.allFail table q target trials := by
    apply Bool.eq_iff_iff.mpr
    simp only [Option.isNone_iff_eq_none, FailureTests.none_iff]
  simp only [prefixPrior, PMF.map_bind, PMF.map_comp, Function.comp_def, choice, flag, GenerationSurvival.game]
  have simpaTerm := PMF.bind_comm (PMF.uniformOfFintype (WalletTables)) (RandomTrialLists.law (Entropy := Entropy) limit) (fun table trials => PMF.pure (FailureTests.allFail table q target trials))
  (try simp only [PMF.map] at simpaTerm ⊢)
  exact simpaTerm

/-- The only possible change from exact first-success completion is a cutoff failure. -/
theorem close_to_capped (limit : Nat) (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    StatisticalClose.Close (real q target adversary) (WalletCapped.actual limit q target adversary)
      ((GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target limit) true) := by
  have bound := CompletionCoupling.bound
    (prefixPrior (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)
    (choice q target) (fun _ => PMF.uniformOfFintype (Selected Entropy Seed Tail))
    (fun context => WalletCompletion.real context.1 q target) (view adversary)
  rw [actual_eq, completed_eq, abort_law] at bound
  intro test
  exact ⟨(bound test).2,(bound test).1⟩

end WalletUnbounded

/-! Exact denominator relaxation and source constants for the W2 statistical bound. -/
namespace W2Arithmetic

theorem denominator (domain budget : Nat) (large : 2 ≤ domain) :
    (budget : ENNReal)/((domain-1 : Nat) : ENNReal) ≤ 2*(budget : ENNReal)/(domain : ENNReal) := by
  have npos : (domain : ENNReal) ≠ 0 := by exact_mod_cast (show domain ≠ 0 from by omega)
  have mpos : ((domain-1 : Nat) : ENNReal) ≠ 0 := by exact_mod_cast (show domain-1 ≠ 0 from by omega)
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) mpos) (ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp)) npos)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  have nreal : (2 : ℝ) ≤ domain := by exact_mod_cast large
  rw [Nat.cast_sub (show 1 ≤ domain from by omega), Nat.cast_one]
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < (domain : ℝ)-1) (by linarith : (0 : ℝ) < domain)).mpr
  have kreal : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  nlinarith

/-- The two cutoff contributions and the two hit terms fit the appendix's delta_gen exactly as stated. -/
theorem source (kS qT : Nat) (tau average : ENNReal) (tailBound : tau ≤ (1 : ENNReal)/2^256)
    (meanBound : average ≤ (2 : ENNReal)^17) :
    tau + (tau + ((kS : ENNReal)/(((2^256 : Nat)-1 : Nat) : ENNReal))*average +
      ((qT : ENNReal)/(((2^512 : Nat)-1 : Nat) : ENNReal))*average) ≤
      (2 : ENNReal)^18*((kS+1 : Nat) : ENNReal)/(2 : ENNReal)^256 +
        (2 : ENNReal)^18*(qT : ENNReal)/(2 : ENNReal)^512 := by
  have large256 : (2 : Nat) ≤ 2^256 := by decide
  have large512 : (2 : Nat) ≤ 2^512 := large256.trans (pow_le_pow_right₀ (by decide) (by decide : 256 ≤ 512))
  have eBound := mul_le_mul (denominator (2^256) kS large256) meanBound (zero_le) (zero_le)
  have dBound := mul_le_mul (denominator (2^512) qT large512) meanBound (zero_le) (zero_le)
  have combined := add_le_add tailBound (add_le_add (add_le_add tailBound eBound) dBound)
  calc
    _ ≤ (1 : ENNReal)/2^256 + ((1 : ENNReal)/2^256 +
        (2*(kS : ENNReal)/((2^256 : Nat) : ENNReal))*(2 : ENNReal)^17 +
        (2*(qT : ENNReal)/((2^512 : Nat) : ENNReal))*(2 : ENNReal)^17) := combined
    _ = ((2 : ENNReal) + (2 : ENNReal)^18*(kS : ENNReal))/(2 : ENNReal)^256 +
        (2 : ENNReal)^18*(qT : ENNReal)/(2 : ENNReal)^512 := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
      have power : (2 : ENNReal)*(2 : ENNReal)^17 = (2 : ENNReal)^18 := by rw [pow_succ]; exact mul_comm _ _
      rw [show (2 : ENNReal)*(kS : ENNReal)*((2 : ENNReal)^256)⁻¹*(2 : ENNReal)^17 =
        ((2 : ENNReal)*(2 : ENNReal)^17)*(kS : ENNReal)*((2 : ENNReal)^256)⁻¹ from by ac_rfl]
      rw [show (2 : ENNReal)*(qT : ENNReal)*((2 : ENNReal)^512)⁻¹*(2 : ENNReal)^17 =
        ((2 : ENNReal)*(2 : ENNReal)^17)*(qT : ENNReal)*((2 : ENNReal)^512)⁻¹ from by ac_rfl, power]
      simp only [add_mul, two_mul, one_mul]
      ac_rfl
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply ENNReal.div_le_div_right
      rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      have two : (2 : ENNReal) ≤ (2 : ENNReal)^18 := by norm_num
      exact (add_le_add two le_rfl).trans_eq (add_comm _ _)

end W2Arithmetic

/-! W2 generation bound: actual first-success generation versus the one-point planted experiment. -/
namespace W2
open WalletGeneration WalletFinite TranscriptErasure WalletExperiments
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

def delta (kS qT : Nat) : ENNReal :=
  (2 : ENNReal)^18*((kS+1 : Nat) : ENNReal)/(2 : ENNReal)^256 +
    (2 : ENNReal)^18*(qT : ENNReal)/(2 : ENNReal)^512

/-- Actual fixed-table rejection sampling is close in its entire selected-triple and adversary-view law. -/
theorem finite_generation_bound (q : Passphrase) (target : Check)
    (adversary : Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result))
    (entropyWidth : Fintype.card Entropy = 2^256) (seedWidth : Fintype.card Seed = 2^512)
    (checkWidth : Fintype.card Check = 2^16) (kS qT : Nat)
    (sBudget : ∀ chosen table, (WalletQuerySets.sSet q (execute table (adversary chosen)).2).card ≤ kS)
    (tBudget : ∀ chosen table, (WalletQuerySets.tSet (execute table (adversary chosen)).2).card ≤ qT) :
    StatisticalClose.Close (WalletUnbounded.real q target adversary)
      (WalletCapped.planted q target adversary) (delta kS qT) := by
  have largeE : 2 ≤ Fintype.card Entropy := by rw [entropyWidth]; decide
  have largeD : 2 ≤ Fintype.card Seed := by
    rw [seedWidth]
    exact (show (2 : Nat) ≤ 2^256 from by decide).trans (pow_le_pow_right₀ (by decide) (by decide : 256 ≤ 512))
  have source := WalletUnbounded.close_to_capped GenerationBounds.cutoff q target adversary
  have erased := WalletCapped.close GenerationBounds.cutoff q target adversary largeE largeD kS qT sBudget tBudget
  have combined := CloseComposition.trans _ _ _ _ _ source erased
  apply StatisticalClose.mono _ _ _ _ combined
  have tailBound := (GenerationBounds.cutoff_tail_enn (Entropy := Entropy) (Seed := Seed) (Tail := Tail)
    q target entropyWidth seedWidth checkWidth).le
  have meanBound := GenerationCount.source_mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail)
    q target entropyWidth seedWidth checkWidth
  simpa only [entropyWidth, seedWidth, delta] using W2Arithmetic.source kS qT _ _ tailBound meanBound

/-- Answer instrumentation is source-view complete and adds no query cost. -/
theorem full_answer_view (q : Passphrase) (target : Check)
    (adversary : Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result))
    (entropyWidth : Fintype.card Entropy = 2^256) (seedWidth : Fintype.card Seed = 2^512)
    (checkWidth : Fintype.card Check = 2^16) (kS qT : Nat)
    (sBudget : ∀ chosen table, (WalletQuerySets.sSet q (execute table (adversary chosen)).2).card ≤ kS)
    (tBudget : ∀ chosen table, (WalletQuerySets.tSet (execute table (adversary chosen)).2).card ≤ qT) :
    StatisticalClose.Close
      (WalletUnbounded.real q target (fun chosen => RetainedAnswers.retaining (adversary chosen)))
      (WalletCapped.planted q target (fun chosen => RetainedAnswers.retaining (adversary chosen))) (delta kS qT) := by
  apply finite_generation_bound q target _ entropyWidth seedWidth checkWidth kS qT
  · intro chosen table
    simpa only [RetainedAnswers.retaining_execution] using sBudget chosen table
  · intro chosen table
    simpa only [RetainedAnswers.retaining_execution] using tBudget chosen table

end W2

/-! W2 on a finite view derived from an arbitrary passphrase-domain adversary. -/
namespace W2Window
open WalletGeneration WalletFinite TranscriptErasure WalletWindow
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]
abbrev Adversary := Selected Entropy Seed Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result
abbrev View := Selected Entropy Seed Tail × (Option Result × List (Point Entropy Passphrase Seed))

def project (window : Finset Passphrase)
    (output : WalletCapped.View (Entropy := Entropy) (Passphrase := {q // q ∈ window}) (Seed := Seed) (Tail := Tail) (Result := Option Result)) :
    View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result) :=
  (output.1,(output.2.1,output.2.2.map (embed window)))

def actual (q : Passphrase) (target : Check)
    (adversary : Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)) :
    PMF (View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)) :=
  let window := passphrases q adversary
  let narrowQ : {q // q ∈ window} := ⟨q,real_member q adversary⟩
  (WalletUnbounded.real narrowQ target (fun chosen => narrow window (adversary chosen))).map (project window)

def planted (q : Passphrase) (target : Check)
    (adversary : Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)) :
    PMF (View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)) :=
  let window := passphrases q adversary
  let narrowQ : {q // q ∈ window} := ⟨q,real_member q adversary⟩
  (WalletCapped.planted narrowQ target (fun chosen => narrow window (adversary chosen))).map (project window)

/-- No Fintype or length bound on the ambient passphrase domain is required. -/
theorem generation_bound (q : Passphrase) (target : Check)
    (adversary : Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result))
    (entropyWidth : Fintype.card Entropy = 2^256) (seedWidth : Fintype.card Seed = 2^512)
    (checkWidth : Fintype.card Check = 2^16) (kS qT : Nat)
    (sBudget : ∀ chosen table, (WalletQuerySets.sSet q (execute table (adversary chosen)).2).card ≤ kS)
    (tBudget : ∀ chosen table, (WalletQuerySets.tSet (execute table (adversary chosen)).2).card ≤ qT) :
    StatisticalClose.Close (actual q target adversary) (planted q target adversary) (W2.delta kS qT) := by
  let window := passphrases q adversary
  let narrowQ : {q // q ∈ window} := ⟨q,real_member q adversary⟩
  have budget := WalletWindowBudgets.budgets q adversary kS qT sBudget tBudget
  have bound := W2.finite_generation_bound narrowQ target (fun chosen => narrow window (adversary chosen))
    entropyWidth seedWidth checkWidth kS qT budget.1 budget.2
  exact CloseComposition.map _ _ _ bound (project window)

end W2Window

/-! Source views and exact independence of the chosen sufficient finite passphrase window. -/
namespace WalletAt
open WalletGeneration WalletFinite TranscriptErasure WalletWindow
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]
abbrev Adversary := Selected Entropy Seed Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result
abbrev View := Selected Entropy Seed Tail × (Result × List (Point Entropy Passphrase Seed))
abbrev Tables (window : Finset Passphrase) := Table (Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)

def observe (window : Finset Passphrase)
    (adversary : Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result))
    (table : Tables (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)
    (chosen : Selected Entropy Seed Tail) : View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result) :=
  (chosen,execute (WalletWindowBudgets.extendTable window table) (adversary chosen))

def actual (window : Finset Passphrase) (q : {q // q ∈ window}) (target : Check)
    (adversary : Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)) :
    PMF (View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)) :=
  (PMF.uniformOfFintype (Tables (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)).bind
    (fun table => (WalletCompletion.real table q target).map (observe window adversary table))

def planted (window : Finset Passphrase) (q : {q // q ∈ window}) (target : Check)
    (adversary : Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)) :
    PMF (View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)) :=
  (PMF.uniformOfFintype (Selected Entropy Seed Tail)).bind fun chosen =>
    (PMF.uniformOfFintype (Tables (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)).map
      (fun table => observe window adversary (restore q target (some chosen) table) chosen)

end WalletAt

/-! Source-form W2 on arbitrary passphrases, with complete observable laws independent of finite view choice. -/
namespace W2Source
open WalletGeneration WalletFinite TranscriptErasure WalletWindow
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Adversary := WalletAt.Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)
abbrev View := WalletAt.View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)

def liftView (output : View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result)) :
    W2Window.View (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Tail := Tail) (Result := Result) :=
  (output.1,(some output.2.1,output.2.2))

local notation "WalletAdversary" => Adversary (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)

omit [DecidableEq Check] [Nonempty Entropy] [Nonempty Check] [Nonempty Tail] in
/-- The narrowing compiler adds only Some to the original result; it preserves all actual queries. -/
theorem observation (q : Passphrase)
    (adversary : WalletAdversary)
    (chosen : Selected Entropy Seed Tail)
    (table : WalletAt.Tables (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (passphrases q adversary)) :
    W2Window.project (passphrases q adversary)
      (chosen,execute table (narrow (passphrases q adversary) (adversary chosen))) =
    liftView (WalletAt.observe (passphrases q adversary) adversary table chosen) := by
  have faithful := adversary_faithful q adversary (WalletWindowBudgets.extendTable (passphrases q adversary) table) chosen
  dsimp only at faithful
  rw [WalletWindowBudgets.restrict_extend] at faithful
  exact congrArg (fun result => (chosen,result)) faithful

/-- The actual finite-cylinder definition equals the source view with the compiler's harmless Some wrapper. -/
theorem actual_eq (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    W2Window.actual q target adversary =
      (WalletAt.actual (passphrases q adversary) ⟨q,real_member q adversary⟩ target adversary).map liftView := by
  simp only [W2Window.actual, WalletUnbounded.real, WalletAt.actual,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext table
  congr 1
  funext chosen
  exact observation q adversary chosen table

omit [DecidableEq Check] in
/-- Programming does not alter compiler fidelity, since the source budget covers every table. -/
theorem planted_eq (q : Passphrase) (target : Check)
    (adversary : WalletAdversary) :
    W2Window.planted q target adversary =
      (WalletAt.planted (passphrases q adversary) ⟨q,real_member q adversary⟩ target adversary).map liftView := by
  simp only [W2Window.planted, WalletCapped.planted, WalletAt.planted,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext chosen
  congr 1
  funext table
  exact observation q adversary chosen _

/-- Full source W2: finite-cylinder ROM, arbitrary passphrase domain, exact appendix delta_gen. -/
theorem generation_bound (q : Passphrase) (target : Check)
    (adversary : WalletAdversary)
    (entropyWidth : Fintype.card Entropy = 2^256) (seedWidth : Fintype.card Seed = 2^512)
    (checkWidth : Fintype.card Check = 2^16) (kS qT : Nat)
    (sBudget : ∀ chosen table, (WalletQuerySets.sSet q (execute table (adversary chosen)).2).card ≤ kS)
    (tBudget : ∀ chosen table, (WalletQuerySets.tSet (execute table (adversary chosen)).2).card ≤ qT) :
    StatisticalClose.Close
      (WalletAt.actual (passphrases q adversary) ⟨q,real_member q adversary⟩ target adversary)
      (WalletAt.planted (passphrases q adversary) ⟨q,real_member q adversary⟩ target adversary)
      (W2.delta kS qT) := by
  have bound := W2Window.generation_bound q target adversary entropyWidth seedWidth checkWidth kS qT sBudget tBudget
  rw [actual_eq, planted_eq] at bound
  intro test
  have extended := bound (fun output => match output.2.1 with
    | none => false
    | some result => test (output.1,(result,output.2.2)))
  simpa only [PMF.map_comp, liftView, Function.comp_def] using extended

/-- Retain any independently sampled external environment, including P, Q and the other ideal functions. -/
theorem joint_generation_bound {Context : Type} (prior : PMF Context) (q : Context → Passphrase) (target : Check)
    (adversary : Context → WalletAdversary)
    (entropyWidth : Fintype.card Entropy = 2^256) (seedWidth : Fintype.card Seed = 2^512)
    (checkWidth : Fintype.card Check = 2^16) (kS qT : Nat)
    (sBudget : ∀ context chosen table, (WalletQuerySets.sSet (q context) (execute table (adversary context chosen)).2).card ≤ kS)
    (tBudget : ∀ context chosen table, (WalletQuerySets.tSet (execute table (adversary context chosen)).2).card ≤ qT) :
    StatisticalClose.Close
      (prior.bind (fun context => (WalletAt.actual (passphrases (q context) (adversary context))
        ⟨q context,real_member _ _⟩ target (adversary context)).map (fun output => (context,output))))
      (prior.bind (fun context => (WalletAt.planted (passphrases (q context) (adversary context))
        ⟨q context,real_member _ _⟩ target (adversary context)).map (fun output => (context,output))))
      (W2.delta kS qT) := by
  have averaged := CloseComposition.bind prior _ _ (fun _ => W2.delta kS qT)
    (fun context => CloseComposition.map _ _ _
      (generation_bound (q context) target (adversary context) entropyWidth seedWidth checkWidth kS qT
        (sBudget context) (tBudget context)) (fun output => (context,output)))
  simpa only [MomentTools.constant] using averaged

end W2Source

end
end MhfeLean
