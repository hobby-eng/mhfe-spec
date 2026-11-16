/- long: the rejection-sampling tail and trial-count estimates form one argument. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MhfeLean.Chapters.GenerationCoupling
import MhfeLean.Chapters.GenerationSampling
import MhfeLean.Chapters.Probability
import MhfeLean.Chapters.ShortSources

namespace MhfeLean
noncomputable section

/-! # Profile trial probabilities, stopping counts and tails
-/

/-! A new entropy and its two independent ideal-function answers have an exact uniform joint law. -/
namespace SeedCheckLaw
open ProbabilityTools
variable {Entropy Seed Check Tail : Type}
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]
  [DecidableEq Entropy] [DecidableEq Seed]

def eager : PMF (Entropy × Seed × (Check × Tail)) :=
  (PMF.uniformOfFintype Entropy).bind fun e =>
    (PMF.uniformOfFintype (Entropy → Seed)).bind fun s =>
      (PMF.uniformOfFintype (Seed → Check × Tail)).map fun t => (e, s e, t (s e))

omit [DecidableEq Entropy] in
/-- The same law holds when S reads any fixed encoding of the entropy. -/
theorem uniform_joint_at {Domain : Type} [Fintype Domain] [DecidableEq Domain]
    (input : Entropy → Domain) :
    ((PMF.uniformOfFintype Entropy).bind fun e =>
      (PMF.uniformOfFintype (Domain → Seed)).bind fun s =>
        (PMF.uniformOfFintype (Seed → Check × Tail)).map fun t => (e,s (input e),t (s (input e)))) =
      PMF.uniformOfFintype (Entropy × Seed × (Check × Tail)) := by
  letI : Nonempty Domain := Nonempty.map input (inferInstance : Nonempty Entropy)
  calc
    _ = (PMF.uniformOfFintype Entropy).bind fun e =>
        ((PMF.uniformOfFintype (Domain → Seed)).map (fun s => s (input e))).bind fun d =>
          ((PMF.uniformOfFintype (Seed → Check × Tail)).map (fun t => t d)).map (fun digest => (e,d,digest)) := by
      simp only [PMF.bind_map, PMF.map_comp, Function.comp_def]
    _ = (PMF.uniformOfFintype Entropy).bind fun e =>
        (PMF.uniformOfFintype Seed).bind fun d =>
          (PMF.uniformOfFintype (Check × Tail)).map (fun digest => (e,d,digest)) := by
      simp_rw [uniform_eval]
    _ = independentPair (PMF.uniformOfFintype Entropy)
        (independentPair (PMF.uniformOfFintype Seed) (PMF.uniformOfFintype (Check × Tail))) := by
      simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
    _ = _ := by rw [← uniform_product, ← uniform_product]

/-- Adaptively selecting T's input from S's output does not destroy independence of fresh tables. -/
theorem uniform_joint : eager (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) =
    PMF.uniformOfFintype (Entropy × Seed × (Check × Tail)) :=
  uniform_joint_at id

/-- A favorable new-point trial: neither lookup touches the cache and the check prefix passes. -/
def test (oldEntropy : Finset Entropy) (oldSeed : Finset Seed) (target : Check) :
    Entropy × Seed × (Check × Tail) → Bool := by
  classical
  exact fun value => decide (value.1 ∉ oldEntropy ∧ value.2.1 ∉ oldSeed ∧ value.2.2.1 = target)

theorem new_pass_probability (oldEntropy : Finset Entropy) (oldSeed : Finset Seed) (target : Check) :
    ((eager (Tail := Tail)).map (test oldEntropy oldSeed target)) true =
      (((Fintype.card Entropy - oldEntropy.card) * (Fintype.card Seed - oldSeed.card) * Fintype.card Tail : Nat) : ENNReal) /
      (((Fintype.card Entropy * Fintype.card Seed * Fintype.card Check * Fintype.card Tail : Nat) : ENNReal)) := by
  classical
  rw [uniform_joint]
  let matching := oldEntropyᶜ ×ˢ (oldSeedᶜ ×ˢ (({target} : Finset Check) ×ˢ (Finset.univ : Finset Tail)))
  have shape : test oldEntropy oldSeed target = fun value => decide (value ∈ matching) := by
    funext value
    simp only [test, matching, Finset.mem_product, Finset.mem_compl, Finset.mem_singleton, Finset.mem_univ,
      and_true]
  rw [shape, FreshSampling.uniform_hit_probability]
  simp only [matching, Finset.card_product, Finset.card_compl, Finset.card_singleton,
    Finset.card_univ, Nat.one_mul, Fintype.card_prod]
  congr 2 <;> ac_rfl

end SeedCheckLaw

/-! Factor the actual dependent wallet-table prior into independent S and T functions. -/
namespace WalletTableFactors
open WalletGeneration WalletFinite TranscriptErasure
open ProbabilityTools
variable {Entropy Passphrase Seed Check Tail : Type}

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)
abbrev PairTables := (Entropy × Passphrase → Seed) × (Seed → Check × Tail)

def split : Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) ≃
    PairTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) where
  toFun := fun table => (fun point => table (Point.s point.1 point.2), fun seed => table (Point.t seed))
  invFun := fun pair point => match point with | .s e q => pair.1 (e,q) | .t d => pair.2 d
  left_inv := by intro table; funext point; cases point <;> rfl
  right_inv := by intro pair; cases pair; rfl

noncomputable section
variable [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

omit [Nonempty Entropy] in
theorem sampling : PMF.uniformOfFintype (Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) =
    (PMF.uniformOfFintype (PairTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))).map split.symm := by
  exact (PMF.uniformOfFintype_map_of_bijective split.symm split.symm.bijective).symm

def nextFresh (q : Passphrase) : PMF (Entropy × Seed × (Check × Tail)) :=
  (PMF.uniformOfFintype Entropy).bind fun e =>
    (PMF.uniformOfFintype (Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))).map fun table =>
      let d : Seed := table (Point.s e q)
      (e,d,table (Point.t d))

/-- A new trial of the full wallet functions has the same fresh joint law. -/
theorem next_uniform (q : Passphrase) : nextFresh (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) q =
      PMF.uniformOfFintype (Entropy × Seed × (Check × Tail)) := by
  letI : Nonempty Passphrase := ⟨q⟩
  unfold nextFresh
  rw [sampling, uniform_product]
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
  exact SeedCheckLaw.uniform_joint_at (fun e : Entropy => (e,q))

end
end WalletTableFactors

/-! Retaining dependent answers gives an exact posterior fresh-table representation. -/
namespace RetainedAnswers
open TranscriptErasure
variable {Point Result : Type} {spec : OracleSpec Point}
abbrev Read (spec : OracleSpec Point) := Sigma spec.Range

variable (table : Table spec) (program : OracleComp spec Result)

def answers : List (Read spec) :=
  OracleComp.construct (fun _ => []) (fun point _ recurse => ⟨point,table point⟩ :: recurse (table point)) program

theorem answer_points : (answers table program).map Sigma.fst = (execute table program).2 := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih =>
    change point :: (answers table (next (table point))).map Sigma.fst =
      (execute table (ask point >>= next)).2
    rw [execute_bind, execute_ask]
    simp only [List.singleton_append]
    rw [ih]

theorem consistent : ∀ read ∈ answers table program, read.2 = table read.1 := by
  induction program using OracleComp.inductionOn with
  | pure result => intro read member; cases member
  | query_bind point next ih =>
    intro read member
    change read ∈ ⟨point,table point⟩ :: answers table (next (table point)) at member
    rcases List.mem_cons.mp member with same | later
    · subst read
      rfl
    · exact ih (table point) read later

/-- Instrumentation returns dependent answers privately without adding any oracle queries. -/
def retaining (program : OracleComp spec Result) : OracleComp spec (Result × List (Read spec)) :=
  OracleComp.construct (fun result => pure (result, []))
    (fun point _ recurse => do
      let value ← ask point
      let rest ← recurse value
      pure (rest.1, ⟨point,value⟩ :: rest.2)) program

theorem retaining_execution :
    execute table (retaining program) = (((execute table program).1, answers table program), (execute table program).2) := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih =>
    change execute table (ask point >>= fun value => retaining (next value) >>= fun rest => pure (rest.1, ⟨point,value⟩ :: rest.2)) =
      (((execute table (ask point >>= next)).1, ⟨point,table point⟩ :: answers table (next (table point))),
        (execute table (ask point >>= next)).2)
    rw [execute_bind, execute_ask]
    dsimp only
    rw [execute_bind]
    dsimp only
    rw [ih]
    dsimp only
    rw [execute_pure]
    simp only [execute_bind, execute_ask, List.append_nil, List.singleton_append]

variable [DecidableEq Point]

def rebuild : List (Read spec) → Table spec → Table spec
  | [], fresh => fresh
  | read :: rest, fresh => Function.update (rebuild rest fresh) read.1 read.2

theorem rebuild_value (reads : List (Read spec)) (original fresh : Table spec)
    (valid : ∀ read ∈ reads, read.2 = original read.1) (point : Point) :
    rebuild reads fresh point = if point ∈ reads.map Sigma.fst then original point else fresh point := by
  induction reads with
  | nil => simp only [rebuild, List.map_nil, List.not_mem_nil, if_false]
  | cons read rest ih =>
    by_cases same : point = read.1
    · subst point
      simp only [rebuild, Function.update_self, List.map_cons, List.mem_cons, true_or, if_true]
      exact valid read List.mem_cons_self
    · rw [rebuild, Function.update_of_ne same]
      rw [ih (fun read member => valid read (List.mem_cons_of_mem _ member))]
      simp only [List.map_cons, List.mem_cons, same, false_or]

omit [DecidableEq Point] in
theorem answers_agree (program : OracleComp spec Result) (first second : Table spec)
    (agree : ∀ point ∈ (execute first program).2, second point = first point) :
    answers second program = answers first program := by
  induction program using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind point next ih =>
    change (∀ q ∈ (execute first (ask point >>= next)).2, second q = first q) at agree
    simp only [execute_bind, execute_ask, List.singleton_append] at agree
    have head := agree point List.mem_cons_self
    have rest := fun q member => agree q (List.mem_cons_of_mem point member)
    change ⟨point, second point⟩ :: answers second (next (second point)) =
      ⟨point, first point⟩ :: answers first (next (first point))
    rw [head, ih (first point) rest]

/-- Original tables are reconstructed from retained answers and an independent fresh remainder. -/
theorem reconstruction (program : OracleComp spec Result) (seed : Table spec × Table spec) :
    rebuild (answers (exchanged program seed).1 program) (exchanged program seed).2 = seed.1 := by
  have agree : ∀ point ∈ (execute seed.1 program).2, (exchanged program seed).1 point = seed.1 point := by
    intro point member
    simp only [exchanged, member, if_true]
  rw [answers_agree program seed.1 (exchanged program seed).1 agree]
  funext point
  rw [rebuild_value _ seed.1 _ (consistent seed.1 program), answer_points]
  by_cases member : point ∈ (execute seed.1 program).2
  · simp only [member, if_true]
  · simp only [member, if_false, exchanged]

noncomputable section
variable [Fintype Point] [∀ point, Fintype (spec point)] [∀ point, Nonempty (spec point)]

/-- The exact eager-table posterior, including the actual transcript and all its answers. -/
theorem posterior (program : OracleComp spec Result) :
    (PMF.uniformOfFintype (Table spec × Table spec)).map
      (fun seed => ((execute seed.1 program, answers seed.1 program), seed.1)) =
    (PMF.uniformOfFintype (Table spec × Table spec)).map
      (fun seed => ((execute seed.1 program, answers seed.1 program), rebuild (answers seed.1 program) seed.2)) := by
  have preserved := PMF.uniformOfFintype_map_of_bijective
    (exchangeEquiv program) (exchangeEquiv program).bijective
  calc
    _ = (PMF.uniformOfFintype (Table spec × Table spec)).map
        ((fun seed => ((execute seed.1 program, answers seed.1 program), rebuild (answers seed.1 program) seed.2)) ∘ exchangeEquiv program) := by
      congr 1
      funext seed
      have agree : ∀ point ∈ (execute seed.1 program).2, (exchanged program seed).1 point = seed.1 point := by
        intro point member
        simp only [exchanged, member, if_true]
      change _ = ((execute (exchanged program seed).1 program, answers (exchanged program seed).1 program),
        rebuild (answers (exchanged program seed).1 program) (exchanged program seed).2)
      rw [reconstruction, stable, answers_agree program seed.1 (exchanged program seed).1 agree]
    _ = ((PMF.uniformOfFintype (Table spec × Table spec)).map (exchangeEquiv program)).map
        (fun seed => ((execute seed.1 program, answers seed.1 program), rebuild (answers seed.1 program) seed.2)) :=
      (PMF.map_comp _ _ _).symm
    _ = _ := by rw [preserved]

/-- Any later probabilistic continuation may use the retained history and the rebuilt table. -/
theorem posterior_bind {Output : Type} (program : OracleComp spec Result)
    (continuation : ((Result × List Point) × List (Read spec)) → Table spec → PMF Output) :
    (PMF.uniformOfFintype (Table spec)).bind (fun table =>
      continuation (execute table program, answers table program) table) =
    (PMF.uniformOfFintype (Table spec)).bind (fun table =>
      (PMF.uniformOfFintype (Table spec)).bind (fun fresh =>
        continuation (execute table program, answers table program) (rebuild (answers table program) fresh))) := by
  have transported := congrArg (fun distribution => distribution.bind
    (fun observation => continuation observation.1 observation.2)) (posterior program)
  have pairLaw : PMF.uniformOfFintype (Table spec × Table spec) =
      ProbabilityTools.independentPair (PMF.uniformOfFintype (Table spec)) (PMF.uniformOfFintype (Table spec)) :=
    ProbabilityTools.uniform_product
  simpa only [pairLaw, ProbabilityTools.independentPair, PMF.bind_map, PMF.bind_bind,
    PMF.bind_const, Function.comp_def] using transported

end
end RetainedAnswers

/-! Read all trial prefixes to expose a finite history for the next-trial contraction. -/
namespace GenerationHistory
open WalletGeneration TranscriptErasure
variable {Entropy Passphrase Seed Check Tail : Type}

structure Trial (Entropy Seed Check Tail : Type) where
  entropy : Entropy
  seed : Seed
  digest : Check × Tail

def scan (q : Passphrase) : List Entropy → OracleComp (spec Entropy Passphrase Seed Check Tail)
    (List (Trial Entropy Seed Check Tail))
  | [] => pure []
  | e :: trials => do
    let d : Seed ← ask (spec := spec Entropy Passphrase Seed Check Tail) (Point.s e q)
    let digest : Check × Tail ← ask (spec := spec Entropy Passphrase Seed Check Tail) (Point.t d)
    let rest ← scan q trials
    pure (⟨e,d,digest⟩ :: rest)

variable (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)

theorem scan_cons
    (e : Entropy) (trials : List Entropy) :
    execute table (scan q (e :: trials)) =
      let d : Seed := table (Point.s e q)
      let digest : Check × Tail := table (Point.t d)
      (⟨e,d,digest⟩ :: (execute table (scan q trials)).1,
        ([Point.s e q, Point.t d] : List (Point Entropy Passphrase Seed)) ++ (execute table (scan q trials)).2) := by
  conv_lhs => unfold scan
  rw [execute_bind, execute_ask]
  dsimp only
  rw [execute_bind, execute_ask]
  dsimp only
  rw [execute_bind]
  dsimp only
  rw [execute_pure]
  simp only [List.append_nil, List.singleton_append]
  rfl

theorem length (trials : List Entropy) : (execute table (scan q trials)).1.length = trials.length := by
  induction trials with
  | nil => rfl
  | cons e trials ih => rw [scan_cons]; simp only [List.length_cons, ih]

def recordedLog (q : Passphrase) (record : Trial Entropy Seed Check Tail) :
    List (Point Entropy Passphrase Seed) :=
  [Point.s record.entropy q, Point.t record.seed]

theorem trace (trials : List Entropy) :
    (execute table (scan q trials)).2 = (execute table (scan q trials)).1.flatMap (recordedLog q) := by
  induction trials with
  | nil => rfl
  | cons e trials ih => rw [scan_cons]; simp only [List.flatMap_cons, recordedLog, ih]

variable [DecidableEq Entropy] [DecidableEq Seed]

def entropyCache (records : List (Trial Entropy Seed Check Tail)) : Finset Entropy := (records.map Trial.entropy).toFinset
def seedCache (records : List (Trial Entropy Seed Check Tail)) : Finset Seed := (records.map Trial.seed).toFinset

omit [DecidableEq Seed] in
theorem cache_entropy_count (table : Table (spec Entropy Passphrase Seed Check Tail))
    (q : Passphrase) (trials : List Entropy) :
    (entropyCache (execute table (scan q trials)).1).card ≤ trials.length := by
  calc
    _ ≤ _ := List.toFinset_card_le _
    _ = _ := by rw [List.length_map, length]

omit [DecidableEq Entropy] in
theorem cache_seed_count (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (trials : List Entropy) : (seedCache (execute table (scan q trials)).1).card ≤ trials.length := by
  calc
    _ ≤ _ := List.toFinset_card_le _
    _ = _ := by rw [List.length_map, length]

omit [DecidableEq Seed] in
theorem entropy_unread (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (trials : List Entropy) (candidate : Entropy)
    (new : candidate ∉ entropyCache (execute table (scan q trials)).1) :
    Point.s candidate q ∉ (execute table (scan q trials)).2 := by
  rw [trace]
  intro member
  obtain ⟨record, inRecords, inLog⟩ := List.mem_flatMap.mp member
  change Point.s candidate q ∈ [Point.s record.entropy q, Point.t record.seed] at inLog
  rcases List.mem_cons.mp inLog with same | tail
  · apply new
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨record, inRecords, (Point.s.inj same).1.symm⟩
  · have impossible := List.mem_singleton.mp tail
    cases impossible

omit [DecidableEq Entropy] in
theorem seed_unread (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (trials : List Entropy) (candidate : Seed)
    (new : candidate ∉ seedCache (execute table (scan q trials)).1) :
    Point.t candidate ∉ (execute table (scan q trials)).2 := by
  rw [trace]
  intro member
  obtain ⟨record, inRecords, inLog⟩ := List.mem_flatMap.mp member
  change Point.t candidate ∈ [Point.s record.entropy q, Point.t record.seed] at inLog
  rcases List.mem_cons.mp inLog with impossible | tail
  · cases impossible
  · have same := List.mem_singleton.mp tail
    apply new
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨record, inRecords, (Point.t.inj same).symm⟩

end GenerationHistory

/-! Relate private scanned histories to actual rejection-loop failure and new-point lookups. -/
namespace HistoryNoPass
open WalletGeneration TranscriptErasure GenerationHistory
variable {Entropy Passphrase Seed Check Tail : Type}

/-- Reading all n trials agrees with the stopping loop on the event that none passes. -/
theorem none_iff [DecidableEq Check] (table : Table (spec Entropy Passphrase Seed Check Tail))
    (q : Passphrase) (target : Check) (trials : List Entropy) :
    (execute table (loop q target trials)).1 = none ↔
      ∀ record ∈ (execute table (scan q trials)).1, record.digest.1 ≠ target := by
  induction trials with
  | nil => simp only [loop, scan, execute_pure, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons e trials ih =>
    rw [execution_cons, scan_cons]
    dsimp only
    by_cases passing : (table (Point.t (table (Point.s e q)))).1 = target
    · rw [if_pos passing]
      constructor
      · intro impossible
        cases impossible
      · intro all
        exact False.elim (all _ List.mem_cons_self passing)
    · rw [if_neg passing]
      constructor
      · intro none
        have previous := ih.mp none
        intro record member
        rcases List.mem_cons.mp member with same | later
        · subst record
          exact passing
        · exact previous record later
      · intro all
        apply ih.mpr
        intro record member
        exact all record (List.mem_cons_of_mem _ member)

variable [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

/-- Rebuilding a real history leaves a new entropy lookup equal to its independent fresh-table value. -/
theorem fresh_entropy (table fresh : Table (spec Entropy Passphrase Seed Check Tail))
    (q : Passphrase) (trials : List Entropy) (e : Entropy)
    (new : e ∉ entropyCache (execute table (scan q trials)).1) :
    RetainedAnswers.rebuild (RetainedAnswers.answers table (scan q trials)) fresh (Point.s e q) =
      fresh (Point.s e q) := by
  rw [RetainedAnswers.rebuild_value _ table _ (RetainedAnswers.consistent table (scan q trials)),
    RetainedAnswers.answer_points, if_neg (entropy_unread table q trials e new)]

/-- Rebuilding a real history leaves a new seed lookup equal to its independent fresh-table value. -/
theorem fresh_seed (table fresh : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (trials : List Entropy) (d : Seed) (new : d ∉ seedCache (execute table (scan q trials)).1) :
    RetainedAnswers.rebuild (RetainedAnswers.answers table (scan q trials)) fresh (Point.t d) =
      fresh (Point.t d) := by
  rw [RetainedAnswers.rebuild_value _ table _ (RetainedAnswers.consistent table (scan q trials)),
    RetainedAnswers.answer_points, if_neg (seed_unread table q trials d new)]

end HistoryNoPass

/-! Exact new-point probability lower bounds before any finite-cutoff approximation. -/
namespace NewTrialBound

/-- Losing at most one quarter of each input space leaves at least one half of their product. -/
theorem half_product (n m a b : Nat) (left : 4*a ≤ n) (right : 4*b ≤ m) : n*m ≤ 2*(n-a)*(m-b) := by
  have l : 3*n ≤ 4*(n-a) := by omega
  have r : 3*m ≤ 4*(m-b) := by omega
  have product := Nat.mul_le_mul l r
  nlinarith

theorem division_mul (numerator denominator multiplier : ENNReal) :
    (numerator / denominator) * multiplier = (numerator * multiplier) / denominator := by
  simp only [div_eq_mul_inv]
  ac_rfl

noncomputable section
variable {Entropy Seed Check Tail : Type}
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]
  [DecidableEq Entropy] [DecidableEq Seed]

/-- A cache occupying at most one quarter of each space gives the contraction used in W2. -/
theorem probability (oldEntropy : Finset Entropy) (oldSeed : Finset Seed) (target : Check)
    (entropyBound : 4 * oldEntropy.card ≤ Fintype.card Entropy)
    (seedBound : 4 * oldSeed.card ≤ Fintype.card Seed) :
    1 / ((2 * Fintype.card Check : Nat) : ENNReal) ≤
      ((SeedCheckLaw.eager (Tail := Tail)).map
        (SeedCheckLaw.test oldEntropy oldSeed target)) true := by
  rw [SeedCheckLaw.new_pass_probability]
  have leftNonzero : ((2 * Fintype.card Check : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast (show 2 * Fintype.card Check ≠ 0 from Nat.mul_ne_zero (by decide) Fintype.card_ne_zero)
  have leftFinite : ((2 * Fintype.card Check : Nat) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have denominatorNonzero : ((Fintype.card Entropy * Fintype.card Seed * Fintype.card Check * Fintype.card Tail : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast (show Fintype.card Entropy * Fintype.card Seed * Fintype.card Check * Fintype.card Tail ≠ 0 by positivity)
  have denominatorFinite : ((Fintype.card Entropy * Fintype.card Seed * Fintype.card Check * Fintype.card Tail : Nat) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  apply (ENNReal.div_le_iff leftNonzero leftFinite).mpr
  rw [division_mul]
  apply (ENNReal.le_div_iff_mul_le (Or.inl denominatorNonzero) (Or.inl denominatorFinite)).mpr
  simp only [one_mul]
  have product := Nat.mul_le_mul_right (Fintype.card Check * Fintype.card Tail)
    (half_product _ _ _ _ entropyBound seedBound)
  norm_cast
  simpa only [mul_assoc, mul_left_comm, mul_comm] using product

end
end NewTrialBound

/-! A concrete next trial after rebuilding a real history has the required pass probability. -/
namespace CachedTrial
open WalletGeneration WalletFinite TranscriptErasure
open GenerationHistory GameExpectation MomentTools
open ProbabilityTools
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

def prior : PMF (Entropy × WalletTables) :=
  independentPair (PMF.uniformOfFintype Entropy)
    (PMF.uniformOfFintype (WalletTables))

def readTrial (q : Passphrase) (input : Entropy × WalletTables) :
    Entropy × Seed × (Check × Tail) :=
  let d : Seed := input.2 (Point.s input.1 q)
  (input.1,d,input.2 (Point.t d))

def good (history : WalletTables)
    (q : Passphrase) (target : Check) (trials : List Entropy) :
    Entropy × WalletTables → Bool :=
  fun input => SeedCheckLaw.test (entropyCache (execute history (scan q trials)).1)
    (seedCache (execute history (scan q trials)).1) target (readTrial q input)

def pass (history : WalletTables)
    (q : Passphrase) (target : Check) (trials : List Entropy) :
    Entropy × WalletTables → Bool :=
  fun input =>
    let rebuilt := RetainedAnswers.rebuild (RetainedAnswers.answers history (scan q trials)) input.2
    let d : Seed := rebuilt (Point.s input.1 q)
    decide ((rebuilt (Point.t d)).1 = target)

omit [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
theorem good_implies (history : WalletTables)
    (q : Passphrase) (target : Check) (trials : List Entropy)
    (input : Entropy × WalletTables)
    (favorable : good history q target trials input = true) : pass history q target trials input = true := by
  have details : input.1 ∉ entropyCache (execute history (scan q trials)).1 ∧
      input.2 (Point.s input.1 q) ∉ seedCache (execute history (scan q trials)).1 ∧
      (input.2 (Point.t (input.2 (Point.s input.1 q)))).1 = target := by
    have law := favorable
    simp only [good, SeedCheckLaw.test, readTrial] at law
    exact of_decide_eq_true (inst := _) law
  unfold pass
  apply decide_eq_true
  try dsimp only
  rw [HistoryNoPass.fresh_entropy history input.2 q trials input.1 details.1]
  rw [HistoryNoPass.fresh_seed history input.2 q trials _ details.2.1]
  exact details.2.2

omit [DecidableEq Check] in
theorem read_law (q : Passphrase) : (prior (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail)).map (readTrial q) =
      PMF.uniformOfFintype (Entropy × Seed × (Check × Tail)) := by
  have shape : (prior (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail)).map (readTrial q) =
      WalletTableFactors.nextFresh q := by
    simp only [prior, independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def, readTrial,
      WalletTableFactors.nextFresh]
  rw [shape]
  exact WalletTableFactors.next_uniform q

private theorem event_mono {Domain : Type} (distribution : PMF Domain)
    (first second : Domain → Bool) (implies : ∀ input, first input = true → second input = true) :
    (distribution.map first) true ≤ (distribution.map second) true := by
  rw [MomentTools.probability, MomentTools.probability]
  apply MomentTools.mono
  intro input
  by_cases active : first input = true
  · simp only [active, implies input active, if_true, le_refl]
  · simp only [Bool.eq_false_iff.mpr active, Bool.false_eq_true, if_false, zero_le]

theorem pass_probability (history : WalletTables)
    (q : Passphrase) (target : Check) (trials : List Entropy)
    (entropyBound : 4 * (entropyCache (execute history (scan q trials)).1).card ≤ Fintype.card Entropy)
    (seedBound : 4 * (seedCache (execute history (scan q trials)).1).card ≤ Fintype.card Seed) :
    1 / ((2 * Fintype.card Check : Nat) : ENNReal) ≤
      ((prior (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail)).map (pass history q target trials)) true := by
  calc
    _ ≤ ((prior (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail)).map (good history q target trials)) true := by
      have shape : (prior (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail)).map (good history q target trials) =
          ((prior (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail)).map (readTrial q)).map
            (SeedCheckLaw.test (entropyCache (execute history (scan q trials)).1)
              (seedCache (execute history (scan q trials)).1) target) := by
        rw [PMF.map_comp]
        rfl
      rw [shape, read_law, ← SeedCheckLaw.uniform_joint]
      exact NewTrialBound.probability _ _ target entropyBound seedBound
    _ ≤ _ := event_mono _ _ _ (good_implies history q target trials)

end CachedTrial

/-! The genuine eager-table prefix experiment satisfies a relative next-pass bound. -/
namespace ConditionalTrial
open WalletGeneration WalletFinite TranscriptErasure
open GenerationHistory GameExpectation MomentTools
open ProbabilityTools
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)

def failed (target : Check) (records : List (Trial Entropy Seed Check Tail)) : Bool :=
  records.all fun record => decide (record.digest.1 ≠ target)

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

def passed (q : Passphrase) (target : Check)
    (table : WalletTables) (e : Entropy) : Bool :=
  let d : Seed := table (Point.s e q)
  decide ((table (Point.t d)).1 = target)

def progress (q : Passphrase) (target : Check) (trials : List Entropy) : PMF Bool :=
  (PMF.uniformOfFintype (WalletTables)).bind fun table =>
    (PMF.uniformOfFintype Entropy).map fun e => failed target (execute table (scan q trials)).1 && passed q target table e

def afterFixed (q : Passphrase) (target : Check) (trials : List Entropy)
    (history : WalletTables) : PMF Bool :=
  (PMF.uniformOfFintype (WalletTables)).bind fun fresh =>
    (PMF.uniformOfFintype Entropy).map fun e => failed target (execute history (scan q trials)).1 &&
      passed q target (RetainedAnswers.rebuild (RetainedAnswers.answers history (scan q trials)) fresh) e

/-- The entire previous-history event is retained under the exact table posterior. -/
theorem posterior_progress (q : Passphrase) (target : Check) (trials : List Entropy) :
    progress (Seed := Seed) (Tail := Tail) q target trials =
      (PMF.uniformOfFintype (WalletTables)).bind
        (afterFixed q target trials) := by
  exact RetainedAnswers.posterior_bind (scan q trials) (fun history table =>
    (PMF.uniformOfFintype Entropy).map fun e => failed target history.1.1 && passed q target table e)

/-- Conditional on any real history, the next favorable fresh draw supplies the relative bound. -/
theorem fixed_lower (q : Passphrase) (target : Check) (trials : List Entropy)
    (history : WalletTables)
    (entropyBound : 4 * trials.length ≤ Fintype.card Entropy)
    (seedBound : 4 * trials.length ≤ Fintype.card Seed) :
    (if failed target (execute history (scan q trials)).1 then 1 / ((2*Fintype.card Check : Nat) : ENNReal) else 0) ≤
      (afterFixed q target trials history) true := by
  by_cases active : failed target (execute history (scan q trials)).1 = true
  · rw [if_pos active]
    have shape : afterFixed q target trials history =
        ((CachedTrial.prior (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail)).map
          (CachedTrial.pass history q target trials)) := by
      unfold afterFixed
      simp only [active, Bool.true_and]
      simp only [CachedTrial.prior, independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
      exact PMF.bind_comm _ _ _
    rw [shape]
    exact CachedTrial.pass_probability history q target trials
      ((Nat.mul_le_mul_left 4 (cache_entropy_count history q trials)).trans entropyBound)
      ((Nat.mul_le_mul_left 4 (cache_seed_count history q trials)).trans seedBound)
  · rw [if_neg active]
    exact zero_le

/-- No division by the probability of the history event is used. -/
theorem progress_lower (q : Passphrase) (target : Check) (trials : List Entropy)
    (entropyBound : 4 * trials.length ≤ Fintype.card Entropy)
    (seedBound : 4 * trials.length ≤ Fintype.card Seed) :
    (1 / ((2*Fintype.card Check : Nat) : ENNReal)) *
      (((PMF.uniformOfFintype (WalletTables)).map
        (fun table => failed target (execute table (scan q trials)).1)) true) ≤
      (progress (Seed := Seed) (Tail := Tail) q target trials) true := by
  calc
    _ = moment (PMF.uniformOfFintype (WalletTables))
        (fun table => if failed target (execute table (scan q trials)).1 then 1/((2*Fintype.card Check : Nat) : ENNReal) else 0) := by
      rw [probability]
      have scaled := mul_const
        (PMF.uniformOfFintype (WalletTables))
        (fun table => if failed target (execute table (scan q trials)).1 then (1 : ENNReal) else 0)
        (1/((2*Fintype.card Check : Nat) : ENNReal))
      have indicator : (fun table : WalletTables =>
          (if failed target (execute table (scan q trials)).1 then (1 : ENNReal) else 0) *
            (1/((2*Fintype.card Check : Nat) : ENNReal))) =
          (fun table => if failed target (execute table (scan q trials)).1 then 1/((2*Fintype.card Check : Nat) : ENNReal) else 0) := by
        funext table
        split_ifs <;> simp only [one_mul, zero_mul]
      rw [indicator] at scaled
      exact (mul_comm _ _).trans scaled.symm
    _ ≤ moment (PMF.uniformOfFintype (WalletTables))
        (fun history => (afterFixed q target trials history) true) :=
      MomentTools.mono _ _ _ (fun history => fixed_lower q target trials history entropyBound seedBound)
    _ = _ := by
      rw [posterior_progress, PMF.bind_apply]
      rfl

end ConditionalTrial

/-! A fixed-table first-success test is exactly the all-failed predicate on its trial prefix. -/
namespace FailureTests
open WalletGeneration TranscriptErasure GenerationHistory
variable {Entropy Passphrase Seed Check Tail : Type}

def record (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase) (e : Entropy) :
    Trial Entropy Seed Check Tail :=
  let d : Seed := table (Point.s e q)
  ⟨e,d,table (Point.t d)⟩

theorem records_map (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (trials : List Entropy) : (execute table (scan q trials)).1 = trials.map (record table q) := by
  induction trials with
  | nil => rfl
  | cons e trials ih => rw [scan_cons, List.map_cons, ih]; rfl

variable [DecidableEq Check]

variable (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase) (target : Check)
  (trials : List Entropy)

def allFail : Bool :=
  trials.all fun e => !(ConditionalTrial.passed q target table e)

theorem failed_eq :
    ConditionalTrial.failed target (execute table (scan q trials)).1 = allFail table q target trials := by
  rw [records_map]
  simp only [ConditionalTrial.failed, List.all_map, Function.comp_def, record,
    allFail, ConditionalTrial.passed, decide_not]
  rfl

theorem none_iff :
    (execute table (loop q target trials)).1 = none ↔ allFail table q target trials = true := by
  rw [HistoryNoPass.none_iff, ← failed_eq, ConditionalTrial.failed, List.all_eq_true]
  simp only [decide_eq_true_eq]

theorem append_last (e : Entropy) :
    allFail table q target (trials ++ [e]) =
      (allFail table q target trials && !(ConditionalTrial.passed q target table e)) := by
  simp only [allFail, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

end FailureTests

/-! Exact partition of a surviving prefix into next-pass and next-failure events. -/
namespace BoolPartition
open GameExpectation MomentTools

theorem partition (distribution : PMF (Bool × Bool)) :
    ((distribution.map (fun value => value.1 && value.2)) true) +
      ((distribution.map (fun value => value.1 && !value.2)) true) =
      ((distribution.map Prod.fst) true) := by
  rw [probability, probability, probability, ← MomentTools.add]
  congr 1
  funext value
  rcases value with ⟨first,second⟩
  cases first <;> cases second <;> norm_num

/-- Finite probabilities allow ordinary real subtraction without losing a small event. -/
theorem contraction (distribution : PMF (Bool × Bool)) (passRate : ℝ)
    (progress : passRate * ((distribution.map Prod.fst) true).toReal ≤ ((distribution.map (fun value => value.1 && value.2)) true).toReal) :
    ((distribution.map (fun value => value.1 && !value.2)) true).toReal ≤
      (1-passRate) * ((distribution.map Prod.fst) true).toReal := by
  have total := congrArg ENNReal.toReal (partition distribution)
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] at total
  nlinarith

end BoolPartition

/-! Pair the prefix-failure flag with the next actual check under the original table prior. -/
namespace TrialPairs
open WalletGeneration WalletFinite TranscriptErasure
open FailureTests GameExpectation MomentTools
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]
abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)

def fixed (q : Passphrase) (target : Check) (trials : List Entropy) : PMF (Bool × Bool) :=
  (PMF.uniformOfFintype (Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
    (PMF.uniformOfFintype Entropy).map fun e => (allFail table q target trials, ConditionalTrial.passed q target table e)

theorem left_law (q : Passphrase) (target : Check) (trials : List Entropy) : (fixed (Seed := Seed) (Tail := Tail) q target trials).map Prod.fst =
      (PMF.uniformOfFintype (Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))).map
        (fun table => allFail table q target trials) := by
  unfold fixed
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  have drop (table : Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) :
      (PMF.uniformOfFintype Entropy).map (fun _ => allFail table q target trials) = PMF.pure (allFail table q target trials) :=
    PMF.map_const (PMF.uniformOfFintype Entropy) (allFail table q target trials)
  simp_rw [drop]
  rfl

theorem pass_law (q : Passphrase) (target : Check) (trials : List Entropy) : (fixed (Seed := Seed) (Tail := Tail) q target trials).map (fun value => value.1 && value.2) =
      ConditionalTrial.progress (Seed := Seed) (Tail := Tail) q target trials := by
  unfold fixed ConditionalTrial.progress
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, failed_eq]

theorem fixed_lower (q : Passphrase) (target : Check) (trials : List Entropy)
    (entropyBound : 4 * trials.length ≤ Fintype.card Entropy)
    (seedBound : 4 * trials.length ≤ Fintype.card Seed) :
    (1 / ((2*Fintype.card Check : Nat) : ENNReal)) *
      (((fixed (Seed := Seed) (Tail := Tail) q target trials).map Prod.fst) true) ≤
      (((fixed (Seed := Seed) (Tail := Tail) q target trials).map (fun value => value.1 && value.2)) true) := by
  rw [left_law, pass_law]
  simpa only [failed_eq] using ConditionalTrial.progress_lower q target trials entropyBound seedBound

end TrialPairs

/-! Explicit finite survival estimates used for W2's bounded sequential generation. -/
namespace GeometricSurvival

/-- The finite-cutoff form needs contraction only before the cutoff. -/
theorem tail_bound_until (survival : Nat → ℝ) (ratio : ℝ) (limit : Nat) (nonnegative : 0 ≤ ratio)
    (start : survival 0 = 1) (step : ∀ n, n < limit → survival (n+1) ≤ ratio * survival n) :
    ∀ n, n ≤ limit → survival n ≤ ratio ^ n := by
  intro n
  induction n with
  | zero => intro _; simp only [start, pow_zero, le_refl]
  | succ n ih =>
    intro within
    calc
      _ ≤ ratio * survival n := step n (by omega)
      _ ≤ ratio * ratio ^ n := mul_le_mul_of_nonneg_left (ih (by omega)) nonnegative
      _ = _ := (pow_succ' ratio n).symm

theorem expected_bound_until (survival : Nat → ℝ) (ratio : ℝ) (limit : Nat)
    (nonnegative : ∀ n, n ≤ limit → 0 ≤ survival n) (ratio_lt : ratio < 1) (start : survival 0 = 1)
    (step : ∀ n, n < limit → survival (n+1) ≤ ratio * survival n) :
    (∑ n ∈ Finset.range limit, survival n) ≤ 1 / (1-ratio) := by
  have telescopes : ∀ n, n ≤ limit →
      (1-ratio) * (∑ i ∈ Finset.range n, survival i) ≤ 1-survival n := by
    intro n
    induction n with
    | zero => intro _; simp only [Finset.range_zero, Finset.sum_empty, mul_zero, start, sub_self, le_refl]
    | succ n ih =>
      intro within
      rw [Finset.sum_range_succ]
      have previous := ih (by omega)
      have next := step n (by omega)
      nlinarith
  apply (le_div_iff₀ (sub_pos.mpr ratio_lt)).mpr
  have bound := telescopes limit le_rfl
  have last := nonnegative limit le_rfl
  nlinarith

/-- Bernoulli bounds a block of at least 1/p trials by one half. -/
theorem block_bound (probability : ℝ) (count : Nat) (positive : 0 ≤ probability)
    (atMostOne : probability ≤ 1) (enough : 1 ≤ count * probability) : (1-probability)^count ≤ 1/2 := by
  have bernoulli := one_add_mul_le_pow (show (-2 : ℝ) ≤ probability by linarith) count
  have twice : 2 ≤ (1+probability)^count := by linarith
  have product : (1-probability)^count * (1+probability)^count ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) (by nlinarith [sq_nonneg probability])
  have scaled := mul_le_mul_of_nonneg_left twice (pow_nonneg (by linarith : 0 ≤ 1-probability) count)
  nlinarith

/-- The appendix's 2^80 cutoff has tail strictly below 2^-256 under the stated contraction. -/
theorem cutoff : (1-(1 : ℝ)/2^17)^(2^80 : Nat) < 1/2^256 := by
  have block : (1-(1 : ℝ)/2^17)^(2^17 : Nat) ≤ 1/2 :=
    block_bound _ _ (by norm_num) (by norm_num) (by norm_num)
  have exponent : (2^80 : Nat) = 2^17 * 2^63 := by decide
  rw [exponent, pow_mul]
  calc
    _ ≤ (1/2 : ℝ)^(2^63 : Nat) := pow_le_pow_left₀ (by norm_num) block _
    _ ≤ (1/2 : ℝ)^257 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by decide)
    _ < _ := by
      rw [show (257 : Nat) = 256 + 1 from rfl, pow_succ]
      norm_num [div_pow]

end GeometricSurvival

/-! Actual uniform-prefix survival probabilities and their finite-horizon contraction. -/
namespace GenerationSurvival
open WalletGeneration WalletFinite TranscriptErasure
open FailureTests GameExpectation MomentTools
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]
abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)

def game (q : Passphrase) (target : Check) (count : Nat) : PMF Bool :=
  (RandomTrialLists.law (Entropy := Entropy) count).bind fun trials =>
    (PMF.uniformOfFintype (Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))).map
      (fun table => allFail table q target trials)

def pairs (q : Passphrase) (target : Check) (count : Nat) : PMF (Bool × Bool) :=
  (RandomTrialLists.law (Entropy := Entropy) count).bind (TrialPairs.fixed (Seed := Seed) (Tail := Tail) q target)

theorem left_law (q : Passphrase) (target : Check) (count : Nat) : (pairs (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count).map Prod.fst = game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count := by
  simp only [pairs, game, PMF.map_bind, TrialPairs.left_law]

theorem next_law (q : Passphrase) (target : Check) (count : Nat) : (pairs (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count).map (fun value => value.1 && !value.2) = game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target (count+1) := by
  simp only [pairs, game, RandomTrialLists.step, PMF.map_bind, PMF.map_comp, PMF.bind_bind,
    PMF.bind_map, Function.comp_def, TrialPairs.fixed, append_last]
  congr 1
  funext trials
  exact PMF.bind_comm _ _ _

theorem scores (q : Passphrase) (target : Check) (count : Nat) (test : Bool × Bool → Bool) :
    (((pairs (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count).map test) true) =
      moment (RandomTrialLists.law (Entropy := Entropy) count) (fun trials => ((TrialPairs.fixed (Seed := Seed) (Tail := Tail) q target trials).map test) true) := by
  simp only [pairs, PMF.map_bind, PMF.bind_apply, moment]

theorem progress_lower (q : Passphrase) (target : Check) (count : Nat)
    (entropyBound : 4*count ≤ Fintype.card Entropy) (seedBound : 4*count ≤ Fintype.card Seed) :
    (1 / ((2*Fintype.card Check : Nat) : ENNReal)) *
      (((pairs (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count).map Prod.fst) true) ≤
      (((pairs (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count).map (fun value => value.1 && value.2)) true) := by
  rw [scores, scores]
  calc
    _ = moment (RandomTrialLists.law (Entropy := Entropy) count) (fun trials =>
        (1/((2*Fintype.card Check : Nat) : ENNReal)) * ((TrialPairs.fixed (Seed := Seed) (Tail := Tail) q target trials).map Prod.fst) true) := by
      simpa only [mul_comm] using (mul_const (RandomTrialLists.law (Entropy := Entropy) count)
        (fun trials => ((TrialPairs.fixed (Seed := Seed) (Tail := Tail) q target trials).map Prod.fst) true)
        (1/((2*Fintype.card Check : Nat) : ENNReal))).symm
    _ ≤ _ := by
      rw [RandomTrialLists.law, moment_map, moment_map]
      apply MomentTools.mono
      intro vector
      exact TrialPairs.fixed_lower q target (List.ofFn vector)
        (by simpa only [List.length_ofFn] using entropyBound) (by simpa only [List.length_ofFn] using seedBound)

def survival (q : Passphrase) (target : Check) (count : Nat) : ℝ :=
  ((game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count) true).toReal

theorem contraction (q : Passphrase) (target : Check) (count : Nat)
    (entropyBound : 4*count ≤ Fintype.card Entropy) (seedBound : 4*count ≤ Fintype.card Seed) :
    survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target (count+1) ≤
      (1 - 1/((2*Fintype.card Check : Nat) : ℝ)) * survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count := by
  have lower := ENNReal.toReal_mono (PMF.apply_ne_top _ _) (progress_lower (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count entropyBound seedBound)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] at lower
  have bound := BoolPartition.contraction (pairs (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target count)
    (1/((2*Fintype.card Check : Nat) : ℝ)) lower
  rw [left_law, next_law] at bound
  exact bound

theorem start (q : Passphrase) (target : Check) : survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target 0 = 1 := by
  simp only [survival, game, RandomTrialLists.law, PMF.bind_map, Function.comp_def,
    List.ofFn_zero, allFail, List.all_nil, PMF.bind_const]
  have law : (PMF.uniformOfFintype (Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))).map (fun _ => true) = PMF.pure true :=
    PMF.map_const _ true
  rw [law, PMF.pure_apply_self, ENNReal.toReal_one]

end GenerationSurvival

/-! Specialize the actual generation contraction to the appendix's domain widths and cutoff. -/
namespace GenerationBounds
open GenerationSurvival
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev cutoff : Nat := 2^80

theorem source_step (q : Passphrase) (target : Check) (entropyWidth : Fintype.card Entropy = 2^256)
    (seedWidth : Fintype.card Seed = 2^512) (checkWidth : Fintype.card Check = 2^16) (n : Nat)
    (within : n < cutoff) : survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target (n+1) ≤
      (1-(1 : ℝ)/2^17) * survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target n := by
  have entropyBound : 4*n ≤ Fintype.card Entropy := by
    rw [entropyWidth]
    exact (Nat.mul_le_mul_left 4 (Nat.le_of_lt within)).trans (by decide)
  have seedBound : 4*n ≤ Fintype.card Seed := by
    rw [seedWidth]
    exact (Nat.mul_le_mul_left 4 (Nat.le_of_lt within)).trans
      ((show 4*cutoff ≤ (2^256 : Nat) from by decide).trans
        (pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 2) (by decide : 256 ≤ 512)))
  have bound := contraction (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target n entropyBound seedBound
  simpa only [checkWidth, show (2 * 2^16 : Nat) = 2^17 from by decide, Nat.cast_pow, Nat.cast_ofNat] using bound

theorem expected_survival (q : Passphrase) (target : Check)
    (entropyWidth : Fintype.card Entropy = 2^256) (seedWidth : Fintype.card Seed = 2^512)
    (checkWidth : Fintype.card Check = 2^16) : (∑ n ∈ Finset.range cutoff, survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target n) ≤ (2 : ℝ)^17 := by
  have bound := GeometricSurvival.expected_bound_until
    (survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target) (1-(1 : ℝ)/2^17) cutoff
    (fun _ _ => ENNReal.toReal_nonneg) (by norm_num)
    (start (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target)
    (source_step q target entropyWidth seedWidth checkWidth)
  have denominator : 1 / (1-(1-(1 : ℝ)/2^17)) = (2 : ℝ)^17 := by norm_num
  simpa only [denominator] using bound

theorem cutoff_tail (q : Passphrase) (target : Check) (entropyWidth : Fintype.card Entropy = 2^256)
    (seedWidth : Fintype.card Seed = 2^512) (checkWidth : Fintype.card Check = 2^16) :
    survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target cutoff < (1 : ℝ)/2^256 := by
  have bound := GeometricSurvival.tail_bound_until
    (survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target) (1-(1 : ℝ)/2^17) cutoff
    (by norm_num) (start (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target)
    (source_step q target entropyWidth seedWidth checkWidth) cutoff le_rfl
  exact bound.trans_lt GeometricSurvival.cutoff

/-- The same cutoff bound in the ENNReal probability domain used for game hopping. -/
theorem cutoff_tail_enn (q : Passphrase) (target : Check)
    (entropyWidth : Fintype.card Entropy = 2^256) (seedWidth : Fintype.card Seed = 2^512)
    (checkWidth : Fintype.card Check = 2^16) : ((GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target cutoff) true) <
      (1 : ENNReal)/2^256 := by
  apply (ENNReal.toReal_lt_toReal (PMF.apply_ne_top _ _) (by simp)).mp
  have simpaTerm := cutoff_tail (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target entropyWidth seedWidth checkWidth
  (try simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at simpaTerm ⊢)
  exact simpaTerm

end GenerationBounds

/-! Exact finite tail-sum identity for the capped number of trials. -/
namespace CountTails

theorem nat_sum (count limit : Nat) (bounded : count ≤ limit) :
    count = ∑ index ∈ Finset.range limit, if index < count then 1 else 0 := by
  have truncated : (Finset.range limit).filter (fun index => index < count) = Finset.range count := by
    ext index
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, truncated]
  simp

noncomputable section
open GameExpectation MomentTools

theorem enn_sum (count limit : Nat) (bounded : count ≤ limit) :
    (count : ENNReal) = ∑ index : Fin limit, if index.val < count then 1 else 0 := by
  have casted := congrArg (fun value : Nat => (value : ENNReal)) (nat_sum count limit bounded)
  try dsimp only at casted
  rw [Nat.cast_sum] at casted
  simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← Fin.sum_univ_eq_sum_range] using casted

/-- Integrating the identity needs no independence between the stopping count and oracle values. -/
theorem mean {Outcome : Type} (distribution : PMF Outcome) (count : Outcome → Nat) (limit : Nat)
    (bounded : ∀ outcome, count outcome ≤ limit) :
    moment distribution (fun outcome => (count outcome : ENNReal)) =
      ∑ index : Fin limit, moment distribution (fun outcome => if index.val < count outcome then 1 else 0) := by
  calc
    _ = moment distribution (fun outcome => ∑ index : Fin limit, if index.val < count outcome then 1 else 0) := by
      congr 1
      funext outcome
      exact enn_sum _ _ (bounded outcome)
    _ = _ := finite_sum _ _

end
end CountTails

/-! Actual query-count stopping time and failure of every shorter trial prefix. -/
namespace StoppedPrefix
open WalletGeneration TranscriptErasure RejectedIndices
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]

theorem count_cons (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase) (target : Check)
    (e : Entropy) (trials : List Entropy) :
    let d : Seed := table (Point.s e q)
    count table q target (e :: trials) = if (table (Point.t d)).1 = target then 1 else count table q target trials + 1 := by
  unfold count
  rw [execution_cons]
  dsimp only
  split_ifs <;> simp only [List.length_cons, List.length_nil, List.length_append]
  all_goals omega

variable (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase) (target : Check)

theorem positive (e : Entropy) (trials : List Entropy) : 0 < count table q target (e :: trials) := by
  rw [count_cons]
  split_ifs <;> omega

theorem count_bound (trials : List Entropy) : count table q target trials ≤ trials.length := by
  induction trials with
  | nil => simp only [count, loop, execute_pure, List.length_nil, Nat.zero_div, le_refl]
  | cons e trials ih =>
    rw [count_cons]
    split_ifs <;> simp only [List.length_cons] <;> omega

/-- For n below the full trial budget, J>n exactly means that the first n trials all failed. -/
theorem before_count (trials : List Entropy) (n : Nat) (within : n < trials.length) :
    n < count table q target trials ↔ (execute table (loop q target (trials.take n))).1 = none := by
  induction trials generalizing n with
  | nil => simp only [List.length_nil] at within; omega
  | cons e trials ih =>
    cases n with
    | zero =>
      simp only [List.take_zero, loop, execute_pure, iff_true]
      exact positive table q target e trials
    | succ n =>
      have inside : n < trials.length := by simp only [List.length_cons] at within; omega
      rw [List.take_succ_cons, count_cons, execution_cons]
      dsimp only
      split_ifs
      · constructor
        · intro impossible; omega
        · intro impossible; cases impossible
      · simpa only [Nat.add_lt_add_iff_right] using ih n inside

end StoppedPrefix

/-! Connect the actual capped generator's raw sampling, failure event and stopping count. -/
namespace GenerationRaw
open WalletGeneration WalletFinite WalletLaws
open TranscriptErasure ProbabilityTools GameExpectation MomentTools
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)
abbrev Raws (limit : Nat) := Raw (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) limit

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

omit [DecidableEq Check] in
/-- Marginalize the unused fallback, then exchange the two independent draws. -/
theorem sampled {Result : Type} (limit : Nat)
    (read : WalletTables → List Entropy → Result) :
    (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => read raw.1 (List.ofFn raw.2.1)) =
    (RandomTrialLists.law (Entropy := Entropy) limit).bind fun trials =>
      (PMF.uniformOfFintype (WalletTables)).map
        (fun table => read table trials) := by
  rw [uniform_product, uniform_product]
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have drop (table : WalletTables)
      (trials : Fin limit → Entropy) :
      (PMF.uniformOfFintype (Selected Entropy Seed Tail)).map (fun _ => read table (List.ofFn trials)) =
        PMF.pure (read table (List.ofFn trials)) := PMF.map_const _ _
  simp_rw [drop]
  simp only [RandomTrialLists.law, PMF.bind_map, Function.comp_def]
  have simpaTerm := (PMF.bind_comm (PMF.uniformOfFintype (WalletTables)) (PMF.uniformOfFintype (Fin limit → Entropy)) (fun table trials => PMF.pure (read table (List.ofFn trials))))
  (try simp only [PMF.map] at simpaTerm ⊢)
  exact simpaTerm

/-- Failure of the generator is exactly the actual survival experiment. -/
theorem failure_law (limit : Nat) (q : Passphrase) (target : Check) :
    (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => decide ((execute raw.1 (loop q target (List.ofFn raw.2.1))).1 = none)) =
    GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target limit := by
  rw [sampled limit (fun table trials => decide ((execute table (loop q target trials)).1 = none))]
  unfold GenerationSurvival.game
  congr 1
  funext trials
  congr 1
  funext table
  simp only [FailureTests.none_iff, Bool.decide_eq_true]

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
theorem take_vector (n extra : Nat) (trials : Fin (n+extra) → Entropy) :
    (List.ofFn trials).take n = List.ofFn (fun index : Fin n => trials (Fin.castAdd extra index)) := by
  rw [List.ofFn_add]
  have take (a b : List Entropy) : (a ++ b).take a.length = a := List.take_left
  have simpaTerm := take (List.ofFn (fun i : Fin n => trials (Fin.castAdd extra i))) (List.ofFn (fun i : Fin extra => trials (Fin.natAdd n i)))
  (try simp only [List.length_ofFn] at simpaTerm ⊢)
  exact simpaTerm

/-- All shorter prefixes retain the same uniform law as independently drawn prefixes. -/
theorem prefix_game (n extra : Nat) (q : Passphrase) (target : Check) :
    (RandomTrialLists.law (Entropy := Entropy) (n+extra)).bind
      (fun trials => (PMF.uniformOfFintype (WalletTables)).map
        (fun table => decide ((execute table (loop q target (trials.take n))).1 = none))) =
    GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target n := by
  simp only [RandomTrialLists.law, PMF.bind_map, Function.comp_def, take_vector]
  calc
    _ = ((PMF.uniformOfFintype (Fin (n+extra) → Entropy)).map
      (fun trials => fun index : Fin n => trials (Fin.castAdd extra index))).bind
      (fun trials => (PMF.uniformOfFintype (WalletTables)).map
        (fun table => decide ((execute table (loop q target (List.ofFn trials))).1 = none))) := by
      rw [PMF.bind_map]
      rfl
    _ = _ := by
      rw [RandomTrialLists.prefix_law]
      unfold GenerationSurvival.game
      simp only [RandomTrialLists.law, PMF.bind_map, Function.comp_def, FailureTests.none_iff,
        Bool.decide_eq_true]

/-- Tail probabilities of J come from the actual executed loop, not an independent count. -/
theorem count_tail (limit n : Nat) (q : Passphrase) (target : Check) (within : n < limit) :
    (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => decide (n < RejectedIndices.count raw.1 q target (List.ofFn raw.2.1))) =
    GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target n := by
  rw [sampled limit (fun table trials => decide (n < RejectedIndices.count table q target trials))]
  have equivalent :
      ((RandomTrialLists.law (Entropy := Entropy) limit).bind fun trials =>
      (PMF.uniformOfFintype (WalletTables)).map
        (fun table => decide (n < RejectedIndices.count table q target trials))) =
      ((RandomTrialLists.law (Entropy := Entropy) limit).bind fun trials =>
      (PMF.uniformOfFintype (WalletTables)).map
        (fun table => decide ((execute table (loop q target (trials.take n))).1 = none))) := by
    simp only [RandomTrialLists.law, PMF.bind_map, Function.comp_def]
    congr 1
    funext trials
    congr 1
    funext table
    simp only [StoppedPrefix.before_count table q target (List.ofFn trials) n
      (by simpa only [List.length_ofFn] using within)]
  rw [equivalent]
  obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le within.le
  subst limit
  exact prefix_game n extra q target

end GenerationRaw

/-! Exact expectation and source-width bounds for the executed generator's trial count. -/
namespace GenerationCount
open WalletGeneration TranscriptErasure GameExpectation MomentTools
open GenerationRaw
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

def mean (limit : Nat) (q : Passphrase) (target : Check) : ENNReal :=
  moment (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit))
    (fun raw => (RejectedIndices.count raw.1 q target (List.ofFn raw.2.1) : ENNReal))

theorem mean_eq (limit : Nat) (q : Passphrase) (target : Check) : mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target =
      ∑ index : Fin limit, (GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index.val) true := by
  unfold mean
  rw [CountTails.mean _ _ limit (fun raw => by
    simpa only [List.length_ofFn] using StoppedPrefix.count_bound raw.1 q target (List.ofFn raw.2.1))]
  apply Finset.sum_congr rfl
  intro index _
  have law := congrArg (fun distribution : PMF Bool => distribution true) (count_tail (Entropy := Entropy)
    (Seed := Seed) (Tail := Tail) limit index.val q target index.isLt)
  simpa only [probability, decide_eq_true_eq] using law

theorem mean_finite (limit : Nat) (q : Passphrase) (target : Check) : mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target ≠ ⊤ := by
  rw [mean_eq]
  exact ENNReal.sum_ne_top.mpr (fun _ _ => PMF.apply_ne_top _ _)

/-- The first 2^80 trials have expected stopping count at most 2^17. -/
theorem source_mean (q : Passphrase) (target : Check) (entropyWidth : Fintype.card Entropy = 2^256)
    (seedWidth : Fintype.card Seed = 2^512) (checkWidth : Fintype.card Check = 2^16) : mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) GenerationBounds.cutoff q target ≤ (2 : ENNReal)^17 := by
  apply (ENNReal.toReal_le_toReal (mean_finite _ q target) (by simp)).mp
  rw [mean_eq, ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have bound := GenerationBounds.expected_survival (Entropy := Entropy) (Seed := Seed) (Tail := Tail)
    q target entropyWidth seedWidth checkWidth
  simpa only [GenerationSurvival.survival, ← Fin.sum_univ_eq_sum_range] using bound

/-- The real raw generator fails at the cutoff with probability strictly below 2^-256. -/
theorem source_abort (q : Passphrase) (target : Check) (entropyWidth : Fintype.card Entropy = 2^256)
    (seedWidth : Fintype.card Seed = 2^512) (checkWidth : Fintype.card Check = 2^16) :
    ((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)
      GenerationBounds.cutoff)).map
      (fun raw => decide ((execute raw.1 (loop q target (List.ofFn raw.2.1))).1 = none))) true < (1 : ENNReal)/2^256 := by
  rw [failure_law]
  exact GenerationBounds.cutoff_tail_enn q target entropyWidth seedWidth checkWidth

end GenerationCount

/-! Membership events for an optional point, integrated over their complete context. -/
namespace FiberMembership
variable {Context Domain : Type} [Fintype Domain] [DecidableEq Domain]

def test (matching : Context → Finset Domain) (observation : Context × Option Domain) : Bool :=
  observation.2.any fun point => decide (point ∈ matching observation.1)

theorem mass (distribution : PMF (Context × Option Domain)) (matching : Context → Finset Domain) :
    (distribution.map (test matching)) true =
      ∑' context, ∑ point ∈ matching context, distribution (context,some point) := by
  classical
  rw [MomentTools.probability, GameExpectation.moment, ENNReal.tsum_prod']
  apply tsum_congr
  intro context
  rw [tsum_fintype]
  simp only [Fintype.sum_option, test, Option.any_none, Bool.false_eq_true, if_false, mul_zero,
    Option.any_some, decide_eq_true_eq, mul_ite, mul_one, zero_add]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- An enabled-point union costs at most the sum of its individual event probabilities. -/
theorem union_bound {Outcome Index : Type} [Fintype Index] (distribution : PMF Outcome)
    (events : Index → Outcome → Bool) :
    (distribution.map (fun outcome => decide (∃ index, events index outcome = true))) true ≤
      ∑ index, (distribution.map (events index)) true := by
  classical
  rw [MomentTools.probability]
  simp_rw [MomentTools.probability]
  rw [← MomentTools.finite_sum]
  apply MomentTools.mono
  intro outcome
  by_cases existsEvent : ∃ index, events index outcome = true
  · simp only [existsEvent, decide_true, if_true]
    obtain ⟨index, active⟩ := existsEvent
    have included := Finset.single_le_sum (f := fun i => if events i outcome then (1 : ENNReal) else 0)
      (fun _ _ => zero_le) (Finset.mem_univ index)
    simpa only [active, if_true] using included
  · simp only [existsEvent, decide_false, Bool.false_eq_true, if_false]
    exact zero_le

end FiberMembership

/-! Sum actual rejected-point hits, preserving their existence probabilities and the stopping count. -/
namespace GenerationHits
open WalletGeneration TranscriptErasure GameExpectation MomentTools
open GenerationRaw
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]
abbrev Contexts := RejectedEntropyModel.Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)

def entropyEvent {limit : Nat} (q : Passphrase) (target : Check)
    (matching : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) → Finset Entropy)
    (index : Fin limit) (raw : Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit) : Bool :=
  FiberMembership.test matching (RejectedEntropyModel.observe q target index raw)

def seedEvent {limit : Nat} (q : Passphrase) (target : Check)
    (matching : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) → Finset Seed)
    (index : Fin limit) (raw : Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit) : Bool :=
  FiberMembership.test matching (RejectedSeedModel.observe q target index raw)

/-- A rejected-index existence event is bounded by the corresponding actual count tail. -/
theorem enabled_count {limit : Nat} (q : Passphrase) (target : Check) (index : Fin limit) :
    (((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => decide (RejectedEntropyModel.enabled index (WalletJointLaw.joint q target raw)))) true) ≤
    (GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index.val) true := by
  rw [← count_tail limit index.val q target index.isLt]
  rw [probability, probability]
  apply MomentTools.mono
  intro raw
  by_cases active : RejectedEntropyModel.enabled index (WalletJointLaw.joint q target raw)
  · have later : index.val < RejectedIndices.count raw.1 q target (List.ofFn raw.2.1) := by
      have bound := active.2
      change index.val+1 < RejectedIndices.count raw.1 q target (List.ofFn raw.2.1) at bound
      omega
    simp only [active, later, decide_true, if_true, le_refl]
  · simp only [active, decide_false, Bool.false_eq_true, if_false]
    exact zero_le

theorem entropy_index {limit : Nat} (q : Passphrase) (target : Check) (index : Fin limit)
    (large : 2 ≤ Fintype.card Entropy)
    (matching : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) → Finset Entropy)
    (budget : Nat) (size : ∀ context, (matching context).card ≤ budget) :
    (((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (entropyEvent q target matching index)) true) ≤
      ((budget : ENNReal)/((Fintype.card Entropy-1 : Nat) : ENNReal)) *
        (GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index.val) true := by
  have bound := RejectedEntropyProbability.matching_bound (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index large matching budget size
  rw [← FiberMembership.mass] at bound
  have same : ((RejectedEntropyProbability.law (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index).map Prod.fst).map
      (fun context => decide (RejectedEntropyModel.enabled index context)) =
      (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => decide (RejectedEntropyModel.enabled index (WalletJointLaw.joint q target raw))) := by
    simp only [RejectedEntropyProbability.law, PMF.map_comp, Function.comp_def,
      RejectedEntropyModel.observe]
  rw [same] at bound
  have first := bound.trans (mul_le_mul_right (enabled_count (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index) _)
  (try simp only [entropyEvent, RejectedEntropyProbability.law, PMF.map_comp, Function.comp_def] at first ⊢)
  exact first

theorem seed_index {limit : Nat} (q : Passphrase) (target : Check) (index : Fin limit)
    (large : 2 ≤ Fintype.card Seed)
    (matching : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) → Finset Seed)
    (budget : Nat) (size : ∀ context, (matching context).card ≤ budget) :
    (((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (seedEvent q target matching index)) true) ≤
      ((budget : ENNReal)/((Fintype.card Seed-1 : Nat) : ENNReal)) *
        (GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index.val) true := by
  have bound := RejectedSeedProbability.matching_bound (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index large matching budget size
  rw [← FiberMembership.mass] at bound
  have same : ((RejectedSeedProbability.law (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index).map Prod.fst).map
      (fun context => decide (RejectedSeedModel.enabled index context)) =
      (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => decide (RejectedEntropyModel.enabled index (WalletJointLaw.joint q target raw))) := by
    simp only [RejectedSeedProbability.law, PMF.map_comp, Function.comp_def,
      RejectedSeedModel.observe, RejectedSeedModel.enabled, RejectedEntropyModel.enabled]
    rfl
  rw [same] at bound
  have first := bound.trans (mul_le_mul_right (enabled_count (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index) _)
  (try simp only [seedEvent, RejectedSeedProbability.law, PMF.map_comp, Function.comp_def] at first ⊢)
  exact first

/-- The complete rejected-entropy hit union is charged to E[J], not to the cutoff. -/
theorem entropy_union (limit : Nat) (q : Passphrase) (target : Check)
    (large : 2 ≤ Fintype.card Entropy)
    (matching : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) → Finset Entropy)
    (budget : Nat) (size : ∀ context, (matching context).card ≤ budget) :
    (((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => decide (∃ index, entropyEvent q target matching index raw = true))) true) ≤
      ((budget : ENNReal)/((Fintype.card Entropy-1 : Nat) : ENNReal)) *
        GenerationCount.mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target := by
  calc
    _ ≤ ∑ index : Fin limit, (((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (entropyEvent q target matching index)) true) := by
        simpa only [MomentTools.probability, decide_eq_true_eq] using
          FiberMembership.union_bound
            (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit))
            (entropyEvent q target matching) 
    _ ≤ ∑ index : Fin limit, ((budget : ENNReal)/((Fintype.card Entropy-1 : Nat) : ENNReal)) *
      (GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index.val) true :=
        Finset.sum_le_sum (fun index _ => entropy_index q target index large matching budget size)
    _ = _ := by rw [← Finset.mul_sum, ← GenerationCount.mean_eq]

theorem seed_union (limit : Nat) (q : Passphrase) (target : Check)
    (large : 2 ≤ Fintype.card Seed)
    (matching : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) → Finset Seed)
    (budget : Nat) (size : ∀ context, (matching context).card ≤ budget) :
    (((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (fun raw => decide (∃ index, seedEvent q target matching index raw = true))) true) ≤
      ((budget : ENNReal)/((Fintype.card Seed-1 : Nat) : ENNReal)) *
        GenerationCount.mean (Entropy := Entropy) (Seed := Seed) (Tail := Tail) limit q target := by
  calc
    _ ≤ ∑ index : Fin limit, (((PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit)).map
      (seedEvent q target matching index)) true) := by
        simpa only [MomentTools.probability, decide_eq_true_eq] using
          FiberMembership.union_bound
            (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) limit))
            (seedEvent q target matching) 
    _ ≤ ∑ index : Fin limit, ((budget : ENNReal)/((Fintype.card Seed-1 : Nat) : ENNReal)) *
      (GenerationSurvival.game (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index.val) true :=
        Finset.sum_le_sum (fun index _ => seed_index q target index large matching budget size)
    _ = _ := by rw [← Finset.mul_sum, ← GenerationCount.mean_eq]

end GenerationHits

end
end MhfeLean
