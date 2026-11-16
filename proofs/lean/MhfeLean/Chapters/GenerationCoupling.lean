-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.GenerationSampling
import MhfeLean.Chapters.Probability

namespace MhfeLean
noncomputable section

/-! # Erase rejected profile trials while retaining the joint law
-/

/-! Finite transitive symmetry determines uniform marginal laws. -/
namespace UniformSymmetry
variable {Value Index : Type}

theorem map_equiv_at (distribution : PMF Value) (action : Equiv.Perm Value) (value : Value) :
    (distribution.map action) (action value) = distribution value := by
  simpa only [Equiv.symm_apply_apply] using
    ProbabilityTools.equiv_apply distribution action (action value)

/-- A uniform input law transports equivariant observations to an invariant output law. -/
theorem equivariant_uniform {Raw : Type} [Fintype Raw] [Nonempty Raw] (observe : Raw → Value)
    (input : Equiv.Perm Raw) (output : Equiv.Perm Value)
    (natural : ∀ raw,observe (input raw)=output (observe raw)) :
    ((PMF.uniformOfFintype Raw).map observe).map output=(PMF.uniformOfFintype Raw).map observe := by
  rw [PMF.map_comp]
  have commutes : output ∘ observe=observe ∘ input := (funext natural).symm
  rw [commutes,← PMF.map_comp,PMF.uniformOfFintype_map_of_bijective input input.bijective]

/-- Invariance under any transitive family, not necessarily all permutations, forces uniformity. -/
theorem uniform_of_transitive [Fintype Value] [Nonempty Value] (distribution : PMF Value)
    (actions : Index → Equiv.Perm Value)
    (transitive : ∀ first second, ∃ action, actions action first = second)
    (invariant : ∀ action, distribution.map (actions action) = distribution) :
    distribution = PMF.uniformOfFintype Value := by
  classical
  have constant : ∀ first second, distribution first = distribution second := by
    intro first second
    obtain ⟨action, moves⟩ := transitive first second
    have mass := map_equiv_at distribution (actions action) first
    rw [invariant, moves] at mass
    exact mass.symm
  ext value
  rw [PMF.uniformOfFintype_apply]
  have total : (Fintype.card Value : ENNReal) * distribution value = 1 := by
    calc
      _ = ∑ x : Value, distribution x := by
        simp_rw [constant (second := value)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 1 := by simpa only [tsum_fintype] using distribution.tsum_coe
  have nonzero : (Fintype.card Value : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have finite : (Fintype.card Value : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have scaled := congrArg (fun x : ENNReal => (Fintype.card Value : ENNReal)⁻¹ * x) total
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel nonzero finite, one_mul, mul_one] using scaled

end UniformSymmetry

/-! Uniformity of the selected triple, with a symmetric fallback at the finite cutoff. -/
namespace WalletLaws
open WalletGeneration WalletFinite TranscriptErasure
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Tail] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Raw (count : Nat) := Table (spec Entropy Passphrase Seed Check Tail) ×
  (Fin count → Entropy) × Selected Entropy Seed Tail

def observe {count : Nat} (q : Passphrase) (target : Check) (raw : Raw (Entropy := Entropy)
    (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) : Selected Entropy Seed Tail :=
  ((execute raw.1 (loop q target (List.ofFn raw.2.1))).1).getD raw.2.2

def rawAction {count : Nat} (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed)
    (tail : Equiv.Perm Tail) : Equiv.Perm (Raw (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) :=
  Equiv.prodCongr (WalletSymmetry.tableEquiv entropy seed tail)
    (Equiv.prodCongr (trialAction entropy) (selectedAction entropy seed tail))

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Tail]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- An abort is assigned an independent uniform triple; relabelling preserves that fallback too. -/
theorem natural {count : Nat} (q : Passphrase) (target : Check)
    (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail)
    (raw : Raw (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) :
    observe q target (rawAction entropy seed tail raw) = selectedAction entropy seed tail (observe q target raw) := by
  have trials : List.ofFn ((trialAction entropy) raw.2.1) = (List.ofFn raw.2.1).map entropy := by
    simp only [trialAction, Equiv.coe_fn_mk, List.map_ofFn]
    rfl
  change ((execute (WalletSymmetry.relabel entropy seed tail raw.1)
      (loop q target (List.ofFn ((trialAction entropy) raw.2.1)))).1).getD
        (selectedAction entropy seed tail raw.2.2) = _
  rw [trials, WalletSymmetry.loop_natural]
  unfold observe
  cases chosen : (execute raw.1 (loop q target (List.ofFn raw.2.1))).1 <;> rfl

def law (count : Nat) (q : Passphrase) (target : Check) : PMF (Selected Entropy Seed Tail) :=
  (PMF.uniformOfFintype (Raw (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count)).map (observe q target)

omit [DecidableEq Tail] in
theorem invariant (count : Nat) (q : Passphrase) (target : Check) (entropy : Equiv.Perm Entropy)
    (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail) :
    (law count q target).map (selectedAction entropy seed tail) = law count q target := by
  exact UniformSymmetry.equivariant_uniform (observe q target)
    (rawAction entropy seed tail) (selectedAction entropy seed tail)
    (natural q target entropy seed tail)

/-- The selected E, seed and 240-bit tail are jointly uniform, not merely separate uniform marginals. -/
theorem selected_uniform (count : Nat) (q : Passphrase) (target : Check) : law (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count q target =
      PMF.uniformOfFintype (Selected Entropy Seed Tail) := by
  let actions : (Equiv.Perm Entropy × Equiv.Perm Seed × Equiv.Perm Tail) → Equiv.Perm (Selected Entropy Seed Tail) :=
    fun action => selectedAction action.1 action.2.1 action.2.2
  apply UniformSymmetry.uniform_of_transitive _ actions
  · intro first second
    refine ⟨(Equiv.swap first.entropy second.entropy, Equiv.swap first.seed second.seed,
      Equiv.swap first.tail second.tail), ?_⟩
    cases first with
    | mk e1 d1 t1 =>
      cases second with
      | mk e2 d2 t2 =>
        change Selected.mk (Equiv.swap e1 e2 e1) (Equiv.swap d1 d2 d1) (Equiv.swap t1 t2 t1) = _
        rw [Equiv.swap_apply_left, Equiv.swap_apply_left, Equiv.swap_apply_left]
  · intro action
    exact invariant count q target action.1 action.2.1 action.2.2

end WalletLaws

/-! Exact generation-erasure representation of the programmed S/T experiment. -/
namespace WalletErasureLaw
open WalletGeneration WalletFinite WalletLaws
open TranscriptErasure ProbabilityTools
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Tail] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)
abbrev Context (count : Nat) := (Fin count → Entropy) × Selected Entropy Seed Tail
abbrev RawSeed (count : Nat) := Raw (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) count

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

def programmed (q : Passphrase) (target : Check) : PMF (Selected Entropy Seed Tail × WalletTables) :=
  (PMF.uniformOfFintype (Selected Entropy Seed Tail)).bind fun chosen =>
    (PMF.uniformOfFintype (WalletTables)).map fun fresh =>
      (chosen, restore q target (some chosen) fresh)

def freshAfter (count : Nat) (q : Passphrase) (target : Check) :
    PMF (Selected Entropy Seed Tail × WalletTables) :=
  (PMF.uniformOfFintype (RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count)).bind fun raw =>
    (PMF.uniformOfFintype (WalletTables)).map fun fresh =>
      (observe q target raw, restore q target (some (observe q target raw)) fresh)

/-- The erased generation's selected triple has exactly the programmed experiment's joint law. -/
theorem fresh_after_eq (count : Nat) (q : Passphrase) (target : Check) : freshAfter (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count q target = programmed q target := by
  let kernel := fun chosen : Selected Entropy Seed Tail =>
    (PMF.uniformOfFintype (WalletTables)).map fun fresh =>
      (chosen, restore q target (some chosen) fresh)
  calc
    _ = (law (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count q target).bind kernel := by
      simp only [freshAfter, law, PMF.bind_map, Function.comp_def, kernel]
    _ = _ := by rw [selected_uniform]; rfl

/-- Rerandomize every generator-read point, then restore the selected or cutoff-fallback values. -/
def erasedAfter (count : Nat) (q : Passphrase) (target : Check) :
    PMF (Selected Entropy Seed Tail × WalletTables) :=
  (PMF.uniformOfFintype (Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count)).bind fun context =>
    (PMF.uniformOfFintype (WalletTables ×
      WalletTables)).map fun tables =>
      let program := loop q target (List.ofFn context.1)
      let chosen := (execute tables.1 program).1.getD context.2
      (chosen, restore q target (some chosen) (exchanged program tables).2)

/-- The actual read-point erasure, including its fallback convention, matches the programmed law. -/
theorem erased_after_eq (count : Nat) (q : Passphrase) (target : Check) : erasedAfter (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count q target = programmed q target := by
  let tablesLaw := PMF.uniformOfFintype (WalletTables)
  let contextLaw := PMF.uniformOfFintype (Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count)
  let view := fun (context : Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count)
      (table fresh : WalletTables) =>
    let chosen := (execute table (loop q target (List.ofFn context.1))).1.getD context.2
    (chosen, restore q target (some chosen) fresh)
  have erasure : erasedAfter count q target = contextLaw.bind (fun context =>
      (PMF.uniformOfFintype (WalletTables ×
        WalletTables)).map
        (fun tables => view context tables.1 tables.2)) := by
    unfold erasedAfter
    congr 1
    funext context
    exact erased_distribution (loop q target (List.ofFn context.1)) (fun trace fresh =>
      let chosen := trace.1.getD context.2
      (chosen, restore q target (some chosen) fresh))
  have pairLaw : PMF.uniformOfFintype (WalletTables ×
      WalletTables) =
      independentPair tablesLaw tablesLaw := uniform_product
  have rawLaw : PMF.uniformOfFintype (RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) =
      independentPair tablesLaw contextLaw := uniform_product
  calc
    _ = contextLaw.bind fun context => tablesLaw.bind fun table => tablesLaw.map (view context table) := by
      rw [erasure, pairLaw]
      simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
    _ = tablesLaw.bind fun table => contextLaw.bind fun context => tablesLaw.map (view context table) :=
      PMF.bind_comm contextLaw tablesLaw _
    _ = freshAfter count q target := by
      unfold freshAfter
      rw [rawLaw]
      simp only [independentPair, PMF.bind_map, PMF.bind_bind, Function.comp_def, view, observe]
      rfl
    _ = _ := fresh_after_eq count q target

end WalletErasureLaw

/-! Transitive symmetry within each retained context gives exact joint independence. -/
namespace FiberSymmetry
open ProbabilityTools UniformSymmetry
variable {Context Value Index : Type} [Fintype Value] [Nonempty Value]

omit [Nonempty Value] in
theorem fst_mass (distribution : PMF (Context × Value)) (context : Context) :
    (distribution.map Prod.fst) context = ∑ value : Value, distribution (context, value) := by
  classical
  letI : DecidableEq Context := Classical.decEq Context
  rw [PMF.map_apply]
  rw [ENNReal.tsum_prod']
  have split (c : Context) :
      (∑' value : Value, if context = c then distribution (c,value) else 0) =
      if context = c then ∑' value : Value, distribution (c,value) else 0 := by
    by_cases same : context = c <;> simp only [same, if_true, if_false, tsum_zero]
  simp_rw [split]
  simpa only [eq_comm, tsum_fintype] using tsum_ite_eq context (fun c => ∑' value : Value, distribution (c,value))

/-- The retained context can include the stopping time and passphrase. -/
theorem independent_uniform (distribution : PMF (Context × Value))
    (actions : Index → Equiv.Perm Value)
    (transitive : ∀ first second, ∃ action, actions action first = second)
    (invariant : ∀ action, distribution.map (Equiv.prodCongr (Equiv.refl Context) (actions action)) = distribution) :
    distribution = independentPair (distribution.map Prod.fst) (PMF.uniformOfFintype Value) := by
  classical
  have constant (context : Context) (first second : Value) : distribution (context,first) = distribution (context,second) := by
    obtain ⟨action, moves⟩ := transitive first second
    have transported := map_equiv_at distribution (Equiv.prodCongr (Equiv.refl Context) (actions action)) (context,first)
    rw [invariant] at transported
    simpa only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply, moves] using transported.symm
  ext pair
  rcases pair with ⟨context,value⟩
  rw [independentPair_apply, PMF.uniformOfFintype_apply]
  have total : (Fintype.card Value : ENNReal) * distribution (context,value) = (distribution.map Prod.fst) context := by
    rw [fst_mass]
    simp_rw [constant context (second := value)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have nonzero : (Fintype.card Value : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have finite : (Fintype.card Value : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have scaled := congrArg (fun x : ENNReal => (Fintype.card Value : ENNReal)⁻¹ * x) total
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel nonzero finite, one_mul, mul_comm] using scaled

end FiberSymmetry

/-! Keep the trial count and success flag while proving uniformity of the selected triple. -/
namespace WalletJointLaw
open WalletGeneration WalletFinite WalletLaws TranscriptErasure
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]

abbrev RawSeed (count : Nat) := Raw (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) count

def context {count : Nat} (q : Passphrase) (target : Check) (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) : Nat × Bool :=
  let run := execute raw.1 (loop q target (List.ofFn raw.2.1))
  (run.2.length / 2, run.1.isSome)

def joint {count : Nat} (q : Passphrase) (target : Check) (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) :
    (Nat × Bool) × Selected Entropy Seed Tail := (context q target raw, observe q target raw)

theorem natural {count : Nat} (q : Passphrase) (target : Check)
    (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail)
    (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) :
    joint q target (rawAction entropy seed tail raw) =
      (Equiv.prodCongr (Equiv.refl (Nat × Bool)) (selectedAction entropy seed tail)) (joint q target raw) := by
  have trials : List.ofFn ((trialAction entropy) raw.2.1) = (List.ofFn raw.2.1).map entropy := by
    simp only [trialAction, Equiv.coe_fn_mk, List.map_ofFn]
    rfl
  apply Prod.ext
  · change context q target (rawAction entropy seed tail raw) = context q target raw
    change (((execute (WalletSymmetry.relabel entropy seed tail raw.1)
      (loop q target (List.ofFn ((trialAction entropy) raw.2.1)))).2).length / 2,
        ((execute (WalletSymmetry.relabel entropy seed tail raw.1)
      (loop q target (List.ofFn ((trialAction entropy) raw.2.1)))).1).isSome) = _
    rw [trials, WalletSymmetry.loop_natural]
    simp only [List.length_map, Option.isSome_map]
    rfl
  · exact WalletLaws.natural q target entropy seed tail raw

variable [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Tail]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

def distribution (count : Nat) (q : Passphrase) (target : Check) :
    PMF ((Nat × Bool) × Selected Entropy Seed Tail) :=
  (PMF.uniformOfFintype (RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count)).map (joint q target)

/-- Exact independence from trial count and success flag, including at the finite cutoff. -/
theorem uniform_with_context (count : Nat) (q : Passphrase) (target : Check) : distribution (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count q target =
      ProbabilityTools.independentPair
        ((distribution (Entropy := Entropy) (Seed := Seed) (Tail := Tail) count q target).map Prod.fst)
        (PMF.uniformOfFintype (Selected Entropy Seed Tail)) := by
  let actions : (Equiv.Perm Entropy × Equiv.Perm Seed × Equiv.Perm Tail) → Equiv.Perm (Selected Entropy Seed Tail) :=
    fun action => selectedAction action.1 action.2.1 action.2.2
  apply FiberSymmetry.independent_uniform _ actions
  · intro first second
    refine ⟨(Equiv.swap first.entropy second.entropy, Equiv.swap first.seed second.seed,
      Equiv.swap first.tail second.tail), ?_⟩
    cases first with
    | mk e1 d1 t1 =>
      cases second with
      | mk e2 d2 t2 =>
        change Selected.mk (Equiv.swap e1 e2 e1) (Equiv.swap d1 d2 d1) (Equiv.swap t1 t2 t1) = _
        rw [Equiv.swap_apply_left, Equiv.swap_apply_left, Equiv.swap_apply_left]
  · intro action
    exact UniformSymmetry.equivariant_uniform (joint q target)
      (rawAction action.1 action.2.1 action.2.2)
      (Equiv.prodCongr (Equiv.refl (Nat × Bool)) (selectedAction action.1 action.2.1 action.2.2))
      (natural q target action.1 action.2.1 action.2.2)

end WalletJointLaw

/-! Exact first-success decomposition, without a distinct-trial assumption. -/
namespace RejectedTrials
open WalletGeneration TranscriptErasure
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]

def trialLog (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (e : Entropy) : List (Point Entropy Passphrase Seed) := [Point.s e q, Point.t (table (Point.s e q))]

theorem decomposition (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (target : Check) (trials : List Entropy) (chosen : Selected Entropy Seed Tail)
    (success : (execute table (loop q target trials)).1 = some chosen) :
    ∃ rejected rest : List Entropy,
      trials = rejected ++ chosen.entropy :: rest ∧
      (execute table (loop q target trials)).2 = (rejected ++ [chosen.entropy]).flatMap (trialLog table q) ∧
      ∀ e ∈ rejected, (table (Point.t (table (Point.s e q)))).1 ≠ target := by
  induction trials with
  | nil => cases success
  | cons e trials ih =>
    rw [execution_cons] at success
    dsimp only at success
    split_ifs at success with passing
    · have same := Option.some.inj success
      subst chosen
      refine ⟨[], trials, rfl, ?_, ?_⟩
      · rw [execution_cons]
        simp only [passing, if_true, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, trialLog]
      · intro value impossible
        cases impossible
    · obtain ⟨rejected, rest, shape, trace, failures⟩ := ih success
      refine ⟨e :: rejected, rest, ?_, ?_, ?_⟩
      · simpa only [List.cons_append, List.cons.injEq, true_and] using shape
      · rw [execution_cons]
        simp only [passing, if_false, trace, List.cons_append, List.flatMap_cons, trialLog]
      · intro value member
        rcases List.mem_cons.mp member with same | later
        · subst value
          exact passing
        · exact failures value later

theorem rejected_different (table : Table (spec Entropy Passphrase Seed Check Tail))
    (q : Passphrase) (target : Check) (trials : List Entropy) (chosen : Selected Entropy Seed Tail)
    (success : (execute table (loop q target trials)).1 = some chosen) (rejected : List Entropy)
    (failures : ∀ e ∈ rejected, (table (Point.t (table (Point.s e q)))).1 ≠ target) (e : Entropy)
    (member : e ∈ rejected) : e ≠ chosen.entropy ∧ table (Point.s e q) ≠ chosen.seed := by
  have values := selected_values table q target trials chosen success
  have notSeed : table (Point.s e q) ≠ chosen.seed := fun equal =>
    failures e member (by rw [equal]; exact congrArg Prod.fst values.2)
  exact ⟨fun equal => notSeed (equal ▸ values.1), notSeed⟩

end RejectedTrials

/-! Zero-based rejected indices are exactly the trials before the selected last trial. -/
namespace RejectedIndices
open WalletGeneration TranscriptErasure RejectedTrials
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]

def count (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (target : Check) (trials : List Entropy) : Nat := (execute table (loop q target trials)).2.length / 2

omit [DecidableEq Check] in
theorem log_length (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (trials : List Entropy) : (trials.flatMap (trialLog table q)).length = 2 * trials.length := by
  induction trials with
  | nil => rfl
  | cons e trials ih =>
    simp only [List.flatMap_cons, List.length_append, trialLog, List.length_cons, List.length_nil, ih]
    omega

/-- No rejected entropy or seed equals the selected one, even if rejected trials repeat. -/
theorem before_selected (table : Table (spec Entropy Passphrase Seed Check Tail)) (q : Passphrase)
    (target : Check) (trials : List Entropy) (chosen : Selected Entropy Seed Tail)
    (success : (execute table (loop q target trials)).1 = some chosen) (index : Nat)
    (earlier : index + 1 < count table q target trials) (candidate : Entropy)
    (atIndex : trials[index]? = some candidate) :
    candidate ≠ chosen.entropy ∧ table (Point.s candidate q) ≠ chosen.seed := by
  obtain ⟨rejected, rest, shape, trace, failures⟩ := decomposition table q target trials chosen success
  have length : count table q target trials = rejected.length + 1 := by
    unfold count
    rw [trace, log_length]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have within : index < rejected.length := by omega
  rw [shape, List.getElem?_append_left within] at atIndex
  have member := List.mem_of_getElem? atIndex
  exact rejected_different table q target trials chosen success rejected failures candidate member

end RejectedIndices

/-! Actual rejected entropy at a fixed index, retaining its selected triple and stopping context. -/
namespace RejectedEntropyModel
open WalletGeneration WalletFinite WalletLaws TranscriptErasure
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]
abbrev RawSeed (count : Nat) := Raw (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) count
abbrev Context := (Nat × Bool) × Selected Entropy Seed Tail

def enabled {count : Nat} (index : Fin count) (context : Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)) : Prop :=
  context.1.2 = true ∧ index.val + 1 < context.1.1
instance {count : Nat} (index : Fin count) (context : Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)) :
    Decidable (enabled index context) := inferInstanceAs (Decidable (_ ∧ _))

def observe {count : Nat} (q : Passphrase) (target : Check) (index : Fin count)
    (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) :
    Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) × Option Entropy :=
  let context := WalletJointLaw.joint q target raw
  (context, if enabled index context then some (raw.2.1 index) else none)

def contextAction (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail) :
    Equiv.Perm (Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)) :=
  Equiv.prodCongr (Equiv.refl (Nat × Bool)) (selectedAction entropy seed tail)

def outputAction (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail) :
    Equiv.Perm (Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) × Option Entropy) :=
  Equiv.prodCongr (contextAction entropy seed tail) (Equiv.optionCongr entropy)

theorem natural {count : Nat} (q : Passphrase) (target : Check) (index : Fin count)
    (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail)
    (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) :
    observe q target index (rawAction entropy seed tail raw) = outputAction entropy seed tail (observe q target index raw) := by
  unfold observe
  rw [WalletJointLaw.natural]
  change (contextAction entropy seed tail (WalletJointLaw.joint q target raw),
    if enabled index (contextAction entropy seed tail (WalletJointLaw.joint q target raw))
      then some (entropy (raw.2.1 index)) else none) = _
  have same : enabled index (contextAction entropy seed tail (WalletJointLaw.joint q target raw)) ↔
      enabled index (WalletJointLaw.joint q target raw) := Iff.rfl
  simp only [same]
  by_cases active : enabled index (WalletJointLaw.joint q target raw)
  · simp only [active, if_true]
    rfl
  · simp only [active, if_false]
    rfl

/-- The excluded entropy has exactly zero mass on successful rejected-index branches. -/
theorem different {count : Nat} (q : Passphrase) (target : Check) (index : Fin count)
    (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count)
    (active : enabled index (WalletJointLaw.joint q target raw)) :
    raw.2.1 index ≠ (WalletJointLaw.joint q target raw).2.entropy := by
  change (execute raw.1 (loop q target (List.ofFn raw.2.1))).1.isSome = true ∧
    index.val + 1 < RejectedIndices.count raw.1 q target (List.ofFn raw.2.1) at active
  cases selected : (execute raw.1 (loop q target (List.ofFn raw.2.1))).1 with
  | none => simp only [selected, Option.isSome_none, Bool.false_eq_true, false_and] at active
  | some chosen =>
    have atIndex : (List.ofFn raw.2.1)[index.val]? = some (raw.2.1 index) := by
      rw [List.getElem?_ofFn, dif_pos index.isLt]
    have differs := (RejectedIndices.before_selected raw.1 q target (List.ofFn raw.2.1)
      chosen selected index.val active.2 (raw.2.1 index) atIndex).1
    simpa only [WalletJointLaw.joint, WalletLaws.observe, selected, Option.getD_some] using differs

end RejectedEntropyModel

/-! Symmetry on the complement of the selected entropy/seed gives exact point bounds. -/
namespace SymmetricCollision
variable {Value : Type} [Fintype Value] [DecidableEq Value]

/-- No independence assumption is hidden here: a whole conditional mass fiber is compared. -/
theorem point_bound (weight : Value → ENNReal) (excluded : Value) (zero : weight excluded = 0)
    (symmetric : ∀ first second, first ≠ excluded → second ≠ excluded → weight first = weight second)
    (large : 2 ≤ Fintype.card Value) (point : Value) :
    weight point ≤ (∑ value : Value, weight value) / ((Fintype.card Value - 1 : Nat) : ENNReal) := by
  by_cases equal : point = excluded
  · rw [equal, zero]
    exact zero_le
  · have total : (∑ value : Value, weight value) = ((Fintype.card Value - 1 : Nat) : ENNReal) * weight point := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset Value) weight (Finset.mem_univ excluded), zero, add_zero]
      calc
        _ = ∑ _ ∈ (Finset.univ : Finset Value).erase excluded, weight point := by
          apply Finset.sum_congr rfl
          intro value member
          exact symmetric value point (Finset.mem_erase.mp member).1 equal
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ excluded),
            Finset.card_univ, nsmul_eq_mul]
    rw [total]
    have nonzero : ((Fintype.card Value - 1 : Nat) : ENNReal) ≠ 0 := by
      exact_mod_cast (show Fintype.card Value - 1 ≠ 0 by omega)
    have finite : ((Fintype.card Value - 1 : Nat) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel nonzero finite, one_mul]

end SymmetricCollision

/-! Integrate conditional point bounds while retaining the probability that an index exists. -/
namespace FiberHit
open GameExpectation MomentTools
variable {Context Domain : Type} [Fintype Domain]

/-- Option.none carries disabled indices; only enabled fibers are charged. -/
theorem bound (distribution : PMF (Context × Option Domain)) (enabled : Context → Prop)
    [DecidablePred enabled] (denominator : ENNReal)
    (pointBound : ∀ context point, distribution (context,some point) ≤ (∑ value : Domain, distribution (context,some value)) / denominator)
    (inactive : ∀ context, ¬ enabled context → ∀ point, distribution (context,some point) = 0)
    (matching : Context → Finset Domain) (limit : Nat)
    (size : ∀ context, (matching context).card ≤ limit) :
    (∑' context, ∑ point ∈ matching context, distribution (context,some point)) ≤
      ((limit : ENNReal) / denominator) *
        (((distribution.map Prod.fst).map (fun context => decide (enabled context))) true) := by
  have massBound (context : Context) :
      (∑ value : Domain, distribution (context,some value)) ≤ (distribution.map Prod.fst) context := by
    rw [FiberSymmetry.fst_mass]
    simp only [Fintype.sum_option]
    exact le_add_self
  have pointwise (context : Context) :
      (∑ point ∈ matching context, distribution (context,some point)) ≤
        (distribution.map Prod.fst) context * (if enabled context then ((limit : ENNReal) / denominator) else 0) := by
    by_cases active : enabled context
    · rw [if_pos active]
      calc
        _ ≤ ∑ _ ∈ matching context, ((distribution.map Prod.fst) context / denominator) := by
          apply Finset.sum_le_sum
          intro point _
          exact (pointBound context point).trans (ENNReal.div_le_div_right (massBound context) _)
        _ = (matching context).card * ((distribution.map Prod.fst) context / denominator) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (limit : ENNReal) * ((distribution.map Prod.fst) context / denominator) :=
          mul_le_mul_left (by exact_mod_cast size context) _
        _ = _ := by simp only [div_eq_mul_inv]; ac_rfl
    · simp only [inactive context active, Finset.sum_const_zero, if_neg active, mul_zero, le_refl]
  calc
    _ ≤ ∑' context, (distribution.map Prod.fst) context *
        (if enabled context then ((limit : ENNReal) / denominator) else 0) := ENNReal.tsum_le_tsum pointwise
    _ = moment (distribution.map Prod.fst) (fun context =>
        (if enabled context then (1 : ENNReal) else 0) * ((limit : ENNReal) / denominator)) := by
      congr 1
      funext context
      by_cases active : enabled context <;> simp only [active, if_true, if_false, one_mul, zero_mul]
    _ = _ := by
      rw [mul_const, probability]
      simp only [decide_eq_true_eq]
      exact mul_comm _ _

end FiberHit

/-! Rejected entropy and seed use the same stabilizer argument on the recorded context. -/
namespace RejectedFiber
open GameExpectation
variable {Raw Context Value : Type} [Fintype Raw] [Nonempty Raw] [Fintype Value] [DecidableEq Value]

/-- The observation retains the complete selected context and enables only rejected trials. -/
def observe (context : Raw → Context) (candidate : Raw → Value) (enabled : Context → Prop)
    [DecidablePred enabled] (raw : Raw) : Context × Option Value :=
  (context raw,if enabled (context raw) then some (candidate raw) else none)

/-- Uniform relabeling and the actual rejection rule give a conditional hit bound. -/
theorem matching_bound (context : Raw → Context) (candidate : Raw → Value)
    (enabled : Context → Prop) [DecidablePred enabled] (excluded : Context → Value)
    (rawAction : Equiv.Perm Value → Equiv.Perm Raw)
    (contextAction : Equiv.Perm Value → Equiv.Perm Context)
    (natural : ∀ permutation raw,observe context candidate enabled (rawAction permutation raw)=
      Equiv.prodCongr (contextAction permutation) (Equiv.optionCongr permutation)
        (observe context candidate enabled raw))
    (fixed : ∀ ctx permutation,permutation (excluded ctx)=excluded ctx → contextAction permutation ctx=ctx)
    (different : ∀ raw,enabled (context raw) → candidate raw ≠ excluded (context raw))
    (large : 2 ≤ Fintype.card Value) (matching : Context → Finset Value) (limit : Nat)
    (size : ∀ ctx,(matching ctx).card ≤ limit) :
    let law := (PMF.uniformOfFintype Raw).map (observe context candidate enabled)
    (∑' ctx,∑ point ∈ matching ctx,law (ctx,some point)) ≤
      ((limit:ENNReal)/((Fintype.card Value-1:Nat):ENNReal))*
        (((law.map Prod.fst).map (fun ctx => decide (enabled ctx))) true) := by
  classical
  let law := (PMF.uniformOfFintype Raw).map (observe context candidate enabled)
  have supported (ctx : Context) (point : Value) (positive : law (ctx,some point) ≠ 0) :
      enabled ctx ∧ point ≠ excluded ctx := by
    have member : (ctx,some point) ∈ law.support := by
      simpa only [PMF.mem_support_iff] using positive
    obtain ⟨raw,_,equal⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    change (context raw,if enabled (context raw) then some (candidate raw) else none) = (ctx,some point) at equal
    by_cases active : enabled (context raw)
    · simp only [if_pos active,Prod.mk.injEq,Option.some.injEq] at equal
      exact ⟨equal.1 ▸ active,by simpa only [equal.1,equal.2] using different raw active⟩
    · simp only [if_neg active,Prod.mk.injEq] at equal
      cases equal.2
  have excluded_zero (ctx : Context) : law (ctx,some (excluded ctx))=0 := by
    by_contra positive
    exact (supported ctx (excluded ctx) positive).2 rfl
  have inactive_zero (ctx : Context) (inactive : ¬ enabled ctx) (point : Value) : law (ctx,some point)=0 := by
    by_contra positive
    exact inactive (supported ctx point positive).1
  have invariant (permutation : Equiv.Perm Value) :
      law.map (Equiv.prodCongr (contextAction permutation) (Equiv.optionCongr permutation))=law := by
    exact UniformSymmetry.equivariant_uniform (observe context candidate enabled)
      (rawAction permutation) (Equiv.prodCongr (contextAction permutation) (Equiv.optionCongr permutation))
      (natural permutation)
  have symmetric (ctx : Context) (first second : Value)
      (firstNe : first ≠ excluded ctx) (secondNe : second ≠ excluded ctx) :
      law (ctx,some first)=law (ctx,some second) := by
    let permutation := Equiv.swap first second
    have fixes := fixed ctx permutation (Equiv.swap_apply_of_ne_of_ne firstNe.symm secondNe.symm)
    have moves : Equiv.prodCongr (contextAction permutation) (Equiv.optionCongr permutation)
        (ctx,some first) = (ctx,some second) := by
      change (contextAction permutation ctx,some (permutation first)) = _
      rw [fixes]
      simp only [permutation,Equiv.swap_apply_left]
    have transported := UniformSymmetry.map_equiv_at law
      (Equiv.prodCongr (contextAction permutation) (Equiv.optionCongr permutation)) (ctx,some first)
    rw [invariant,moves] at transported
    exact transported.symm
  exact FiberHit.bound law enabled _
    (fun ctx point => SymmetricCollision.point_bound _ (excluded ctx)
      (excluded_zero ctx) (symmetric ctx) large point) inactive_zero matching limit size

end RejectedFiber

/-! Conditional rejected-entropy fibers are uniform off the selected entropy. -/
namespace RejectedEntropyProbability
open WalletGeneration WalletFinite WalletLaws TranscriptErasure
open RejectedEntropyModel
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Tail] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Raws (count : Nat) := RawSeed (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) count
abbrev Contexts := Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)

def law {count : Nat} (q : Passphrase) (target : Check) (index : Fin count) : PMF (Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) × Option Entropy) :=
  (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count)).map
    (RejectedEntropyModel.observe q target index)

omit [DecidableEq Tail] in
theorem matching_bound {count : Nat} (q : Passphrase) (target : Check) (index : Fin count)
    (large : 2 ≤ Fintype.card Entropy)
    (matching : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) → Finset Entropy)
    (limit : Nat) (size : ∀ context, (matching context).card ≤ limit) :
    (∑' context, ∑ point ∈ matching context, (law q target index) (context,some point)) ≤
      ((limit : ENNReal) / ((Fintype.card Entropy-1 : Nat) : ENNReal)) *
        ((((law (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index).map Prod.fst).map (fun context => decide (enabled index context))) true) := by
  apply RejectedFiber.matching_bound (WalletJointLaw.joint q target)
    (fun raw => raw.2.1 index) (enabled index) (fun ctx => ctx.2.entropy)
    (fun permutation => rawAction permutation (Equiv.refl Seed) (Equiv.refl Tail)) (fun permutation => contextAction permutation (Equiv.refl Seed) (Equiv.refl Tail))
    (fun permutation raw => RejectedEntropyModel.natural q target index permutation (Equiv.refl Seed) (Equiv.refl Tail) raw)
    ?_ (RejectedEntropyModel.different q target index) large matching limit size
  intro ctx permutation fixes
  rcases ctx with ⟨⟨j,passed⟩,⟨e,d,t⟩⟩
  change ((j,passed),Selected.mk (permutation e) d t)=_
  change permutation e=e at fixes
  rw [fixes]

end RejectedEntropyProbability

/-! Actual rejected seed at a fixed index, retaining its selected triple and stopping context. -/
namespace RejectedSeedModel
open WalletGeneration WalletFinite WalletLaws TranscriptErasure
variable {Entropy Passphrase Seed Check Tail : Type} [DecidableEq Check]
abbrev RawSeed (count : Nat) := Raw (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) count
abbrev Context := (Nat × Bool) × Selected Entropy Seed Tail

def enabled {count : Nat} (index : Fin count) (context : Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)) : Prop :=
  context.1.2 = true ∧ index.val + 1 < context.1.1
instance {count : Nat} (index : Fin count) (context : Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)) :
    Decidable (enabled index context) := inferInstanceAs (Decidable (_ ∧ _))

def observe {count : Nat} (q : Passphrase) (target : Check) (index : Fin count)
    (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) :
    Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) × Option Seed :=
  let context := WalletJointLaw.joint q target raw
  (context, if enabled index context then some (raw.1 (Point.s (raw.2.1 index) q)) else none)

def contextAction (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail) :
    Equiv.Perm (Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)) :=
  Equiv.prodCongr (Equiv.refl (Nat × Bool)) (selectedAction entropy seed tail)

def outputAction (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail) :
    Equiv.Perm (Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail) × Option Seed) :=
  Equiv.prodCongr (contextAction entropy seed tail) (Equiv.optionCongr seed)

theorem natural {count : Nat} (q : Passphrase) (target : Check) (index : Fin count)
    (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail)
    (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count) :
    observe q target index (rawAction entropy seed tail raw) = outputAction entropy seed tail (observe q target index raw) := by
  unfold observe
  rw [WalletJointLaw.natural]
  change (contextAction entropy seed tail (WalletJointLaw.joint q target raw),
    if enabled index (contextAction entropy seed tail (WalletJointLaw.joint q target raw))
      then some (WalletSymmetry.relabel entropy seed tail raw.1 (Point.s (entropy (raw.2.1 index)) q)) else none) = _
  rw [WalletSymmetry.relabel_s]
  have same : enabled index (contextAction entropy seed tail (WalletJointLaw.joint q target raw)) ↔
      enabled index (WalletJointLaw.joint q target raw) := Iff.rfl
  simp only [same]
  by_cases active : enabled index (WalletJointLaw.joint q target raw)
  · simp only [active, if_true]
    rfl
  · simp only [active, if_false]
    rfl

/-- The excluded seed has exactly zero mass on successful rejected-index branches. -/
theorem different {count : Nat} (q : Passphrase) (target : Check) (index : Fin count)
    (raw : RawSeed (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count)
    (active : enabled index (WalletJointLaw.joint q target raw)) :
    raw.1 (Point.s (raw.2.1 index) q) ≠ (WalletJointLaw.joint q target raw).2.seed := by
  change (execute raw.1 (loop q target (List.ofFn raw.2.1))).1.isSome = true ∧
    index.val + 1 < RejectedIndices.count raw.1 q target (List.ofFn raw.2.1) at active
  cases selected : (execute raw.1 (loop q target (List.ofFn raw.2.1))).1 with
  | none => simp only [selected, Option.isSome_none, Bool.false_eq_true, false_and] at active
  | some chosen =>
    have atIndex : (List.ofFn raw.2.1)[index.val]? = some (raw.2.1 index) := by
      rw [List.getElem?_ofFn, dif_pos index.isLt]
    have differs := (RejectedIndices.before_selected raw.1 q target (List.ofFn raw.2.1)
      chosen selected index.val active.2 (raw.2.1 index) atIndex).2
    simpa only [WalletJointLaw.joint, WalletLaws.observe, selected, Option.getD_some] using differs

end RejectedSeedModel

/-! Conditional rejected-seed fibers are uniform off the selected seed. -/
namespace RejectedSeedProbability
open WalletGeneration WalletFinite WalletLaws TranscriptErasure
open RejectedSeedModel
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Tail] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Raws (count : Nat) := RawSeed (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) count
abbrev Contexts := Context (Entropy := Entropy) (Seed := Seed) (Tail := Tail)

def law {count : Nat} (q : Passphrase) (target : Check) (index : Fin count) : PMF (Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) × Option Seed) :=
  (PMF.uniformOfFintype (Raws (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) count)).map
    (RejectedSeedModel.observe q target index)

omit [DecidableEq Tail] in
theorem matching_bound {count : Nat} (q : Passphrase) (target : Check) (index : Fin count)
    (large : 2 ≤ Fintype.card Seed)
    (matching : Contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) → Finset Seed)
    (limit : Nat) (size : ∀ context, (matching context).card ≤ limit) :
    (∑' context, ∑ point ∈ matching context, (law q target index) (context,some point)) ≤
      ((limit : ENNReal) / ((Fintype.card Seed-1 : Nat) : ENNReal)) *
        ((((law (Entropy := Entropy) (Seed := Seed) (Tail := Tail) q target index).map Prod.fst).map (fun context => decide (enabled index context))) true) := by
  apply RejectedFiber.matching_bound (WalletJointLaw.joint q target)
    (fun raw => raw.1 (Point.s (raw.2.1 index) q)) (enabled index) (fun ctx => ctx.2.seed)
    (fun permutation => rawAction (Equiv.refl Entropy) permutation (Equiv.refl Tail)) (fun permutation => contextAction (Equiv.refl Entropy) permutation (Equiv.refl Tail))
    (fun permutation raw => RejectedSeedModel.natural q target index (Equiv.refl Entropy) permutation (Equiv.refl Tail) raw)
    ?_ (RejectedSeedModel.different q target index) large matching limit size
  intro ctx permutation fixes
  rcases ctx with ⟨⟨j,passed⟩,⟨e,d,t⟩⟩
  change ((j,passed),Selected.mk e (permutation d) t)=_
  change permutation d=d at fixes
  rw [fixes]

end RejectedSeedProbability

end
end MhfeLean
