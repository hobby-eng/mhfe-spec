import MhfeLean.Chapters.GenerationCoupling
import MhfeLean.Chapters.GenerationBound

namespace MhfeLean
noncomputable section

/-! # Hidden selection rules at fixed oracle functions

A policy sees only a finite Boolean outcome history. Its independent coins give
probabilities of continuing or selecting a previous trial. The terminal-trace
weights below are the operational product of those probabilities and independent
uniform trial probabilities. Their total mass one is almost-sure termination;
it is not an assumption about the selected entropy distribution.
-/

namespace SelectionRules
open ProbabilityTools
variable {Entropy : Type} [Fintype Entropy] [DecidableEq Entropy]

abbrev Policy := List Bool → PMF (Option Nat)

/-- The index is retained, and the chosen trial must actually pass. -/
abbrev Trace (accepted : Finset Entropy) :=
  Σ count : Nat, {data : (Fin count → Entropy) × Fin count // data.1 data.2 ∈ accepted}

def outcomes (accepted : Finset Entropy) {count : Nat} (values : Fin count → Entropy) : List Bool :=
  List.ofFn (fun index => decide (values index ∈ accepted))

/-- Each terminal path contains all preceding continue decisions and its final selection. -/
def weight (accepted : Finset Entropy) (policy : Policy) (trace : Trace accepted) : ENNReal :=
  let bits := outcomes accepted trace.2.1.1
  ((Fintype.card Entropy:ENNReal)⁻¹)^trace.1 *
    (∏ index : Fin trace.1, policy (bits.take index.val) none) *
    policy bits (some trace.2.1.2.val)

/-- Only valid stopping paths are counted. Total mass one excludes both divergence and invalid selection. -/
def law (accepted : Finset Entropy) (policy : Policy)
    (terminates : HasSum (weight accepted policy) 1) : PMF (Trace accepted) :=
  ⟨weight accepted policy,terminates⟩

def chosen (accepted : Finset Entropy) (trace : Trace accepted) : {e // e ∈ accepted} :=
  ⟨trace.2.1.1 trace.2.1.2,trace.2.2⟩

/-- A permutation inside the passing set leaves every rejected value fixed. -/
def extend (accepted : Finset Entropy) (perm : Equiv.Perm {e // e ∈ accepted}) : Equiv.Perm Entropy where
  toFun value := if member : value ∈ accepted then (perm ⟨value,member⟩).1 else value
  invFun value := if member : value ∈ accepted then (perm.symm ⟨value,member⟩).1 else value
  left_inv value := by
    by_cases member : value ∈ accepted
    · simp only [dif_pos member]
      simp only [dif_pos (perm ⟨value,member⟩).2]
      exact congrArg Subtype.val (perm.symm_apply_apply ⟨value,member⟩)
    · simp only [dif_neg member]
  right_inv value := by
    by_cases member : value ∈ accepted
    · simp only [dif_pos member]
      simp only [dif_pos (perm.symm ⟨value,member⟩).2]
      exact congrArg Subtype.val (perm.apply_symm_apply ⟨value,member⟩)
    · simp only [dif_neg member]

omit [Fintype Entropy] in
theorem extend_member (accepted : Finset Entropy) (perm : Equiv.Perm {e // e ∈ accepted})
    (value : Entropy) : extend accepted perm value ∈ accepted ↔ value ∈ accepted := by
  by_cases member : value ∈ accepted
  · change (if h : value ∈ accepted then (perm ⟨value,h⟩).val else value) ∈ accepted ↔ value ∈ accepted
    simp only [member, iff_true]
    exact (perm ⟨value,member⟩).2
  · simp [extend, member]

/-- Relabel every trial while preserving its position and the selected index. -/
def relabel (accepted : Finset Entropy) (perm : Equiv.Perm {e // e ∈ accepted}) : Equiv.Perm (Trace accepted) where
  toFun trace := ⟨trace.1,⟨(fun index => extend accepted perm (trace.2.1.1 index),trace.2.1.2),
    (extend_member accepted perm _).mpr trace.2.2⟩⟩
  invFun trace := ⟨trace.1,⟨(fun index => (extend accepted perm).symm (trace.2.1.1 index),trace.2.1.2),by
    have backward := extend_member accepted perm ((extend accepted perm).symm (trace.2.1.1 trace.2.1.2))
    rw [Equiv.apply_symm_apply] at backward
    exact backward.mp trace.2.2⟩⟩
  left_inv := by
    rintro ⟨count,⟨⟨values,index⟩,passed⟩⟩
    dsimp only
    apply congrArg (Sigma.mk count)
    apply Subtype.ext
    apply Prod.ext
    · funext position
      exact (extend accepted perm).symm_apply_apply _
    · rfl
  right_inv := by
    rintro ⟨count,⟨⟨values,index⟩,passed⟩⟩
    dsimp only
    apply congrArg (Sigma.mk count)
    apply Subtype.ext
    apply Prod.ext
    · funext position
      exact (extend accepted perm).apply_symm_apply _
    · rfl

omit [Fintype Entropy] in
/-- Port to Lean 4.35: `Equiv.coe_fn_mk` no longer matches this structure, whose proof fields are
stated in unfolded form; this is the same application law. -/
theorem relabel_apply (accepted : Finset Entropy) (perm : Equiv.Perm {e // e ∈ accepted})
    (trace : Trace accepted) :
    relabel accepted perm trace=⟨trace.1,⟨(fun index => extend accepted perm (trace.2.1.1 index),trace.2.1.2),
      (extend_member accepted perm _).mpr trace.2.2⟩⟩ := rfl

/-- The policy cannot see a relabeling that leaves all pass/fail outcomes unchanged. -/
theorem weight_relabel (accepted : Finset Entropy) (policy : Policy)
    (perm : Equiv.Perm {e // e ∈ accepted}) (trace : Trace accepted) :
    weight accepted policy (relabel accepted perm trace)=weight accepted policy trace := by
  have bits : outcomes accepted (fun index => extend accepted perm (trace.2.1.1 index))=
      outcomes accepted trace.2.1.1 := by
    simp only [outcomes]
    congr 1
    funext index
    simp only [extend_member]
  have simpaTerm := congrArg (fun history => ((Fintype.card Entropy:ENNReal)⁻¹)^trace.1 * (∏ index : Fin trace.1, policy (history.take index.val) none)*policy history (some trace.2.1.2.val)) bits
  (try simp only [weight, relabel, Equiv.coe_fn_mk] at simpaTerm ⊢)
  exact simpaTerm

theorem law_relabel (accepted : Finset Entropy) (policy : Policy)
    (terminates : HasSum (weight accepted policy) 1) (perm : Equiv.Perm {e // e ∈ accepted}) :
    (law accepted policy terminates).map (relabel accepted perm)=law accepted policy terminates := by
  ext trace
  have point := UniformSymmetry.map_equiv_at (law accepted policy terminates)
    (relabel accepted perm) ((relabel accepted perm).symm trace)
  rw [Equiv.apply_symm_apply] at point
  rw [point]
  change weight accepted policy ((relabel accepted perm).symm trace)=weight accepted policy trace
  have same := weight_relabel accepted policy perm ((relabel accepted perm).symm trace)
  rw [Equiv.apply_symm_apply] at same
  exact same.symm

omit [Fintype Entropy] in
theorem chosen_relabel (accepted : Finset Entropy) (perm : Equiv.Perm {e // e ∈ accepted})
    (trace : Trace accepted) :
    chosen accepted (relabel accepted perm trace)=perm (chosen accepted trace) := by
  apply Subtype.ext
  simp only [chosen, relabel_apply, Equiv.coe_fn_mk, extend, dif_pos trace.2.2]

/-- At fixed S,T,Q, any almost-surely terminating hidden outcome policy returns a uniform passing entropy. -/
theorem selected_uniform (accepted : Finset Entropy) (nonempty : accepted.Nonempty)
    (policy : Policy) (terminates : HasSum (weight accepted policy) 1) :
    (law accepted policy terminates).map (chosen accepted)=
      @PMF.uniformOfFintype {e // e ∈ accepted} inferInstance ⟨⟨nonempty.choose,nonempty.choose_spec⟩⟩ := by
  letI : Nonempty {e // e ∈ accepted} := ⟨⟨nonempty.choose,nonempty.choose_spec⟩⟩
  apply UniformSymmetry.uniform_of_transitive _ (fun perm : Equiv.Perm {e // e ∈ accepted} => perm)
  · intro first second
    exact ⟨Equiv.swap first second,Equiv.swap_apply_left _ _⟩
  · intro perm
    calc
      _ = ((law accepted policy terminates).map (relabel accepted perm)).map (chosen accepted) := by
        simp only [PMF.map_comp]
        congr 1
        funext trace
        exact (chosen_relabel accepted perm trace).symm
      _ = _ := by rw [law_relabel]

/-- Forgetting the membership proof gives the same law as sequential first-success completion. -/
theorem entropy_uniform (accepted : Finset Entropy) (nonempty : accepted.Nonempty) (policy : Policy)
    (terminates : HasSum (weight accepted policy) 1) :
    (law accepted policy terminates).map (fun trace => (chosen accepted trace).1)=
      PMF.uniformOfFinset accepted nonempty := by
  have selected := congrArg (fun distribution : PMF {e // e ∈ accepted} => distribution.map Subtype.val)
    (selected_uniform accepted nonempty policy terminates)
  try dsimp only at selected
  rw [PMF.map_comp] at selected
  calc
    _ = _ := selected
    _ = _ := by
      ext value
      rw [PMF.map_apply, PMF.uniformOfFinset_apply]
      by_cases member : value ∈ accepted
      · simp only [PMF.uniformOfFintype_apply, Fintype.card_coe]
        rw [if_pos member]
        have equal : (∑' x : {e // e ∈ accepted}, if value=x.val then (accepted.card:ENNReal)⁻¹ else 0)=
            (accepted.card:ENNReal)⁻¹ := by
          simpa only [Subtype.ext_iff, eq_comm] using tsum_ite_eq (⟨value,member⟩ : {e // e ∈ accepted})
            (fun _ => (accepted.card:ENNReal)⁻¹)
        exact equal
      · have different : ∀ x : {e // e ∈ accepted}, value≠x.val := by
          intro x same
          exact member (same ▸ x.2)
        simp only [different, if_false, tsum_zero, member]

/-- Pointwise kernel equality retains the complete fixed-function context in the joint distribution. -/
theorem joint {Context : Type} (prior : PMF Context) (accepted : Context → Finset Entropy)
    (nonempty : ∀ context, (accepted context).Nonempty) (policy : Context → Policy)
    (terminates : ∀ context, HasSum (weight (accepted context) (policy context)) 1) :
    (prior.bind fun context => ((law (accepted context) (policy context) (terminates context)).map
      (fun trace => (context,(chosen (accepted context) trace).1)))) =
    (prior.bind fun context => (PMF.uniformOfFinset (accepted context) (nonempty context)).map (fun e => (context,e))) := by
  apply congrArg (PMF.bind prior)
  funext context
  calc
    _ = ((law (accepted context) (policy context) (terminates context)).map
        (fun trace => (chosen (accepted context) trace).1)).map (fun e => (context,e)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [entropy_uniform]

end SelectionRules

namespace WalletSelection
open SelectionRules WalletGeneration TranscriptErasure
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

abbrev Tables := Table (WalletGeneration.spec Entropy Passphrase Seed Check Tail)

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

/-- The hidden search only reads its fixed tables; the empty-set branch uses the same arbitrary fallback. -/
def chosenLaw (q : Passphrase) (target : Check)
    (table : WalletTables)
    (policy : Policy)
    (terminates : (WalletCompletion.passing table q target).Nonempty →
      HasSum (weight (WalletCompletion.passing table q target) policy) 1) :
    PMF (Selected Entropy Seed Tail) :=
  if existsPassing : (WalletCompletion.passing table q target).Nonempty then
    (law (WalletCompletion.passing table q target) policy (terminates existsPassing)).map
      (fun trace => WalletCompletion.make table q
        (chosen (WalletCompletion.passing table q target) trace).val)
  else PMF.uniformOfFintype (Selected Entropy Seed Tail)

omit [DecidableEq Passphrase] [DecidableEq Seed] [Fintype Passphrase] [Fintype Check] [Nonempty Check] in
/-- This is equality with the exact fixed-table sequential completion used by Theorem5. -/
theorem chosen_eq (q : Passphrase) (target : Check)
    (table : WalletTables)
    (policy : Policy)
    (terminates : (WalletCompletion.passing table q target).Nonempty →
      HasSum (weight (WalletCompletion.passing table q target) policy) 1) :
    chosenLaw q target table policy terminates=WalletCompletion.real table q target := by
  unfold chosenLaw WalletCompletion.real
  split_ifs with nonempty
  · have equal := congrArg (fun distribution : PMF Entropy => distribution.map (WalletCompletion.make table q))
      (entropy_uniform (WalletCompletion.passing table q target) nonempty policy (terminates nonempty))
    simpa only [PMF.map_comp, Function.comp_def] using equal
  · rfl

/-- Owner trial count, timing and trial values are not supplied to the adversary. -/
def actual (q : Passphrase) (target : Check)
    (policy : WalletTables → Policy)
    (terminates : ∀ table, (WalletCompletion.passing table q target).Nonempty →
      HasSum (weight (WalletCompletion.passing table q target) (policy table)) 1)
    (adversary : WalletExperiments.Adversary (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)) :
    PMF (WalletUnbounded.View (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Tail := Tail) (Result := Result)) :=
  (PMF.uniformOfFintype (WalletTables)).bind
    fun table => (chosenLaw q target table (policy table) (terminates table)).map
      (fun selected => (selected,execute table (adversary selected)))

/-- Full selected triple and adversary transcript law agree, retaining all oracle tables through execution. -/
theorem actual_eq (q : Passphrase) (target : Check)
    (policy : WalletTables → Policy)
    (terminates : ∀ table, (WalletCompletion.passing table q target).Nonempty →
      HasSum (weight (WalletCompletion.passing table q target) (policy table)) 1)
    (adversary : WalletExperiments.Adversary (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Result := Result)) :
    actual q target policy terminates adversary=WalletUnbounded.real q target adversary := by
  unfold actual
  simp_rw [chosen_eq]
  rfl

end WalletSelection

end
end MhfeLean
