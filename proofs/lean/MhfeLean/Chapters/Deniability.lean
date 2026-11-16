import MhfeLean.Chapters.PasswordPairs
import MhfeLean.Chapters.MatchingAttack
import MhfeLean.Chapters.WalletSource
import MhfeLean.Chapters.DeniabilityModel
import MhfeLean.Chapters.GenerationCoupling
import MhfeLean.Chapters.KnownPairEarly

namespace MhfeLean
noncomputable section

/-! # Prepared disclosure and its programmable-record simulator

The simulator sees the container and the base record oracle, but not the real
password or phrase. Conditioning only changes its initially drawn password.
The same argument permits a failure result when no different password exists.
-/

namespace PreparedDisclosure
open StatisticalClose GameExpectation MomentTools
variable {Password State Phrase Record : Type} [DecidableEq Password] [DecidableEq Phrase]

/-- A disclosure includes a record-lookup function, so every adaptive lookup is covered. -/
abbrev View (Password State Record Phrase : Type) :=
  Password × State × Record × (Phrase → Record)

/-- Programming one synthetic record leaves all other base-oracle answers intact. -/
def overlay (base : Phrase → Record) (phrase : Phrase) (record : Record) : Phrase → Record :=
  fun queried => if queried = phrase then record else base queried

/-- The real-wallet oracle is provided to the simulator; it is not derived from the container. -/
def realOracle (real : Phrase) (record empty : Record) : Phrase → Record :=
  fun queried => if queried = real then record else empty

theorem overlay_at (base : Phrase → Record) (phrase : Phrase) (record : Record) :
    overlay base phrase record phrase = record := by simp [overlay]

theorem overlay_other (base : Phrase → Record) (phrase queried : Phrase) (record : Record)
    (different : queried ≠ phrase) : overlay base phrase record queried = base queried := by
  simp [overlay, different]

/-- The prepared experiment's lookup rule, including coincident real and disclosed phrases. -/
theorem lookup_rule (real disclosed queried : Phrase) (realRecord disclosedRecord empty : Record) :
    overlay (realOracle real realRecord empty) disclosed disclosedRecord queried =
      if queried = disclosed then disclosedRecord
      else if queried = real then realRecord else empty := rfl

/-- One simulated opening uses only the supplied inverse and the synthetic usage scenario. -/
def opening (inverse : Password → State → State) (phrase : State → Phrase)
    (usage : Phrase → PMF Record) (container : State) (base : Phrase → Record)
    (disclosed : Password) : PMF (Option (View Password State Record Phrase)) :=
  let recovered := inverse disclosed container
  (usage (phrase recovered)).map fun record =>
    some (disclosed, recovered, record, overlay base (phrase recovered) record)

def simulator (passwords : PMF Password) (inverse : Password → State → State)
    (phrase : State → Phrase) (usage : Phrase → PMF Record) (container : State)
    (base : Phrase → Record) : PMF (Option (View Password State Record Phrase)) :=
  passwords.bind (opening inverse phrase usage container base)

/-- Exact conditional draw, with the source convention's common failure if its support is empty. -/
def replacement (passwords : PMF Password) (real : Password)
    (next : Password → PMF (Option (View Password State Record Phrase))) :
    PMF (Option (View Password State Record Phrase)) :=
  by
  classical
  exact if possible : ∃ candidate, candidate ≠ real ∧ candidate ∈ passwords.support then
    (passwords.filter {candidate | candidate ≠ real} possible).bind next
  else PMF.pure none

/-- Keep an allowed first draw; a rejected first draw is conditionally redrawn or fails. -/
def prepared (passwords : PMF Password) (real : Password)
    (next : Password → PMF (Option (View Password State Record Phrase))) :
    PMF (Option (View Password State Record Phrase)) :=
  passwords.bind fun candidate =>
    if candidate = real then replacement passwords real next else next candidate

omit [DecidableEq Phrase] in
/-- The kept-first implementation has exactly the conditional distribution, not an approximation. -/
theorem conditional (passwords : PMF Password) (real : Password)
    (next : Password → PMF (Option (View Password State Record Phrase)))
    (possible : ∃ candidate, candidate ≠ real ∧ candidate ∈ passwords.support) :
    prepared passwords real next =
      (passwords.filter {candidate | candidate ≠ real} possible).bind next := by
  have redraw := congrArg (fun law : PMF Password => law.bind next)
    (ConditionalRedraw.conditional passwords (fun candidate => candidate ≠ real) possible)
  try dsimp only at redraw
  rw [← redraw]
  simp only [prepared, replacement, dif_pos possible, ConditionalRedraw.trial,
    PMF.bind_bind]
  congr 1
  funext candidate
  by_cases same : candidate = real <;> simp [same]

omit [DecidableEq Phrase] in
/-- The failure case has total mass one; it is not discarded by conditioning on a valid disclosure. -/
theorem failure (passwords : PMF Password) (real : Password)
    (next : Password → PMF (Option (View Password State Record Phrase)))
    (impossible : ¬ ∃ candidate, candidate ≠ real ∧ candidate ∈ passwords.support) :
    prepared passwords real next = PMF.pure none := by
  have replacement_eq : replacement passwords real next = PMF.pure none := by
    simp only [replacement, dif_neg impossible]
  have result := PMF.bind_const passwords (PMF.pure (none : Option (View Password State Record Phrase)))
  rw [prepared]
  apply PMF.ext
  intro output
  rw [PMF.bind_apply]
  rw [← result, PMF.bind_apply]
  apply tsum_congr
  intro candidate
  by_cases same : candidate = real
  · simp only [same, if_true, replacement_eq]
  · have absent : passwords candidate = 0 := by
      by_contra nonzero
      exact impossible ⟨candidate, same, nonzero⟩
    simp only [absent, zero_mul]

omit [DecidableEq Phrase] in
/-- Changing only the rejected first draw costs at most its original probability. -/
theorem redraw_close (passwords : PMF Password) (real : Password)
    (next : Password → PMF (Option (View Password State Record Phrase))) :
    Close (passwords.bind next) (prepared passwords real next) (passwords real) := by
  have pointwise (candidate : Password) :
      Close (next candidate)
        (if candidate = real then replacement passwords real next else next candidate)
        (if candidate = real then 1 else 0) := by
    by_cases same : candidate = real
    · subst candidate
      simp only [if_true]
      intro test
      exact ⟨((next real).map test).coe_le_one true |>.trans (le_add_of_nonneg_left (zero_le)),
        ((replacement passwords real next).map test).coe_le_one true |>.trans
          (le_add_of_nonneg_left (zero_le))⟩
    · simpa only [if_neg same] using of_eq (next candidate) (next candidate) rfl
  have estimate := CloseComposition.bind passwords next
    (fun candidate => if candidate = real then replacement passwords real next else next candidate)
    (fun candidate => if candidate = real then 1 else 0) pointwise
  have mass : moment passwords (fun candidate => if candidate = real then 1 else 0) = passwords real := by
    unfold moment
    simp only [mul_ite, mul_one, mul_zero]
    exact tsum_ite_eq real (fun candidate => passwords candidate)
  simpa only [prepared, mass] using estimate

/-- The simulator is within p1 for every full-view test; it does not receive the real password. -/
theorem simulation (passwords : PMF Password) (real : Password) (inverse : Password → State → State)
    (phrase : State → Phrase) (usage : Phrase → PMF Record) (container : State)
    (base : Phrase → Record) (p1 : ENNReal) (largest : ∀ candidate, passwords candidate ≤ p1) :
    Close (simulator passwords inverse phrase usage container base)
      (prepared passwords real (opening inverse phrase usage container base)) p1 :=
  StatisticalClose.mono _ _ _ _
    (redraw_close passwords real (opening inverse phrase usage container base)) (largest real)

end PreparedDisclosure

namespace PreparedDisclosureCost
open Gamma2Model QueryCounts
variable {Password Entropy : Type}
attribute [local irreducible] finalize

/-- The supplied inverse can be the actual suite-3 recovery, with twelve A/B/H calls and no G call. -/
theorem recover (password : Password) (container : State) (tables : Tables Password Entropy) :
    let run := execute tables (finalize password 12 container (by omega))
    run.1.1 = (KnownPairModel.roundsEquiv
      (KnownPairModel.allMasks password tables.a tables.b tables.h)).symm container ∧
    run.2.countP isA = 12 ∧ run.2.countP isB = 12 ∧ run.2.countP isH = 12 ∧
      run.2.countP InverseCounts.isG = 0 :=
  ⟨CipherExecution.inverse password container tables,
    InverseCounts.counts password tables 12 (by omega) container⟩

end PreparedDisclosureCost

/-! The genuine forward oracle execution implements the same cipher as K1.
Changing a distinct password's A row leaves the full result and path unchanged.
-/
namespace ForwardCipher
open Gamma2Model TwoChainModel KnownPairModel
variable {Password Entropy : Type}

def masks (password : Password) (base : Tables Password Entropy) (fuel start : Nat)
    (bound : start+fuel≤12) : List (Half → Half) :=
  List.ofFn (fun index : Fin fuel =>
    mask password base.a base.b base.h ⟨start+index.val,by omega⟩)

/-- The list of pure round masks follows exactly the executor's increasing indices. -/
theorem masks_step (password : Password) (base : Tables Password Entropy) (fuel start : Nat)
    (bound : start+(fuel+1)≤12) :
    masks password base (fuel+1) start bound =
      mask password base.a base.b base.h ⟨start,by omega⟩ ::
        masks password base fuel (start+1) (by omega) := by
  unfold masks
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext index
  apply congrArg (mask password base.a base.b base.h)
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

attribute [local irreducible] forward

/-- Both the starting offset and the full remaining round count are preserved. -/
theorem result (password : Password) (base : Tables Password Entropy) (fuel start : Nat)
    (source : State) (bound : start+fuel≤12) :
    (execute base (forward password fuel start source bound)).1.1=
      Lemma1.encrypt (masks password base fuel start bound) source := by
  induction fuel generalizing start source with
  | zero => simp only [forward,execute_pure,masks,List.ofFn_zero,Lemma1.encrypt]
  | succ fuel ih =>
    rw [RoundBlocks.forward_step,masks_step]
    dsimp only
    rw [ih]
    rfl

/-- In particular, the honest12-round program creates exactly K1.real's ciphertext. -/
theorem twelve (password : Password) (base : Tables Password Entropy) (source : State) :
    (execute base (forward password 12 0 source (by omega))).1.1=
      cipher password base.a base.b base.h source := by
  rw [result]
  rfl

/-- The full honest path, not just its ciphertext, is independent of any other A row. -/
theorem other_row [DecidableEq Password] (focus password : Password) (different : password≠focus)
    (base : Tables Password Entropy) (row : Half → Key) (fuel start : Nat) (source : State)
    (bound : start+fuel≤12) :
    execute (RowA.filled focus base row) (forward password fuel start source bound)=
      execute base (forward password fuel start source bound) := by
  induction fuel generalizing start source with
  | zero => simp only [forward,execute_pure]
  | succ fuel ih =>
    rw [RoundBlocks.forward_step,RoundBlocks.forward_step]
    simp only [RowA.filled] at ih
    simp only [RowA.filled,if_neg different,ih]

end ForwardCipher

end
end MhfeLean
