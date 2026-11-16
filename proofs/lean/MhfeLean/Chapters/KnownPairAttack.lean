-- long: The executable eleven-round attack and its source-law probability proof form one argument.
import Mathlib.Logic.Equiv.Fin.Rotate
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.Deniability
import MhfeLean.Chapters.KnownPairEarly
import MhfeLean.Chapters.KnownPairResampling
import MhfeLean.Chapters.MatchingAttack
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.Probability
import MhfeLean.Chapters.ShortSources
import MhfeLean.Chapters.WalletMatching

namespace MhfeLean
noncomputable section

/-! # Proposition K5: matching search with a known source and container

The false-pass bound uses the actual cipher and allows repeated salts.
-/

/-! The honest path has one H point at index1, even when A salts or keys repeat. -/
namespace K5Reference
open Gamma2Model TwoChainModel
variable {Password Entropy : Type}

def selectKey (round : Fin 12) : Point Password Entropy → Option Key
  | .h key index _ => if index=round then some key else none
  | _ => none

/-- Count only H queries with the specified round, retaining their actual keys. -/
def keys (round : Fin 12) (trace : List (Point Password Entropy)) : List Key :=
  trace.filterMap (selectKey round)

theorem length_keys (round : Fin 12) (trace : List (Point Password Entropy)) :
    (keys round trace).length=trace.countP (QueryCounts.hFor round) := by
  induction trace with
  | nil => rfl
  | cons input rest ih =>
    cases input with
    | a password salt => simpa only [keys,List.filterMap_cons,selectKey,List.length_cons,
        QueryCounts.hFor,List.countP_cons,Bool.false_eq_true,ite_false,add_zero] using ih
    | b index right => simpa only [keys,List.filterMap_cons,selectKey,List.length_cons,
        QueryCounts.hFor,List.countP_cons,Bool.false_eq_true,ite_false,add_zero] using ih
    | g entropy => simpa only [keys,List.filterMap_cons,selectKey,List.length_cons,
        QueryCounts.hFor,List.countP_cons,Bool.false_eq_true,ite_false,add_zero] using ih
    | h key index right =>
      simp only [keys] at ih
      by_cases same : index=round
      · simpa [keys,selectKey,QueryCounts.hFor,same] using congrArg Nat.succ ih
      · simpa [keys,selectKey,QueryCounts.hFor,same] using ih

/-- A list of length1 has just one possible member; no uniqueness of keys across rounds is needed. -/
theorem member_singleton (trace : List Key) (one : trace.length=1) (key : Key) (member : key∈trace) :
    key=trace.headD 0 := by
  cases trace with
  | nil => simp at one
  | cons first rest =>
    cases rest with
    | nil => simpa using member
    | cons next rest =>
      simp only [List.length_cons] at one
      omega

def target (reference : Password) (base : Tables Password Entropy) (source : State) : Key :=
  (keys 1 (execute base (forward reference 12 0 source (by omega))).2).headD 0

/-- Every genuine H1 query uses this one target key; the right-half value is irrelevant here. -/
theorem key_of_member (reference : Password) (base : Tables Password Entropy) (source : State)
    (key : Key) (right : Half)
    (member : Point.h key 1 right ∈ (execute base (forward reference 12 0 source (by omega))).2) :
    key=target reference base source := by
  apply member_singleton
  · rw [length_keys]
    exact ForwardMetadata.h_count reference base source 1
  · apply List.mem_filterMap.mpr
    exact ⟨Point.h key 1 right,member,by simp only [selectKey,if_true]⟩

/-- After fixing the other rows, the target and the genuine ciphertext do not depend on the focused row. -/
theorem other_row [DecidableEq Password] (focus reference : Password) (different : reference≠focus)
    (base : Tables Password Entropy) (row : Half → Key) (source : State) :
    target reference (RowA.filled focus base row) source=target reference base source := by
  unfold target
  rw [ForwardCipher.other_row focus reference different]

end K5Reference

/-! Arbitrary round permutations reuse the existing query language and executor.
The older RoundFlip interface is retained unchanged as accepted evidence; this
extension supplies non-involutive relabellings, notably rounds10..0 to11..1.
-/
namespace RoundRelabel
open Gamma2Model TableFactors
variable {Password Entropy Result : Type}

def point (permutation : Equiv.Perm (Fin 12)) : Point Password Entropy → Point Password Entropy
  | .a password salt => .a password salt
  | .b round right => .b (permutation round) right
  | .h key round right => .h key (permutation round) right
  | .g entropy => .g entropy

variable (permutation : Equiv.Perm (Fin 12)) (base : Tables Password Entropy)

def tables : Tables Password Entropy :=
  ⟨base.a, (fun input => base.b (permutation input.1,input.2)),
    (fun input => base.h (input.1,permutation input.2.1,input.2.2)),base.g⟩

/-- A relabelled query sees exactly the same answer width. -/
def query (permutation : Equiv.Perm (Fin 12)) (input : Point Password Entropy) :
    OracleComp (spec Password Entropy) (spec Password Entropy input) :=
  match input with
  | .a password salt => ask (.a password salt)
  | .b round right => ask (.b (permutation round) right)
  | .h key round right => ask (.h key (permutation round) right)
  | .g entropy => ask (.g entropy)

def program (permutation : Equiv.Perm (Fin 12))
    (original : OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Password Entropy) Result :=
  OracleComp.construct pure (fun input _ recurse => query permutation input >>= recurse) original

/-- Every repeated query is retained; no table is exposed to the translated program. -/
theorem execution (original : OracleComp (spec Password Entropy) Result) :
    execute base (program permutation original)=
      ((execute (tables permutation base) original).1,
        (execute (tables permutation base) original).2.map (point permutation)) := by
  have resolve (input : Point Password Entropy) :
      execute base (query permutation input)=
        (answer (tables permutation base) input,[point permutation input]) := by
    cases input <;> rfl
  induction original using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
    change execute base (query permutation input >>= fun value => program permutation (next value)) =
      ((execute (tables permutation base) (ask input >>= next)).1,
        (execute (tables permutation base) (ask input >>= next)).2.map (point permutation))
    simp only [execute_bind,resolve,ih,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,List.singleton_append,List.map_cons]

/-- Inverse round permutations restore every full oracle table. -/
theorem inverse_tables : tables permutation.symm (tables permutation base)=base := by
  cases base
  simp only [tables,Equiv.apply_symm_apply]

/-- Inverse round permutations also restore each typed query identity. -/
theorem inverse_point (permutation : Equiv.Perm (Fin 12)) (input : Point Password Entropy) :
    point permutation.symm (point permutation input)=input := by
  cases input <;> simp only [point,Equiv.symm_apply_apply]

/-- The relabelling is bijective, so a uniform complete table stays uniform. -/
def tableEquiv (permutation : Equiv.Perm (Fin 12)) : Tables Password Entropy ≃ Tables Password Entropy where
  toFun := tables permutation
  invFun := tables permutation.symm
  left_inv := inverse_tables permutation
  right_inv := by have simpaTerm := inverse_tables (Password := Password) (Entropy := Entropy) permutation.symm
                  (try simp only [Equiv.symm_symm] at simpaTerm ⊢)
                  exact simpaTerm

noncomputable section
variable [Fintype Password] [DecidableEq Password] [Fintype Entropy] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype
local instance : Fintype (Tables Password Entropy) :=
  Fintype.ofEquiv (Quad Password Entropy) TableFactors.tableEquiv.symm
local instance : Nonempty (Tables Password Entropy) := ⟨TableFactors.tableEquiv.symm default⟩

theorem sampling (permutation : Equiv.Perm (Fin 12)) : (sampleTables (Password := Password) (Entropy := Entropy)).map (tables permutation)=sampleTables := by
  rw [sample_uniform]
  exact PMF.uniformOfFintype_map_of_bijective (tableEquiv permutation) (tableEquiv permutation).bijective
end

end RoundRelabel

/-! The eleven-round known-pair inverse stops just before H1, reusing FinalCut.
Only round labels change; the inverse computation and repeated queries are retained.
-/
namespace K5Cut
open Gamma2Model
variable {Password Entropy : Type}

abbrev rotation : Equiv.Perm (Fin 12) := finRotate 12

/-- Move the private log to the actual indices11..1. -/
def shifted (cut : FinalCut.Cut Password Entropy) : FinalCut.Cut Password Entropy :=
  { cut with before := cut.before.map (RoundRelabel.point rotation) }

/-- The prepared state is W2; the final pending query is H(K1,1,R1). -/
def prepare (password : Password) (container : State) :
    OracleComp (spec Password Entropy) (FinalCut.Cut Password Entropy) :=
  shifted <$> RoundRelabel.program rotation
    (FinalCut.prepare password 10 container (by omega))

def terminal (cut : FinalCut.Cut Password Entropy) : Point Password Entropy :=
  .h cut.key 1 cut.state.1

def finish (base : Tables Password Entropy) (cut : FinalCut.Cut Password Entropy) : State :=
  (cut.state.2 ^^^ base.h (cut.key,1,cut.state.1),cut.state.1)

/-- The actual backward computation11..1, including its final mask. -/
def inverse (password : Password) (container : State) : OracleComp (spec Password Entropy) State := do
  let cut ← prepare password container
  let mask : Half ← ask (terminal cut)
  pure (cut.state.2 ^^^ mask,cut.state.1)

attribute [local irreducible] FinalCut.prepare finalize

/-- The cyclic relabelling maps each of the eleven used indices to its successor. -/
theorem rotated_index (index : Fin 11) : rotation index.castSucc=index.succ := by
  exact finRotate_of_lt index.isLt

variable (password : Password) (base : Tables Password Entropy) (container : State)

/-- Both the returned private log and emitted log use the same original query identities. -/
theorem execution :
    execute base (prepare password container)=
      let cut := (execute (RoundRelabel.tables rotation base)
        (FinalCut.prepare password 10 container (by omega))).1
      (shifted cut,(shifted cut).before) := by
  simp only [prepare,execute_map,RoundRelabel.execution,FinalCut.trace,shifted]

/-- No prefix query has H index1, including queries with other keys or right halves. -/
theorem terminal_absent (key : Key) (right : Half) :
    Point.h key 1 right ∉ (execute base (prepare password container)).2 := by
  rw [execution]
  dsimp only [shifted]
  intro member
  obtain ⟨input,queried,equal⟩ := List.mem_map.mp member
  have lifted : RoundRelabel.point rotation (Point.h key 0 right : Point Password Entropy)=
      Point.h key 1 right := by
    simp only [RoundRelabel.point,rotation,finRotate_apply_zero]
  have same : input=Point.h key 0 right := by
    apply (Function.LeftInverse.injective (RoundRelabel.inverse_point rotation))
    exact equal.trans lifted.symm
  exact FinalCut.terminal_absent password
    (RoundRelabel.tables rotation base) 10 (by omega) container key right (same ▸ queried)

/-- Completing the translated cut produces exactly the partial inverse of the shifted cipher. -/
theorem completed :
    (execute base (inverse password container)).1=
      (execute (RoundRelabel.tables rotation base)
        (finalize password 11 container (by omega))).1.1 := by
  rw [FinalCut.finalized password (RoundRelabel.tables rotation base) 10 (by omega)]
  simp only [inverse,execute_bind,execution,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,terminal,
    FinalCut.finish,shifted,RoundRelabel.tables,rotation,finRotate_apply_zero]

/-- The terminal key really came from an A query in this same prefix, even with salt repeats. -/
theorem key_queried :
    ∃ salt, Point.a password salt ∈ (execute base (prepare password container)).2 ∧
      base.a (password,salt)=(execute base (prepare password container)).1.key := by
  rw [execution]
  obtain ⟨salt,member,equal⟩ := CutKeyFacts.key_queried password
    (RoundRelabel.tables rotation base) 10 (by omega) container
  refine ⟨salt,?_,equal⟩
  dsimp only [shifted]
  apply List.mem_map.mpr
  exact ⟨Point.a password salt,by simpa only [FinalCut.trace] using member,rfl⟩

/-- Exactly eleven A calls are made before H1; no fresh-terminal-key premise is needed. -/
theorem count [DecidableEq Password] (password : Password) (base : Tables Password Entropy)
    (container : State) :
    (execute base (prepare password container)).2.countP (QueryCounts.aFor password)=11 := by
  have unchanged (input : Point Password Entropy) :
      QueryCounts.aFor password (RoundRelabel.point rotation input)=
        QueryCounts.aFor password input := by
    cases input <;> rfl
  rw [execution]
  dsimp only [shifted]
  rw [List.countP_map]
  simp only [Function.comp_def,unchanged]
  have count := CutKeyFacts.count password (RoundRelabel.tables rotation base) 10 (by omega) container
  simpa only [FinalCut.trace] using count

end K5Cut

/-! A focused terminal key can hit the honest H1 key only through one of11
actual A calls. Repeated salts never require conditional terminal-key freshness.
-/
namespace K5KeyCollision
open Gamma2Model TwoChainModel GameExpectation
variable {Password Entropy : Type} [DecidableEq Password]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] forward K5Cut.prepare

def event (focus reference : Password) (source : State) (base : Tables Password Entropy) : Bool :=
  decide ((execute base (K5Cut.prepare focus
    (execute base (forward reference 12 0 source (by omega))).1.1)).1.key=
      K5Reference.target reference base source)

/-- The full genuine path is independent of the focused row, so its sole H1 key is fixed first. -/
theorem covered (focus reference : Password) (different : reference≠focus)
    (base : Tables Password Entropy) (row : Half → Key) (source : State)
    (same : event focus reference source (RowA.filled focus base row)=true) :
    RowQueryBound.event focus (K5Reference.target reference base source)
      (K5Cut.prepare focus (execute base (forward reference 12 0 source (by omega))).1.1)
      (RowA.filled focus base row)=true := by
  simp only [event,decide_eq_true_eq] at same
  rw [ForwardCipher.other_row focus reference different,
    K5Reference.other_row focus reference different] at same
  obtain ⟨salt,member,equal⟩ := K5Cut.key_queried focus (RowA.filled focus base row)
    (execute base (forward reference 12 0 source (by omega))).1.1
  unfold RowQueryBound.event
  rw [decide_eq_true_eq]
  refine ⟨salt,List.mem_filterMap.mpr ⟨Point.a focus salt,member,?_⟩,equal.trans same⟩
  exact if_pos rfl

/-- Eleven adaptive row queries suffice for the bound, even if some points repeat. -/
theorem row_probability (focus reference : Password) (different : reference≠focus)
    (base : Tables Password Entropy) (source : State) :
    moment (PMF.uniformOfFintype (Half → Key))
      (fun row => if event focus reference source (RowA.filled focus base row) then 1 else 0)≤
      (11:ENNReal)/(2^256:ENNReal) := by
  let target := K5Reference.target reference base source
  let original := K5Cut.prepare (Entropy := Entropy) focus
    (execute base (forward reference 12 0 source (by omega))).1.1
  calc
    _≤moment (PMF.uniformOfFintype (Half → Key)) (fun row =>
        if RowQueryBound.event focus target original (RowA.filled focus base row) then 1 else 0) := by
      apply MomentTools.mono
      intro row
      by_cases same : event focus reference source (RowA.filled focus base row)=true
      · have hit := covered focus reference different base row source same
        change RowQueryBound.event focus target original _=true at hit
        simp only [same,hit,ite_true,le_refl]
      · rw [if_neg same]
        exact zero_le
    _≤_ := RowQueryBound.probability focus base original target 11 (by
      intro row
      exact (K5Cut.count focus (RowA.filled focus base row) _).le)

variable [Fintype Password] [Fintype Entropy] [DecidableEq Entropy]

/-- The row-last factorization is derived from the same original four-table source law. -/
theorem probability (focus reference : Password) (different : reference≠focus) (source : State) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun base => if event focus reference source base then 1 else 0)≤(11:ENNReal)/(2^256:ENNReal) := by
  apply RowSampling.probability focus
  intro others
  exact row_probability focus reference different _ source

end K5KeyCollision

/-! Analysis-only observer: evaluate the genuine path, then stop the tested
inverse before H1. The guard excludes earlier genuine-path H1 collisions.
The actual attack does not receive the genuine password or the hidden path.
-/
namespace K5Mask
open Gamma2Model TwoChainModel GameExpectation
open G3Fresh G3Programs OracleProjection
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype
abbrev HInput := Key × Fin 12 × Half

def selection (source : State) (path : List (Point Password Entropy))
    (cut : FinalCut.Cut Password Entropy) : HInput × Option Half :=
  ((cut.key,1,cut.state.1),
    if K5Cut.terminal cut ∉ path then some (source.2 ^^^ cut.state.2) else none)

def program (focus reference : Password) (source : State) :
    OracleComp (spec Password Entropy) (HInput × Option Half) := do
  let real ← forward reference 12 0 source (by omega)
  let cut ← K5Cut.prepare focus real.1
  pure (selection source real.2 cut)

def matching (target : Half) : Finset Half := {target}

attribute [local irreducible] forward K5Cut.prepare

variable (focus reference : Password) (source : State) (base : Tables Password Entropy)

/-- The observer exposes no query after the selected terminal point. -/
theorem execution :
    execute base (program focus reference source)=
      let real := (execute base (forward reference 12 0 source (by omega))).1
      let cut := execute base (K5Cut.prepare focus real.1)
      (selection source real.2 cut.1,real.2++cut.2) := by
  simp only [program,execute_bind,execute_pure,forward_trace,List.append_nil]

/-- Enabled selection is operationally fresh in the complete two-path transcript. -/
theorem certificate (enabled : (execute base (program focus reference source)).1.2≠none) :
    embedH (execute base (program focus reference source)).1.1 ∉
      (execute base (program focus reference source)).2 := by
  rw [execution] at enabled ⊢
  let real := (execute base (forward reference 12 0 source (by omega))).1
  let cut := execute base (K5Cut.prepare focus real.1)
  change (selection source real.2 cut.1).2≠none at enabled
  have absent : K5Cut.terminal cut.1 ∉ real.2 := by
    by_contra present
    exact enabled (by simp only [selection,if_neg (not_not.mpr present)])
  change K5Cut.terminal cut.1 ∉ real.2++cut.2
  exact fun member => (List.mem_append.mp member).elim absent
    (K5Cut.terminal_absent focus base real.1 cut.1.key cut.1.state.1)

def focused (focus reference : Password) (source : State) (others : OthersH Password Entropy) :=
  FocusedExecution.focused (focusH others.1 others.2.1 others.2.2)
    (program focus reference source)

/-- The typed certificate supplies freshness to the existing uniform H-table checker. -/
theorem fresh (focus reference : Password) (source : State) (others : OthersH Password Entropy) :
    OptionalFresh.EnabledFresh (focused focus reference source others) := by
  apply EnabledProjection.enabled_fresh (focusH others.1 others.2.1 others.2.2)
    (fun h => (⟨others.1,others.2.1,h,others.2.2⟩ : Tables Password Entropy))
    (by intro table input; cases input <;> rfl) (program focus reference source)
    embedH (identifiesH others)
  intro table
  exact certificate focus reference source _

/-- For a fixed cut, at most one mask produces the known right half of X. -/
theorem size (context : Option Half) : (OptionalFresh.optionalSet matching context).card≤1 := by
  cases context <;> simp [OptionalFresh.optionalSet,matching]

def event : Bool :=
  OptionalFresh.rawHit (focused focus reference source (base.a,base.b,base.g)) matching base.h

variable [Fintype Password] [Fintype Entropy]

/-- Unconditional bound: the event includes the freshness guard, never conditions on it. -/
theorem probability (focus reference : Password) (source : State) : moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun base => if event focus reference source base then 1 else 0)≤1/(2^128:ENNReal) := by
  have estimate := G3Probability.averaged sampleTables
    (PMF.uniformOfFintype (G3Programs.OthersH Password Entropy))
    (fun others h => (⟨others.1,others.2.1,h,others.2.2⟩ : Tables Password Entropy))
    TableFactors.factor_h (focused focus reference source) matching
    (event focus reference source) (by intro others table; rfl)
    (fresh focus reference source) (fun _ => 1) (by intro others table; exact size _)
  simpa only [G3Probability.card_bits,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,
    MomentTools.constant] using estimate

end K5Mask

/-! Relate the fresh-mask observer to the actual known-half acceptance predicate. -/
namespace K5MaskActual
open Gamma2Model TwoChainModel
open OptionalFresh
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] forward K5Cut.prepare

/-- The guarded event is exactly acceptance after completing the actual pending H1 query. -/
theorem actual (focus reference : Password) (source : State) (base : Tables Password Entropy) :
    K5Mask.event focus reference source base=
      let real := (execute base (forward reference 12 0 source (by omega))).1
      let cut := (execute base (K5Cut.prepare focus real.1)).1
      decide (K5Cut.terminal cut ∉ real.2 ∧
        (K5Cut.finish base cut).1=source.2) := by
  unfold K5Mask.event rawHit K5Mask.focused
  rw [FocusedExecution.result_eq
    (OracleProjection.focusH base.a base.b base.g) base.h base
    (by intro input; cases input <;> rfl) (K5Mask.program focus reference source)]
  rw [K5Mask.execution]
  dsimp only
  generalize (execute base (forward reference 12 0 source (by omega))).1=real
  generalize (execute base (K5Cut.prepare focus real.1)).1=cut
  by_cases fresh : K5Cut.terminal cut ∉ real.2
  · simp only [K5Mask.selection,if_pos fresh,optionalSet,K5Mask.matching,
      Finset.mem_singleton]
    rw [decide_eq_decide]
    simp only [K5Cut.finish]
    constructor
    · intro same
      exact ⟨fresh,(PairMaskBound.xor_criterion _ _ _).mp same⟩
    · intro both
      exact (PairMaskBound.xor_criterion _ _ _).mpr both.2
  · simp [K5Mask.selection,fresh,optionalSet]

end K5MaskActual

/-! The partial inverse in K5 recovers W1, whose left half is the known R0. -/
namespace K5Cipher
open Gamma2Model KnownPairModel
variable {Password Entropy : Type}

/-- The rotated eleven-round mask list is exactly the original suffix1..11. -/
theorem mask_partition (password : Password) (base : Tables Password Entropy) :
    allMasks password base.a base.b base.h =
      mask password base.a base.b base.h 0 ::
        CipherExecution.prefixMasks password
          (RoundRelabel.tables K5Cut.rotation base) 11 (by omega) := by
  unfold allMasks CipherExecution.prefixMasks
  rw [List.ofFn_succ]
  congr 1

/-- Completing H1 agrees with decrypting precisely the original suffix, not all twelve rounds. -/
theorem inverse (password : Password) (base : Tables Password Entropy) (container : State) :
    (execute base (K5Cut.inverse password container)).1=
      Lemma1.decrypt
        (CipherExecution.prefixMasks password
          (RoundRelabel.tables K5Cut.rotation base) 11 (by omega)) container := by
  rw [K5Cut.completed,CipherExecution.finalize_decrypt]

/-- For the actual cipher output, backward rounds11..1 return exactly the state after round0. -/
theorem true_state (password : Password) (base : Tables Password Entropy) (source : State) :
    (execute base (K5Cut.inverse password
      (cipher password base.a base.b base.h source))).1=
        Lemma1.forwardRound (mask password base.a base.b base.h 0) source := by
  rw [inverse]
  unfold cipher
  rw [mask_partition]
  change Lemma1.decrypt _ (Lemma1.encrypt _
    (Lemma1.forwardRound _ source))=_
  exact Lemma1.decrypt_encrypt _ _

/-- The real password always satisfies the proposed 128-bit half-state filter. -/
theorem true_accepts (password : Password) (base : Tables Password Entropy) (source : State) :
    (execute base (K5Cut.inverse password
      (cipher password base.a base.b base.h source))).1.1=source.2 := by
  rw [true_state]
  rfl

end K5Cipher

/-! Pairwise wrong-password acceptance in the original known-pair source law.
The two summands use independent valid integration orders, not conditional bounds.
-/
namespace K5FalsePass
open Gamma2Model TwoChainModel GameExpectation
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]
attribute [local irreducible] forward K5Cut.prepare

omit [DecidableEq Password] [DecidableEq Entropy] in
/-- The actual inverse program completes the pending mask in the prepared cut. -/
theorem completed (focus : Password) (base : Tables Password Entropy) (container : State) :
    (execute base (K5Cut.inverse focus container)).1=
      K5Cut.finish base (execute base (K5Cut.prepare focus container)).1 := by
  simp only [K5Cut.inverse,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,
    K5Cut.finish,K5Cut.terminal,answer]

def event (focus reference : Password) (source : State) (base : Tables Password Entropy) : Bool :=
  decide ((execute base (K5Cut.inverse focus
    (KnownPairModel.cipher reference base.a base.b base.h source))).1.1=source.2)

/-- Either the selected H1 is fresh or its key equals the sole genuine H1 key. -/
theorem covered (focus reference : Password) (source : State) (base : Tables Password Entropy)
    (accepted : event focus reference source base=true) :
    K5KeyCollision.event focus reference source base=true ∨
      K5Mask.event focus reference source base=true := by
  let real := (execute base (forward reference 12 0 source (by omega))).1
  let cut := (execute base (K5Cut.prepare focus real.1)).1
  have half_equal : (K5Cut.finish base cut).1=source.2 := by
    simp only [event,decide_eq_true_eq] at accepted
    rw [← ForwardCipher.twelve reference base source,completed] at accepted
    exact accepted
  by_cases absent : K5Cut.terminal cut ∉ real.2
  · apply Or.inr
    rw [K5MaskActual.actual]
    exact decide_eq_true (And.intro absent half_equal)
  · apply Or.inl
    have member : Point.h cut.key 1 cut.state.1 ∈
        (execute base (forward reference 12 0 source (by omega))).2 := by
      rw [forward_trace]
      exact not_not.mp absent
    have equal := K5Reference.key_of_member reference base source cut.key cut.state.1 member
    exact decide_eq_true equal

variable [Fintype Password] [Fintype Entropy]

/-- Stronger pairwise estimate; no previous tests or absent-collision event is conditioned on. -/
theorem probability (focus reference : Password) (different : reference≠focus) (source : State) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun base => if event focus reference source base then 1 else 0)≤
      1/(2^128:ENNReal)+(11:ENNReal)/(2^256:ENNReal) := by
  calc
    _≤moment sampleTables (fun base =>
        (if K5Mask.event focus reference source base then 1 else 0)+
        (if K5KeyCollision.event focus reference source base then 1 else 0)) := by
      refine MomentTools.mono _ _ _ fun base => ?_
      by_cases accepted : event focus reference source base=true
      · rcases covered focus reference source base accepted with hit | hit <;> simp [accepted, hit]
      · simp [accepted]
    _=_ := MomentTools.add _ _ _
    _≤_ := add_le_add (K5Mask.probability focus reference source)
      (K5KeyCollision.probability focus reference different source)

end K5FalsePass

/-! Share only the initial B11 query across the K5 password tests.
The fixed twelve-round SharedInverse helper is retained unchanged as accepted
G8 evidence; this shorter prefix uses the same executor with fuel10.
-/
namespace K5Shared
open Gamma2Model QueryCounts
variable {Password Entropy : Type}
attribute [local irreducible] finalize

/-- Logical rounds10..0, with only the initial B10 answer supplied by the caller. -/
def raw (password : Password) (container : State) (firstSalt : Half) :
    OracleComp (spec Password Entropy) State := do
  let key : Key ← ask (.a password firstSalt)
  let mask : Half ← ask (.h key 10 container.1)
  let rest ← finalize password 10 (container.2 ^^^ mask,container.1) (by omega)
  pure rest.1

/-- The supplied first salt replaces exactly the first query, retaining every other query. -/
theorem raw_execution (password : Password) (base : Tables Password Entropy) (container : State) :
    execute base (raw password container (base.b (10,container.1)))=
      let full := execute base (finalize password 11 container (by omega))
      (full.1.1,full.2.tail) := by
  rw [FinalCut.finalize_step password base 10 (by omega) container]
  simp only [raw,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,List.append_nil,
    List.cons_append,List.nil_append,List.tail_cons]
  rfl

/-- Per logical candidate:11A,10B,11H and no G, including repeat lookups. -/
theorem raw_counts (password : Password) (base : Tables Password Entropy) (container : State) (firstSalt : Half) :
    let queries := (execute base (raw password container firstSalt)).2
    queries.countP isA=11 ∧ queries.countP isB=10 ∧ queries.countP isH=11 ∧
      queries.countP InverseCounts.isG=0 := by
  simp only [raw,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,List.append_nil,List.singleton_append]
  simp only [List.countP_cons,isA,isB,isH,InverseCounts.isG,
    Bool.false_eq_true,ite_true,ite_false,add_zero]
  have rest := InverseCounts.counts password base 10 (by omega)
    (container.2 ^^^ base.h (base.a (password,firstSalt),10,container.1),container.1)
  omega

/-- The executable candidate computation uses actual indices11..1. -/
def recover (password : Password) (container : State) (firstSalt : Half) :
    OracleComp (spec Password Entropy) State :=
  RoundRelabel.program K5Cut.rotation (raw password container firstSalt)

/-- Correct shared B11 input yields exactly the eleven-round K5 inverse result. -/
theorem result (password : Password) (base : Tables Password Entropy) (container : State) :
    (execute base (recover password container (base.b (11,container.1)))).1=
      (execute base (K5Cut.inverse password container)).1 := by
  rw [recover,RoundRelabel.execution,K5Cut.completed]
  have first : (RoundRelabel.tables K5Cut.rotation base).b (10,container.1)=
      base.b (11,container.1) := rfl
  rw [← first,raw_execution]

/-- Relabelling changes no query family, so these are actual original-oracle costs. -/
theorem counts (password : Password) (base : Tables Password Entropy) (container : State) (firstSalt : Half) :
    let queries := (execute base (recover password container firstSalt)).2
    queries.countP isA=11 ∧ queries.countP isB=10 ∧ queries.countP isH=11 ∧
      queries.countP InverseCounts.isG=0 := by
  have a (input : Point Password Entropy) :
      isA (RoundRelabel.point K5Cut.rotation input)=isA input := by cases input <;> rfl
  have b (input : Point Password Entropy) :
      isB (RoundRelabel.point K5Cut.rotation input)=isB input := by cases input <;> rfl
  have h (input : Point Password Entropy) :
      isH (RoundRelabel.point K5Cut.rotation input)=isH input := by cases input <;> rfl
  have g (input : Point Password Entropy) :
      InverseCounts.isG (RoundRelabel.point K5Cut.rotation input)=
        InverseCounts.isG input := by cases input <;> rfl
  simp only [recover,RoundRelabel.execution,List.countP_map,Function.comp_def,a,b,h,g]
  exact raw_counts password (RoundRelabel.tables K5Cut.rotation base) container firstSalt

end K5Shared

/-! Concrete public-input K5 attack: share B11, invert eleven rounds and return
first accepted password, with one fixed fallback. No genuine password is an input.
-/
namespace K5Attack
open Gamma2Model QueryCounts
variable {Password Entropy : Type}
attribute [local irreducible] K5Cut.inverse

variable (source container : State) (base : Tables Password Entropy)

def test (password : Password) : Bool :=
  decide ((execute base (K5Cut.inverse password container)).1.1=source.2)

def run (source container : State) (firstSalt : Half) (fallback : Password) :
    List Password → OracleComp (spec Password Entropy) Password
  | [] => pure fallback
  | candidate :: rest => do
    let recovered ← K5Shared.recover candidate container firstSalt
    if decide (recovered.1=source.2) then pure candidate
    else run source container firstSalt fallback rest

/-- X/Y and the fixed candidate order are the only attack inputs. -/
def attack (source : State) (candidates : List Password) (fallback : Password) (container : State) :
    OracleComp (spec Password Entropy) Password := do
  let salt : Half ← ask (.b 11 container.1)
  run source container salt fallback candidates

/-- The executable attack implements precisely first-pass selection. -/
theorem result (fallback : Password) (candidates : List Password) :
    (execute base (run source container (base.b (11,container.1)) fallback candidates)).1=
      FirstPass.choose (test source container base) fallback candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [run,execute_bind,K5Shared.result,
      FirstPass.choose,test]
    split_ifs <;> simp_all

/-- The common salt query does not alter the first-pass result. -/
theorem attack_result (fallback : Password) (candidates : List Password) :
    (execute base (attack source candidates fallback container)).1=
      FirstPass.choose (test source container base) fallback candidates := by
  simp only [attack,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer]
  exact result source container base fallback candidates

/-- Every execution pays at most11A,10B and11H per tested candidate, with no G. -/
theorem run_counts (source container : State) (base : Tables Password Entropy) (firstSalt : Half)
    (fallback : Password) (candidates : List Password) :
    let queries := (execute base (run source container firstSalt fallback candidates)).2
    queries.countP isA≤11*candidates.length ∧ queries.countP isB≤10*candidates.length ∧
      queries.countP isH≤11*candidates.length ∧ queries.countP InverseCounts.isG=0 := by
  induction candidates with
  | nil => simp only [run,execute_pure,List.countP_nil,List.length_nil,Nat.mul_zero,le_refl,and_self]
  | cons candidate rest ih =>
    have paid := K5Shared.counts candidate base container firstSalt
    simp only [run,execute_bind]
    split_ifs
    · simp only [execute_pure,List.countP_append,List.countP_nil,add_zero,List.length_cons]
      omega
    · simp only [List.countP_append,List.length_cons]
      omega

/-- Total budgets are11mA,10m+1B,11mH and0G, including all repeat lookups. -/
theorem counts (source container : State) (base : Tables Password Entropy)
    (fallback : Password) (candidates : List Password) :
    let queries := (execute base (attack source candidates fallback container)).2
    queries.countP isA≤11*candidates.length ∧ queries.countP isB≤10*candidates.length+1 ∧
      queries.countP isH≤11*candidates.length ∧ queries.countP InverseCounts.isG=0 := by
  have rest := run_counts source container base (base.b (11,container.1)) fallback candidates
  simp only [attack,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer,List.singleton_append]
  simp only [List.countP_cons,isA,isB,isH,InverseCounts.isG,
    Bool.false_eq_true,ite_false,ite_true,add_zero]
  omega

end K5Attack

/-! Unconditional first-pass success for a fixed genuine password in K5.
False tests may be correlated; only their individual marginal bounds are used.
-/
namespace K5Conditional
open Gamma2Model GameExpectation
variable {Password Entropy : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype

def delta : ENNReal := 1/(2^128:ENNReal)+(11:ENNReal)/(2^256:ENNReal)

/-- Earlier false passes cover failure whenever no other obstruction to returning the real password exists. -/
theorem before_bound (source : State) (real : Password) (earlier : List Password)
    (no_real : real∉earlier) (win : Tables Password Entropy → Bool)
    (rescued : ∀ base,(∀ candidate∈earlier, K5FalsePass.event candidate real source base=false) → win base=true) :
    1-(earlier.length:ENNReal)*delta≤
      moment (sampleTables (Password := Password) (Entropy := Entropy))
        (fun base => if win base then 1 else 0) := by
  let bad (i : Fin earlier.length) (base : Tables Password Entropy) :=
    K5FalsePass.event (earlier.get i) real source base
  apply FirstPass.probability sampleTables win earlier.length bad delta
  · intro base
    by_cases failed : ∃ i,bad i base=true
    · exact Or.inr failed
    · apply Or.inl
      apply rescued base
      intro candidate member
      obtain ⟨i,equal⟩ := List.mem_iff_get.mp member
      cases hit : K5FalsePass.event candidate real source base with
      | false => rfl
      | true => exact False.elim (failed ⟨i,by simpa only [bad,equal] using hit⟩)
  · intro i
    have different : real≠earlier.get i := by
      intro equal
      exact no_real (equal.symm ▸ List.get_mem earlier i)
    exact K5FalsePass.probability (earlier.get i) real different source

/-- The actual attack returns a tested real password unless a preceding wrong password passes. -/
theorem tested (source : State) (real fallback : Password) (earlier later : List Password)
    (no_real : real∉earlier) : 1-(earlier.length:ENNReal)*delta≤ moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun base =>
        if decide ((execute base (K5Attack.attack source (earlier++real::later) fallback
          (KnownPairModel.cipher real base.a base.b base.h source))).1=real) then 1 else 0) := by
  apply before_bound source real earlier no_real
  intro base fail
  apply decide_eq_true
  rw [K5Attack.attack_result]
  apply FirstPass.selected
  · exact fail
  · exact decide_eq_true (K5Cipher.true_accepts real base source)

/-- An untested real fallback incurs only the false passes of all preceding tests. -/
theorem fallback (source : State) (real : Password) (earlier : List Password)
    (no_real : real∉earlier) : 1-(earlier.length:ENNReal)*delta≤ moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun base =>
        if decide ((execute base (K5Attack.attack source earlier real
          (KnownPairModel.cipher real base.a base.b base.h source))).1=real) then 1 else 0) := by
  apply before_bound source real earlier no_real
  intro base fail
  apply decide_eq_true
  rw [K5Attack.attack_result]
  exact FirstPass.fallback _ real earlier fail

end K5Conditional

namespace K5
open Gamma2Model GameExpectation MomentTools ProbabilityTools
variable {Password Entropy : Type} [Fintype Password] [DecidableEq Password]
  [Fintype Entropy] [DecidableEq Entropy] {m : Nat}
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] execute K5Attack.attack

/-- The false-match allowance stated in Proposition K5: one wrong candidate is accepted with
probability at most `2^-128 + 11·2^-256`, independent of the number of candidates. -/
def delta : ENNReal := 1/(2^128:ENNReal)+(11:ENNReal)/(2^256:ENNReal)

/-- Independent full-table sampling is the original known-pair experiment. -/
def rawGame (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Password) : PMF Bool :=
  passwords.bind fun real => sampleTables.map fun base =>
    decide ((execute base (adversary (KnownPairModel.cipher real base.a base.b base.h source))).1 = real)

theorem source_law (source : State) (passwords : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Password) :
    KnownPairSource.original (Entropy := Entropy) source passwords adversary = rawGame source passwords adversary := by
  unfold KnownPairSource.original rawGame DeltaInputs.environments independentPair
  simp only [K1.realGame, PMF.bind_bind, PMF.bind_map, PMF.pure_bind,
    PMF.map_comp, Function.comp_def]
  simp_rw [TableFactors.factor_h]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, KnownPairTransfer.score, K1.real]
  rfl

/-- Conditional success keeps the real cipher output inside the actual attack. -/
def conditional (source : State) (order : Fin (m+1) → Password) (real : Password) : ENNReal :=
  moment (sampleTables (Password := Password) (Entropy := Entropy)) fun base =>
    if decide ((execute base (K5Attack.attack source (RankedCandidates.tested order)
      (RankedCandidates.fallback order)
      (KnownPairModel.cipher real base.a base.b base.h source))).1 = real) then 1 else 0

/-- The conditional expectation is the actual Delta0 success probability. -/
theorem source_probability (source : State) (passwords : PMF Password)
    (order : Fin (m+1) → Password) : (KnownPairSource.original (Entropy := Entropy) source passwords
      (K5Attack.attack source (RankedCandidates.tested order)
        (RankedCandidates.fallback order))) true = moment passwords (conditional (Entropy := Entropy) source order) := by
  rw [source_law, rawGame, PMF.bind_apply]
  apply tsum_congr
  intro real
  rw [probability]
  rfl

private theorem pair_ranked (source : State) (order : Fin (m+1) → Password)
    (injective : Function.Injective order) (rank : Fin (m+1)) :
    1-(rank.val:ENNReal)*K5Conditional.delta ≤ conditional (Entropy := Entropy) source order (order rank) := by
  by_cases tested_rank : rank.val < m
  · let i : Fin m := ⟨rank.val,tested_rank⟩
    have same_rank : i.castSucc = rank := Fin.ext rfl
    have split : RankedCandidates.tested order =
        (RankedCandidates.tested order).take rank.val ++ order rank ::
          (RankedCandidates.tested order).drop (rank.val+1) := by
      simpa only [same_rank] using RankedCandidates.split order i
    have estimate := K5Conditional.tested (Entropy := Entropy) source (order rank)
      (RankedCandidates.fallback order)
      ((RankedCandidates.tested order).take rank.val)
      ((RankedCandidates.tested order).drop (rank.val+1))
      (RankedCandidates.absent order injective rank)
    rw [← split, RankedCandidates.earlier_length] at estimate
    exact estimate
  · have last : rank = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst rank
    have estimate := K5Conditional.fallback (Entropy := Entropy) source (RankedCandidates.fallback order)
      (RankedCandidates.tested order) (RankedCandidates.last_absent order injective)
    (try simp only [conditional, Fin.val_last, RankedCandidates.tested, List.length_ofFn, RankedCandidates.fallback] at estimate ⊢)
    exact estimate

/-- Each rank loses at most one stated delta_K for every earlier tested password. -/
theorem ranked (source : State) (order : Fin (m+1) → Password)
    (injective : Function.Injective order) (rank : Fin (m+1)) :
    1-(rank.val:ENNReal)*delta ≤ conditional (Entropy := Entropy) source order (order rank) :=
  pair_ranked source order injective rank

/-- Weighted matching loss in the original Delta0 game. -/
theorem weighted (source : State) (passwords : PMF Password) (order : Fin (m+1) → Password)
    (injective : Function.Injective order) :
    (∑ rank : Fin (m+1), passwords (order rank)*(1-(rank.val:ENNReal)*delta)) ≤
      (KnownPairSource.original (Entropy := Entropy) source passwords
        (K5Attack.attack source (RankedCandidates.tested order)
          (RankedCandidates.fallback order))) true := by
  have estimate := RankedCandidates.weighted_lower passwords order injective
    delta (conditional (Entropy := Entropy) source order) (ranked source order injective)
  rw [source_probability]
  exact estimate

end K5

namespace K5
open Gamma2Model GameExpectation
variable {N : Nat} {Entropy : Type} [Fintype Entropy] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype

/-- The requested prefix is capped at the finite dictionary; one candidate remains the fallback. -/
def attack (source : State) (m : Nat) (positive : 0 < N) :
    State → OracleComp (spec (Fin N) Entropy) (Fin N) :=
  let order := PasswordPrefix.order (PasswordPrefix.within (m := m) positive)
  K5Attack.attack source (RankedCandidates.tested order)
    (RankedCandidates.fallback order)

/-- The precise source sum includes empty testing and finite-dictionary saturation. -/
theorem bound (source : State) (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top (fun rank => passwords rank*(1-(rank.val:ENNReal)*delta)) (m+1) ≤
      (KnownPairSource.original (Entropy := Entropy) source passwords (attack source m positive)) true := by
  let k := PasswordPrefix.count m N
  have within : k+1 ≤ N := PasswordPrefix.within positive
  let order := PasswordPrefix.order within
  have injective := PasswordPrefix.injective within
  have estimate := RankedCandidates.weighted_lower passwords order injective
    delta (conditional (Entropy := Entropy) source order) (ranked source order injective)
  have mass : (∑ rank : Fin (k+1), passwords (order rank)*(1-(rank.val:ENNReal)*delta)) =
      RankedMass.top (fun rank => passwords rank*(1-(rank.val:ENNReal)*delta)) (k+1) :=
    by
      simpa only [order, PasswordPrefix.order] using
        (PasswordPrefix.mass
          (fun rank => passwords rank*(1-(rank.val:ENNReal)*delta)) within)
  rw [mass, PasswordPrefix.saturated _ positive] at estimate
  change _ ≤ (KnownPairSource.original (Entropy := Entropy) source passwords
    (K5Attack.attack source (RankedCandidates.tested order)
      (RankedCandidates.fallback order))) true
  rw [source_probability]
  exact estimate

/-- The stated coarse loss follows for every requested number of tested passwords. -/
theorem coarse_bound (source : State) (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top passwords (m+1)*(1-(m:ENNReal)*delta) ≤
      (KnownPairSource.original (Entropy := Entropy) source passwords (attack source m positive)) true := by
  let k := PasswordPrefix.count m N
  have within : k+1 ≤ N := PasswordPrefix.within positive
  let order := PasswordPrefix.order within
  have injective := PasswordPrefix.injective within
  have limit : k ≤ m := Nat.min_le_left m (N-1)
  have weighted := RankedCandidates.weighted_lower passwords order injective
    delta (conditional (Entropy := Entropy) source order) (ranked source order injective)
  have estimate := RankedCandidates.coarse_lower passwords order delta
    (conditional (Entropy := Entropy) source order) weighted
  rw [PasswordPrefix.mass, PasswordPrefix.saturated passwords positive] at estimate
  have index : (k:ENNReal) ≤ (m:ENNReal) := by exact_mod_cast limit
  have loss : (k:ENNReal)*delta ≤ (m:ENNReal)*delta := by
    simpa only [mul_comm] using mul_le_mul_right index delta
  change _ ≤ (KnownPairSource.original (Entropy := Entropy) source passwords
    (K5Attack.attack source (RankedCandidates.tested order)
      (RankedCandidates.fallback order))) true
  rw [source_probability]
  exact (mul_le_mul_right (tsub_le_tsub_left loss 1) _).trans estimate

omit [Fintype Entropy] [DecidableEq Entropy] in
/-- All actual executions have the advertised eleven-call cost, shared initial B and no G query. -/
theorem budgets (source : State) (m : Nat) (positive : 0 < N)
    (base : Tables (Fin N) Entropy) (container : State) :
    let queries := (execute base (attack source m positive container)).2
    queries.countP QueryCounts.isA ≤ 11*m ∧
      queries.countP QueryCounts.isB ≤ 10*m+1 ∧
      queries.countP QueryCounts.isH ≤ 11*m ∧
      queries.countP InverseCounts.isG = 0 := by
  let k := PasswordPrefix.count m N
  let order := PasswordPrefix.order (PasswordPrefix.within (m := m) positive)
  have estimate := K5Attack.counts source container base
    (RankedCandidates.fallback order) (RankedCandidates.tested order)
  have length : (RankedCandidates.tested order).length = k := List.length_ofFn
  rw [length] at estimate
  have limit : k ≤ m := Nat.min_le_left m (N-1)
  change (execute base (K5Attack.attack source
    (RankedCandidates.tested order) (RankedCandidates.fallback order) container)).2.countP
      QueryCounts.isA ≤ 11*m ∧
    (execute base (K5Attack.attack source
      (RankedCandidates.tested order) (RankedCandidates.fallback order) container)).2.countP
      QueryCounts.isB ≤ 10*m+1 ∧
    (execute base (K5Attack.attack source
      (RankedCandidates.tested order) (RankedCandidates.fallback order) container)).2.countP
      QueryCounts.isH ≤ 11*m ∧
    (execute base (K5Attack.attack source
      (RankedCandidates.tested order) (RankedCandidates.fallback order) container)).2.countP
      InverseCounts.isG = 0
  omega

/-- The precise lower sum loses at most the actual first creation-refusal probability. -/
theorem refused_bound (source : State) (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N)
    (later : KnownPairRefusal.Context (N := N) (Entropy := Entropy) ×
      TableFactors.HTable → PMF Bool) :
    RankedMass.top (fun rank => passwords rank*(1-(rank.val:ENNReal)*delta)) (m+1)-
      (2^256:ENNReal)⁻¹ ≤
      (KnownPairRefusal.game source passwords (attack source m positive) later) true := by
  have base := bound (Entropy := Entropy) source passwords m positive
  rw [KnownPairRefusal.original] at base
  have estimate := RefusalResponseLower.bound
    (KnownPairRefusal.initial passwords) (KnownPairRefusal.refused source)
    (KnownPairRefusal.score source (attack source m positive)) later _ base
  rw [KnownPairRefusal.probability] at estimate
  exact estimate

/-- The source's multiplicative lower bound has the same refusal correction, including failure. -/
theorem refused_coarse (source : State) (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N)
    (later : KnownPairRefusal.Context (N := N) (Entropy := Entropy) ×
      TableFactors.HTable → PMF Bool) :
    RankedMass.top passwords (m+1)*(1-(m:ENNReal)*delta)-(2^256:ENNReal)⁻¹ ≤
      (KnownPairRefusal.game source passwords (attack source m positive) later) true := by
  have base := coarse_bound (Entropy := Entropy) source passwords m positive
  rw [KnownPairRefusal.original] at base
  have estimate := RefusalResponseLower.bound
    (KnownPairRefusal.initial passwords) (KnownPairRefusal.refused source)
    (KnownPairRefusal.score source (attack source m positive)) later _ base
  rw [KnownPairRefusal.probability] at estimate
  exact estimate

end K5

end
end MhfeLean
