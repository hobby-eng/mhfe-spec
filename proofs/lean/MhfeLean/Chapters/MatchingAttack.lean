/- long: the operational attack, collision losses and resource counts form one argument. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import MhfeLean.Chapters.ChainCompletion
import MhfeLean.Chapters.ChainEarly
import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.Probability
import MhfeLean.Chapters.ShortSources

namespace MhfeLean
noncomputable section

/-! # Proposition G8: the actual ordered guessing attack and its losses
-/

/-! Exact query-family costs of the actual inverse, including every repeated call. -/
namespace InverseCounts
open Gamma2Model QueryCounts
variable {Password Entropy : Type}
attribute [local irreducible] finalize

def isG : Point Password Entropy → Bool
  | .g _ => true
  | _ => false

/-- Each inverse round makes exactly one A/B/H call and no G call. -/
theorem counts (password : Password) (tables : Tables Password Entropy)
    (fuel : Nat) (bound : fuel ≤ 12) (state : State) :
    let queries := (execute tables (finalize password fuel state bound)).2
    queries.countP isA=fuel ∧ queries.countP isB=fuel ∧ queries.countP isH=fuel ∧ queries.countP isG=0 := by
  induction fuel generalizing state with
  | zero => simp only [finalize,execute_pure,List.countP_nil,and_self]
  | succ fuel ih =>
    rw [FinalCut.finalize_step password tables fuel (by omega) state]
    dsimp only
    simp only [List.countP_append,List.countP_cons,List.countP_nil,isA,isB,isH,isG,
      Bool.false_eq_true,ite_true,ite_false,zero_add,add_zero]
    have rest := ih (by omega)
      (state.2 ^^^ tables.h (tables.a (password,tables.b (⟨fuel,by omega⟩,state.1)),⟨fuel,by omega⟩,state.1),state.1)
    omega

end InverseCounts

/-! Reuse the common first inverse salt lookup across distinct password guesses. -/
namespace SharedInverse
open Gamma2Model QueryCounts
variable {Password Entropy : Type}
attribute [local irreducible] finalize

def recover (password : Password) (container : State) (firstSalt : Half) :
    OracleComp (spec Password Entropy) State := do
  let key : Key ← ask (.a password firstSalt)
  let mask : Half ← ask (.h key 11 container.1)
  let rest ← finalize password 11 (container.2 ^^^ mask,container.1) (by omega)
  pure rest.1

/-- A shared B11 answer yields exactly the same inverse, with only that first B query omitted. -/
theorem execution (password : Password) (tables : Tables Password Entropy) (container : State) :
    execute tables (recover password container (tables.b (11,container.1)))=
      let full := execute tables (finalize password 12 container (by omega))
      (full.1.1,full.2.tail) := by
  rw [FinalCut.finalize_step password tables 11 (by omega) container]
  simp only [recover,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,List.append_nil,
    List.cons_append,List.nil_append,List.tail_cons]
  rfl

/-- Per candidate: twelve A, eleven additional B, twelve H and no G. -/
theorem counts (password : Password) (tables : Tables Password Entropy) (container : State) (firstSalt : Half) :
    let queries := (execute tables (recover password container firstSalt)).2
    queries.countP isA=12 ∧ queries.countP isB=11 ∧ queries.countP isH=12 ∧ queries.countP InverseCounts.isG=0 := by
  simp only [recover,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,List.append_nil,List.singleton_append]
  simp only [List.countP_cons,isA,isB,isH,InverseCounts.isG,
    Bool.false_eq_true,ite_true,ite_false,add_zero]
  have rest := InverseCounts.counts password tables 11 (by omega)
    (container.2 ^^^ tables.h (tables.a (password,firstSalt),11,container.1),container.1)
  omega

end SharedInverse

/-! Deterministic first-match search and an unconditional finite-union success estimate. -/
namespace FirstPass
open GameExpectation
variable {Password Sample : Type}

def choose (test : Password → Bool) (fallback : Password) : List Password → Password
  | [] => fallback
  | candidate :: rest => if test candidate then candidate else choose test fallback rest

/-- A tested real password is returned when all earlier candidates fail. -/
theorem selected (test : Password → Bool) (fallback real : Password) (earlier later : List Password)
    (fail : ∀ candidate ∈ earlier,test candidate=false) (pass : test real=true) :
    choose test fallback (earlier ++ real :: later)=real := by
  induction earlier with
  | nil => simp only [List.nil_append,choose,pass,ite_true]
  | cons candidate rest ih =>
    have head := fail candidate (by simp only [List.mem_cons_self])
    have tail : ∀ value ∈ rest,test value=false := fun value member => fail value (List.mem_cons_of_mem candidate member)
    simp only [List.cons_append,choose,head,Bool.false_eq_true,ite_false]
    exact ih tail

/-- The free final guess is returned if no tested password passes. -/
theorem fallback (test : Password → Bool) (real : Password) (earlier : List Password)
    (fail : ∀ candidate ∈ earlier,test candidate=false) : choose test real earlier=real := by
  induction earlier with
  | nil => rfl
  | cons candidate rest ih =>
    have head := fail candidate (by simp only [List.mem_cons_self])
    have tail : ∀ value ∈ rest,test value=false := fun value member => fail value (List.mem_cons_of_mem candidate member)
    simp only [choose,head,Bool.false_eq_true,ite_false]
    exact ih tail

/-- No independence between false passes is assumed; the finite union is bounded by its marginal masses. -/
theorem probability (law : PMF Sample) (win : Sample → Bool) (count : Nat)
    (bad : Fin count → Sample → Bool) (delta : ENNReal)
    (cover : ∀ sample,win sample=true ∨ ∃ i,bad i sample=true)
    (bounds : ∀ i,moment law (fun sample => if bad i sample then 1 else 0) ≤ delta) :
    1-(count:ENNReal)*delta ≤ moment law (fun sample => if win sample then 1 else 0) := by
  have pointwise (sample : Sample) :
      (1:ENNReal) ≤ (if win sample then 1 else 0)+∑ i : Fin count,(if bad i sample then 1 else 0) := by
    obtain won | ⟨i,hit⟩ := cover sample
    · rw [if_pos won]
      exact le_add_right le_rfl
    · have selected : (1:ENNReal)=(if bad i sample then 1 else 0) := by rw [if_pos hit]
      have in_sum : (1:ENNReal) ≤ ∑ j : Fin count,(if bad j sample then 1 else 0) := by
        calc
          _ = (if bad i sample then 1 else 0) := selected
          _ ≤ _ := Finset.single_le_sum (f := fun j => if bad j sample then (1:ENNReal) else 0)
            (fun j _ => zero_le) (Finset.mem_univ i)
      exact in_sum.trans (le_add_left le_rfl)
  have total : (1:ENNReal) ≤ moment law (fun sample => if win sample then 1 else 0)+(count:ENNReal)*delta := by
    calc
      _ = moment law (fun _ => (1:ENNReal)) := (MomentTools.constant law 1).symm
      _ ≤ moment law (fun sample => (if win sample then 1 else 0)+∑ i : Fin count,(if bad i sample then 1 else 0)) :=
        MomentTools.mono _ _ _ pointwise
      _ = _ := MomentTools.add _ _ _
      _ ≤ _ := by
        apply add_le_add le_rfl
        rw [MomentTools.finite_sum]
        calc
          _ ≤ ∑ _i : Fin count,delta := Finset.sum_le_sum (fun i _ => bounds i)
          _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact tsub_le_iff_right.mpr total

end FirstPass

/-! The concrete ordered guessing attack shares B11 and stops at the first verifier pass. -/
namespace G8Attack
open Gamma2Model QueryCounts
variable {Password E V R : Type} [DecidableEq V]
attribute [local irreducible] finalize

variable (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))

def test (container : State) (tables : Tables Password E) (password : Password) : Bool :=
  let source := coordinates.symm (execute tables (finalize password 12 container (by omega))).1.1
  decide ((hash (tables.g source.1)).1=source.2)

def run (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (container : State) (firstSalt : Half) (fallback : Password) :
    List Password → OracleComp (spec Password E) Password
  | [] => pure fallback
  | candidate :: rest => do
    let recovered ← SharedInverse.recover candidate container firstSalt
    let source := coordinates.symm recovered
    let digest : Hash ← ask (.g source.1)
    if decide ((hash digest).1=source.2) then pure candidate
    else run coordinates hash container firstSalt fallback rest

def attack (candidates : List Password) (fallback : Password) (container : State) :
    OracleComp (spec Password E) Password := do
  let salt : Half ← ask (.b 11 container.1)
  run coordinates hash container salt fallback candidates

/-- First-match semantics for the actual oracle computation, not a supplied simulator. -/
theorem result (container : State) (tables : Tables Password E) (fallback : Password)
    (candidates : List Password) :
    (execute tables (run coordinates hash container (tables.b (11,container.1)) fallback candidates)).1=
      FirstPass.choose (test coordinates hash container tables) fallback candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [run,execute_bind,SharedInverse.execution,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer,
      FirstPass.choose,test]
    split_ifs <;> simp_all

/-- The initial common B query changes no first-match result. -/
theorem attack_result (tables : Tables Password E) (fallback : Password)
    (candidates : List Password) (container : State) :
    (execute tables (attack coordinates hash candidates fallback container)).1=
      FirstPass.choose (test coordinates hash container tables) fallback candidates := by
  simp only [attack,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer]
  exact result coordinates hash container tables fallback candidates

/-- Every execution respects the advertised per-tested-candidate caps, even with repeated points. -/
theorem run_counts (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (container : State) (tables : Tables Password E) (firstSalt : Half) (fallback : Password) (candidates : List Password) :
    let queries := (execute tables (run coordinates hash container firstSalt fallback candidates)).2
    queries.countP isA ≤ 12*candidates.length ∧ queries.countP isB ≤ 11*candidates.length ∧
      queries.countP isH ≤ 12*candidates.length ∧ queries.countP InverseCounts.isG ≤ candidates.length := by
  induction candidates with
  | nil => simp only [run,execute_pure,List.countP_nil,List.length_nil,Nat.mul_zero,le_refl,and_self]
  | cons candidate rest ih =>
    have paid := SharedInverse.counts candidate tables container firstSalt
    simp only [run,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer]
    split_ifs <;> simp only [execute_pure,List.countP_append,List.countP_cons,List.countP_nil,isA,isB,isH,
      InverseCounts.isG,Bool.false_eq_true,ite_false,ite_true,add_zero,List.length_cons] <;> omega

/-- Total budgets:12m A,11m+1 B,12m H and at most m G. -/
theorem counts (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (tables : Tables Password E) (fallback : Password) (candidates : List Password) (container : State) :
    let queries := (execute tables (attack coordinates hash candidates fallback container)).2
    queries.countP isA ≤ 12*candidates.length ∧ queries.countP isB ≤ 11*candidates.length+1 ∧
      queries.countP isH ≤ 12*candidates.length ∧ queries.countP InverseCounts.isG ≤ candidates.length := by
  have rest := run_counts coordinates hash container tables (tables.b (11,container.1)) fallback candidates
  simp only [attack,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer,List.singleton_append]
  simp only [List.countP_cons,isA,isB,isH,InverseCounts.isG,
    Bool.false_eq_true,ite_false,ite_true,add_zero]
  omega

end G8Attack

/-! An unprogrammed verifier query has the exact uniform prefix law, not merely a guessed probability. -/
namespace VerifierProbability
open GameExpectation ProbabilityTools
variable {E V R H : Type} [DecidableEq E]
  [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype R] [Nonempty R] [Fintype H] [Nonempty H]

omit [DecidableEq V] in
/-- A fixed input's hash prefix is uniform under the complete independent hash table. -/
theorem prefix_law (hash : H ≃ (V × R)) (point : E) :
    (PMF.uniformOfFintype (E → H)).map (fun table => (hash (table point)).1)=PMF.uniformOfFintype V := by
  calc
    _ = ((PMF.uniformOfFintype (E → H)).map (fun table => table point)).map (fun value => (hash value).1) :=
      (PMF.map_comp _ _ _).symm
    _ = (PMF.uniformOfFintype H).map (fun value => (hash value).1) := by rw [uniform_eval]
    _ = ((PMF.uniformOfFintype H).map hash).map Prod.fst := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [PMF.uniformOfFintype_map_of_bijective hash hash.bijective,uniform_fst]

/-- Match probability for the verifier alone, with input and target fixed before G is sampled. -/
theorem probability (hash : H ≃ (V × R)) (point : E) (target : V) :
    moment (PMF.uniformOfFintype (E → H))
      (fun table => if decide ((hash (table point)).1=target) then 1 else 0)=
      1/(Fintype.card V:ENNReal) := by
  rw [← MomentTools.probability]
  change ((PMF.uniformOfFintype (E → H)).map
    ((fun value : V => decide (value=target)) ∘ (fun table => (hash (table point)).1))) true=_
  rw [← PMF.map_comp,prefix_law]
  simpa only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] using
    FreshSampling.uniform_hit_probability ({target}:Finset V)

/-- Programming another entropy preserves that query and its exact false-match probability. -/
theorem off_point (hash : H ≃ (V × R)) (real point : E) (different : point ≠ real) (realVerifier target : V) :
    moment (PMF.uniformOfFintype (E → H)) (fun table =>
      if decide ((hash ((Function.update table real
        (hash.symm (realVerifier,(hash (table real)).2))) point)).1=target) then 1 else 0)=
      1/(Fintype.card V:ENNReal) := by
  simp only [Function.update_of_ne different]
  exact probability hash point target

omit [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype R] [Nonempty R] [Fintype H] [Nonempty H] in
/-- The genuine source always passes the programmed verifier. -/
theorem real_passes (hash : H ≃ (V × R)) (table : E → H) (real : E) (verifier : V) :
    (hash ((Function.update table real (hash.symm (verifier,(hash (table real)).2))) real)).1=verifier := by
  rw [Function.update_self,Equiv.apply_symm_apply]

end VerifierProbability

/-! Fixed candidate inverses and their programmed-verifier tests for the G8 experiment. -/
namespace CandidateData
open Gamma2Model KnownPairModel CryptoInputs
variable {Password E V R : Type}

def recovered (password : Password) (other : ABH Password) (container : State) : State :=
  (roundsEquiv (allMasks password other.1 other.2.1 other.2.2)).symm container

def fields (coordinates : (E × V) ≃ State) (password : Password) (other : ABH Password)
    (container : State) : E × V :=
  coordinates.symm (recovered password other container)

/-- Candidate data is exactly the actual inverse executor result; it reads no G entry. -/
theorem actual (coordinates : (E × V) ≃ State) (password : Password) (other : ABH Password)
    (container : State) (g : E → Hash) :
    coordinates.symm (execute (tables other g) (finalize password 12 container (by omega))).1.1=
      fields coordinates password other container := by
  rw [CipherExecution.inverse]
  rfl

variable [DecidableEq E]

def programmed (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (real : Password)
    (other : ABH Password) (container : State) (g : E → Hash) : E → Hash :=
  let source := fields coordinates real other container
  Function.update g source.1 (hash.symm (source.2,(hash (g source.1)).2))

def passes [DecidableEq V] (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (real candidate : Password) (other : ABH Password) (container : State) (g : E → Hash) : Bool :=
  let test := fields coordinates candidate other container
  decide ((hash (programmed coordinates hash real other container g test.1)).1=test.2)

variable [DecidableEq V]

/-- The genuine password's result always passes, without any probability qualification. -/
theorem real_passes (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (real : Password)
    (other : ABH Password) (container : State) (g : E → Hash) :
    passes coordinates hash real real other container g=true := by
  simp only [passes,programmed,VerifierProbability.real_passes,decide_true]

variable [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- At distinct recovered entropies the false candidate's verifier has exactly the uniform pass rate. -/
theorem distinct_probability (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (real candidate : Password) (other : ABH Password) (container : State)
    (different : (fields coordinates candidate other container).1 ≠ (fields coordinates real other container).1) :
    GameExpectation.moment (PMF.uniformOfFintype (E → Hash))
      (fun g => if passes coordinates hash real candidate other container g then 1 else 0)=
      1/(Fintype.card V:ENNReal) := by
  exact VerifierProbability.off_point hash _ _ different _ _

end CandidateData

/-! Expose exactly one password's independent A row through queries while fixing every other table value. -/
namespace RowA
open Gamma2Model OracleProjection FocusedExecution
variable {Password Entropy Result : Type} [DecidableEq Password]

variable (password : Password) (base : Tables Password Entropy) (row : Half → Key)

/-- The selected password's row is the only table component replaced. -/
def filled : Tables Password Entropy :=
  ⟨fun pair => if pair.1=password then row pair.2 else base.a pair,base.b,base.h,base.g⟩

/-- Other passwords and all cheap oracles are evaluated without consulting the selected row. -/
def handler (password : Password) (base : Tables Password Entropy) : Handler Password Entropy Half Key
  | .a candidate salt => if candidate=password then .inr (salt,fun value : Key => value) else .inl (base.a (candidate,salt))
  | .b round right => .inl (base.b (round,right))
  | .h key round right => .inl (base.h (key,round,right))
  | .g entropy => .inl (base.g entropy)

def selected (password : Password) : Point Password Entropy → Option Half
  | .a candidate salt => if candidate=password then some salt else none
  | _ => none

/-- This is an actual compiler identity; access to an independent row is not supplied as an axiom. -/
theorem agrees (point : Point Password Entropy) :
    resolve (handler password base) row point=answer (filled password base row) point := by
  cases point with
  | a candidate salt => by_cases equal : candidate=password <;> simp [handler,resolve,filled,answer,equal]
  | b round right => rfl
  | h key round right => rfl
  | g entropy => rfl

private theorem delegates (password : Password) (base : Tables Password Entropy) :
    delegatedPoint (handler password base)=selected (Entropy := Entropy) password := by
  funext point
  cases point with
  | a candidate salt => by_cases equal : candidate=password <;> simp [handler,delegatedPoint,selected,equal]
  | b round right => rfl
  | h key round right => rfl
  | g entropy => rfl

def program (password : Password) (base : Tables Password Entropy)
    (original : OracleComp (spec Password Entropy) Result) := focused (handler password base) original

/-- Every original result is preserved with no direct access to the selected row. -/
theorem result (original : OracleComp (spec Password Entropy) Result) :
    (OracleTree.evaluate row (program password base original)).1=(execute (filled password base row) original).1 :=
  result_eq (handler password base) row (filled password base row) (agrees password base row) original

/-- The focused transcript contains exactly that password's salt lookups, with every duplicate retained. -/
theorem trace (original : OracleComp (spec Password Entropy) Result) :
    (OracleTree.evaluate row (program password base original)).2=
      (execute (filled password base row) original).2.filterMap (selected password) := by
  have same := trace_eq (handler password base) row (filled password base row) (agrees password base row) original
  (try simp only [delegates] at same ⊢)
  exact same

private theorem count_points (password : Password) (queries : List (Point Password Entropy)) :
    (queries.filterMap (selected password)).length=queries.countP (QueryCounts.aFor password) := by
  induction queries with
  | nil => rfl
  | cons point rest ih =>
    cases point with
    | a candidate salt => by_cases equal : candidate=password <;> simp [selected,QueryCounts.aFor,equal,ih]
    | b round right => simpa only [List.filterMap_cons,selected,QueryCounts.aFor,List.countP_cons,Bool.false_eq_true,ite_false,add_zero] using ih
    | h key round right => simpa only [List.filterMap_cons,selected,QueryCounts.aFor,List.countP_cons,Bool.false_eq_true,ite_false,add_zero] using ih
    | g entropy => simpa only [List.filterMap_cons,selected,QueryCounts.aFor,List.countP_cons,Bool.false_eq_true,ite_false,add_zero] using ih

/-- The probability analysis can charge only the wrong password's calls, rather than both inverse chains. -/
theorem count (original : OracleComp (spec Password Entropy) Result) :
    (OracleTree.evaluate row (program password base original)).2.length=
      (execute (filled password base row) original).2.countP (QueryCounts.aFor password) := by
  rw [trace,count_points]

end RowA

/-! A complete A table factors exactly into one password row and all other rows. -/
namespace RowUniform
open Gamma2Model ProbabilityTools
variable {Password Entropy : Type} [DecidableEq Password]
attribute [local instance] FiniteBits.fintype

abbrev Outside (password : Password) := {point : Password × Half // point.1 ≠ password}

/-- The complement is retained jointly; uniformity of the row alone would not establish independence. -/
def split (password : Password) : (Password × Half → Key) ≃ ((Half → Key) × (Outside password → Key)) where
  toFun table := (fun salt => table (password,salt),fun point => table point.val)
  invFun fields point := if equal : point.1=password then fields.1 point.2 else fields.2 ⟨point,equal⟩
  left_inv := by
    intro table
    funext point
    dsimp only
    split_ifs with equal
    · exact congrArg table (Prod.ext equal.symm rfl)
    · rfl
  right_inv := by
    intro fields
    apply Prod.ext
    · funext salt
      exact dif_pos rfl
    · funext point
      exact dif_neg point.property

/-- Replacing one row retains the exact complement and changes no other A entry. -/
theorem filled_split (password : Password) (base : Tables Password Entropy) (row : Half → Key) :
    split password (RowA.filled password base row).a=(row,(split password base.a).2) := by
  apply Prod.ext
  · funext salt
    simp only [split,Equiv.coe_fn_mk,RowA.filled,if_true]
  · funext point
    simp only [split,Equiv.coe_fn_mk,RowA.filled,if_neg point.property]

variable [Fintype Password]

/-- This is the whole joint distribution, including independence from all other password rows. -/
theorem joint (password : Password) :
    (PMF.uniformOfFintype (Password × Half → Key)).map (split password)=
      independentPair (PMF.uniformOfFintype (Half → Key)) (PMF.uniformOfFintype (Outside password → Key)) := by
  rw [PMF.uniformOfFintype_map_of_bijective (split password) (split password).bijective]
  exact uniform_product

/-- Sample the complement first and an independent complete row last, with no conditioning assumption. -/
theorem complement_first (password : Password) :
    PMF.uniformOfFintype (Password × Half → Key)=
      (PMF.uniformOfFintype (Outside password → Key)).bind fun other =>
        (PMF.uniformOfFintype (Half → Key)).map fun row => (split password).symm (row,other) := by
  have restored := PMF.uniformOfFintype_map_of_bijective (split password).symm (split password).symm.bijective
  rw [← restored,uniform_product]
  simp only [independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def]
  have simpaTerm := PMF.bind_comm (PMF.uniformOfFintype (Half → Key)) (PMF.uniformOfFintype (Outside password → Key)) (fun row other => PMF.pure ((split password).symm (row,other)))
  (try simp only [PMF.map] at simpaTerm ⊢)
  exact simpaTerm

end RowUniform

/-! Factor the original four-oracle law with a selected password row sampled last. -/
namespace RowSampling
open Gamma2Model GameExpectation
variable {Password Entropy : Type} [DecidableEq Password]
attribute [local instance] FiniteBits.fintype

abbrev Others (password : Password) := (RowUniform.Outside password → Key) ×
  TableFactors.BTable × TableFactors.HTable × TableFactors.GTable Entropy

/-- The complementary A rows and all cheap functions are retained, not marginalized away. -/
def pack (password : Password) : (Others (Entropy := Entropy) password × (Half → Key)) ≃ Tables Password Entropy where
  toFun fields := ⟨(RowUniform.split password).symm (fields.2,fields.1.1),
    fields.1.2.1,fields.1.2.2.1,fields.1.2.2.2⟩
  invFun tables := (((RowUniform.split password tables.a).2,tables.b,tables.h,tables.g),
    (RowUniform.split password tables.a).1)
  left_inv := by
    intro fields
    simp only [Equiv.apply_symm_apply]
  right_inv := by
    intro tables
    simp only [Prod.mk.eta,Equiv.symm_apply_apply]

def base (password : Password) (others : Others (Entropy := Entropy) password) : Tables Password Entropy :=
  pack password (others,fun _ => 0)

/-- Filling a row of the fixed complementary table reconstructs the exact original table record. -/
theorem filled (password : Password) (others : Others (Entropy := Entropy) password) (row : Half → Key) :
    RowA.filled password (base password others) row=pack password (others,row) := by
  have a_equal : (RowA.filled password (base password others) row).a=
      (RowUniform.split password).symm (row,others.1) := by
    apply (RowUniform.split password).injective
    rw [RowUniform.filled_split]
    simp only [base,pack,Equiv.coe_fn_mk,Equiv.apply_symm_apply]
  exact congrArg (fun a => (⟨a,others.2.1,others.2.2.1,others.2.2.2⟩ : Tables Password Entropy)) a_equal

variable [Fintype Password] [Fintype Entropy] [DecidableEq Entropy]

/-- Joint sampling is exactly Gamma2Model.sampleTables, with no new independence assumption. -/
theorem law (password : Password) : sampleTables (Password := Password) (Entropy := Entropy)=
      (PMF.uniformOfFintype (Others (Entropy := Entropy) password)).bind fun others =>
        (PMF.uniformOfFintype (Half → Key)).map fun row =>
          RowA.filled password (base password others) row := by
  simp_rw [filled]
  exact TableFactors.sample_factor (pack password)

/-- A conditional selected-row bound averages to the same bound for all original ideal functions. -/
theorem probability (password : Password) (test : Tables Password Entropy → ENNReal) (limit : ENNReal)
    (row_bound : ∀ others : Others (Entropy := Entropy) password,
      moment (PMF.uniformOfFintype (Half → Key))
        (fun row => test (RowA.filled password (base password others) row)) ≤ limit) :
    moment (sampleTables (Password := Password) (Entropy := Entropy)) test ≤ limit := by
  rw [law password,MomentTools.bind]
  simp_rw [moment_map,Function.comp_def]
  exact MomentTools.bounded _ _ _ row_bound

end RowSampling

/-! Exact A-call accounting and terminal-key provenance for the actual inverse prefix. -/
namespace CutKeyFacts
open Gamma2Model FinalCut
variable {Password Entropy : Type} [DecidableEq Password]

/-- Every inverse prefix through round zero invokes A exactly round+1 times, including repeats. -/
theorem count (password : Password) (tables : Tables Password Entropy) (round : Nat)
    (bound : round < 12) (state : State) :
    (execute tables (prepare password round state bound)).2.countP
      (QueryCounts.aFor password)=round+1 := by
  induction round generalizing state with
  | zero => simp [prepare,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,QueryCounts.aFor]
  | succ round ih =>
    rw [prepare_step]
    dsimp only
    simp only [List.countP_append,List.countP_cons,List.countP_nil,QueryCounts.aFor,
      decide_true,ite_true,Bool.false_eq_true,ite_false,zero_add,add_zero]
    rw [ih (by omega)]
    omega

omit [DecidableEq Password] in
/-- The returned K0 is an answer to an A point actually present in that same prefix's log. -/
theorem key_queried (password : Password) (tables : Tables Password Entropy) (round : Nat)
    (bound : round < 12) (state : State) :
    ∃ salt, Point.a password salt ∈ (execute tables (prepare password round state bound)).2 ∧
      tables.a (password,salt)=(execute tables (prepare password round state bound)).1.key := by
  induction round generalizing state with
  | zero =>
    refine ⟨tables.b (0,state.1),?_,rfl⟩
    simp [prepare,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer]
  | succ round ih =>
    rw [prepare_step]
    dsimp only
    obtain ⟨salt,member,equal⟩ := ih (by omega)
      (state.2 ^^^ tables.h (tables.a (password,tables.b (⟨round+1,bound⟩,state.1)),⟨round+1,bound⟩,state.1),state.1)
    exact ⟨salt,List.mem_append.mpr (Or.inr member),equal⟩

end CutKeyFacts

/-! An inverse under a different password never reads the selected A row. -/
namespace RowIndependent
open Gamma2Model
variable {Password Entropy : Type} [DecidableEq Password]

/-- Retain the full inverse result and both chain/query logs when another password's row changes. -/
theorem inverse (focus password : Password) (different : password ≠ focus)
    (base : Tables Password Entropy) (row : Half → Key) (fuel : Nat) (state : State)
    (within : fuel ≤ 12) :
    execute (RowA.filled focus base row) (finalize password fuel state within)=
      execute base (finalize password fuel state within) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    simp only [finalize,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,RowA.filled,if_neg different]
    simp only [RowA.filled] at ih
    simp only [ih]

/-- In particular the reference password's K0 and pre-H0 state are independent of that selected row. -/
theorem cut (focus password : Password) (different : password ≠ focus)
    (base : Tables Password Entropy) (row : Half → Key) (round : Nat) (state : State)
    (within : round < 12) :
    execute (RowA.filled focus base row) (FinalCut.prepare password round state within)=
      execute base (FinalCut.prepare password round state within) := by
  induction round generalizing state with
  | zero => simp only [FinalCut.prepare,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,RowA.filled,if_neg different]
  | succ round ih =>
    simp only [FinalCut.prepare,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,RowA.filled,if_neg different]
    simp only [RowA.filled] at ih
    simp only [ih]

end RowIndependent

/-! Select a query before its answer, enabling only its first occurrence in a consistent table. -/
namespace NthFresh
open OracleTree OptionalFresh
variable {Domain Answer Result : Type} [DecidableEq Domain]

/-- The oracle program never reads the selected answer before returning its optional context. -/
def prepare (fallback : Domain) : Program Domain Answer Result → Nat → List Domain →
    Program Domain Answer (Domain × Option Unit)
  | .done _,_,_ => .done (fallback,none)
  | .query point _,0,past => .done (point,if point ∈ past then none else some ())
  | .query point next,index+1,past =>
      .query point (fun value => prepare fallback (next value) index (past++[point]))

variable (fallback : Domain) (original : Program Domain Answer Result) (index : Nat)

/-- Freshness follows from the observer's own execution and complete earlier history. -/
theorem history (past : List Domain) (table : Domain → Answer)
    (enabled : (evaluate table (prepare fallback original index past)).1.2 ≠ none) :
    (evaluate table (prepare fallback original index past)).1.1 ∉
      past++(evaluate table (prepare fallback original index past)).2 := by
  induction original generalizing index past with
  | done result => exact False.elim (enabled rfl)
  | query point next ih =>
    cases index with
    | zero =>
      by_cases present : point ∈ past
      · have disabled : (evaluate table (prepare fallback (.query point next) 0 past)).1.2=none := by
          simp only [prepare,if_pos present,evaluate]
        exact False.elim (enabled disabled)
      · simpa only [prepare,if_neg present,evaluate,List.append_nil] using present
    | succ index =>
      have inherited := ih (table point) index (past++[point]) enabled
      simpa only [prepare,evaluate,List.append_assoc,List.singleton_append] using inherited

/-- No freshness premise is postulated for the original program or its repeated queries. -/
theorem fresh : EnabledFresh (prepare fallback original index []) := by
  intro table enabled
  simpa only [List.nil_append] using history fallback original index [] table enabled

/-- Every genuinely first occurrence is selected with its exact point and enabled context. -/
theorem selected (past : List Domain) (table : Domain → Answer)
    (within : index < (evaluate table original).2.length)
    (unread : (evaluate table original).2.getD index fallback ∉ past++(evaluate table original).2.take index) :
    (evaluate table (prepare fallback original index past)).1=
      ((evaluate table original).2.getD index fallback,some ()) := by
  induction original generalizing index past with
  | done result => simp only [evaluate,List.length_nil] at within; omega
  | query point next ih =>
    cases index with
    | zero =>
      have absent : point ∉ past := by simpa [evaluate] using unread
      simp only [prepare,if_neg absent,evaluate]
      rfl
    | succ index =>
      have inside : index < (evaluate table (next (table point))).2.length := by
        simpa only [evaluate,List.length_cons,Nat.succ_lt_succ_iff] using within
      have absent : (evaluate table (next (table point))).2.getD index fallback ∉
          (past++[point])++(evaluate table (next (table point))).2.take index := by
        simpa [evaluate,List.append_assoc] using unread
      have simpaTerm := ih (table point) index (past++[point]) inside absent
      (try simp only [prepare,evaluate] at simpaTerm ⊢)
      exact simpaTerm

noncomputable section
variable [DecidableEq Answer] [Fintype Domain] [Fintype Answer] [Nonempty Answer]

/-- One guarded query contributes at most one uniform-answer point mass. -/
theorem probability (fallback : Domain) (original : Program Domain Answer Result) (index : Nat) (target : Answer) :
    GameExpectation.moment (PMF.uniformOfFintype (Domain → Answer))
      (fun table => if rawHit (prepare fallback original index []) (fun _ : Unit => {target}) table then 1 else 0) ≤
      (1:ENNReal)/(Fintype.card Answer:ENNReal) := by
  rw [← MomentTools.probability]
  have estimate := hit_bound (prepare fallback original index []) (fun _ : Unit => {target})
    (fresh fallback original index) (fun _ => 1) (by
      intro table
      cases selection : (evaluate table (prepare fallback original index [])).1.2 with
      | none => simp only [optionalSet,Finset.card_empty]; omega
      | some context => simp only [optionalSet,Finset.card_singleton,le_refl])
  apply estimate.trans_eq
  simpa only [GameExpectation.moment,Nat.cast_one] using
    MomentTools.constant (PMF.uniformOfFintype (Domain → Answer)) ((1:ENNReal)/(Fintype.card Answer:ENNReal))

end
end NthFresh

/-! An adaptive program with at most q calls hits a fixed answer with probability at most q/card. -/
namespace QueryHit
open OracleTree OptionalFresh GameExpectation MomentTools
variable {Domain Answer Result : Type} [DecidableEq Domain] [DecidableEq Answer]

def event (original : Program Domain Answer Result) (target : Answer) (table : Domain → Answer) :
    Bool := by
  classical
  exact decide (∃ point ∈ (evaluate table original).2,table point=target)

/-- Any matching answer is charged to the first occurrence of its query point. -/
theorem covered (fallback : Domain) (original : Program Domain Answer Result) (target : Answer)
    (limit : Nat) (table : Domain → Answer) (budget : (evaluate table original).2.length ≤ limit)
    (hit : event original target table=true) :
    ∃ index : Fin limit,rawHit (NthFresh.prepare fallback original index.val []) (fun _ : Unit => {target}) table=true := by
  classical
  have details : ∃ point ∈ (evaluate table original).2,table point=target := of_decide_eq_true hit
  obtain ⟨point,member,answerEq⟩ := details
  let queries := (evaluate table original).2
  let index := queries.idxOf point
  have within : index < queries.length := List.idxOf_lt_length_iff.mpr member
  have lookup : queries.getD index fallback=point :=
    (List.getElem_eq_getD (h := within) fallback).symm.trans (List.getElem_idxOf within)
  have unread : queries.getD index fallback ∉ []++queries.take index := by
    rw [List.nil_append,lookup]
    intro found
    have contradiction := (List.mem_take_iff_idxOf_lt member).mp found
    exact Nat.lt_irrefl index contradiction
  have chosen := NthFresh.selected fallback original index [] table within unread
  rw [lookup] at chosen
  refine ⟨⟨index,within.trans_le budget⟩,?_⟩
  simp only [rawHit,chosen,optionalSet,Finset.mem_singleton,answerEq,decide_true]

variable [Fintype Domain] [Fintype Answer] [Nonempty Answer]

/-- Repeated calls add cost but do not invalidate the first-occurrence probability argument. -/
theorem probability (fallback : Domain) (original : Program Domain Answer Result) (target : Answer)
    (limit : Nat) (budget : ∀ table : Domain → Answer,(evaluate table original).2.length ≤ limit) :
    moment (PMF.uniformOfFintype (Domain → Answer)) (fun table => if event original target table then 1 else 0) ≤
      (limit:ENNReal)/(Fintype.card Answer:ENNReal) := by
  classical
  let test := fun (index : Fin limit) table =>
    rawHit (NthFresh.prepare fallback original index.val []) (fun _ : Unit => {target}) table
  have included :
      moment (PMF.uniformOfFintype (Domain → Answer)) (fun table => if event original target table then 1 else 0) ≤
      ∑ index : Fin limit,moment (PMF.uniformOfFintype (Domain → Answer)) (fun table => if test index table then 1 else 0) := by
    rw [← MomentTools.finite_sum]
    apply mono
    intro table
    by_cases hit : event original target table=true
    · rw [hit]
      obtain ⟨index,matching⟩ := covered fallback original target limit table (budget table) hit
      have one : (if test index table then 1 else 0 : ENNReal)=1 := by simp [test,matching]
      calc
        _ = 1 := rfl
        _ = (if test index table then 1 else 0 : ENNReal) := one.symm
        _ ≤ _ := Finset.single_le_sum
          (f := fun query : Fin limit => (if test query table then 1 else 0 : ENNReal))
          (fun _ _ => zero_le) (Finset.mem_univ index)
    · simp only [Bool.eq_false_iff.mpr hit,Bool.false_eq_true,if_false,zero_le]
  apply included.trans
  calc
    _ ≤ ∑ _ : Fin limit,(1:ENNReal)/(Fintype.card Answer:ENNReal) := by
      apply Finset.sum_le_sum
      intro index _
      exact NthFresh.probability fallback original index.val target
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,div_eq_mul_inv,one_mul]

end QueryHit

/-! Fixed-target key hits are charged only to the selected password row's actual A calls. -/
namespace RowQueryBound
open Gamma2Model GameExpectation
variable {Password Entropy Result : Type} [DecidableEq Password]
attribute [local instance] FiniteBits.fintype

def event (password : Password) (target : Key)
    (original : OracleComp (spec Password Entropy) Result) (tables : Tables Password Entropy) : Bool := by
  classical
  exact decide (∃ salt ∈ (execute tables original).2.filterMap (RowA.selected password),tables.a (password,salt)=target)

/-- The focused event is exactly a matching key at an actually queried A point. -/
theorem event_eq (password : Password) (base : Tables Password Entropy) (row : Half → Key)
    (original : OracleComp (spec Password Entropy) Result) (target : Key) :
    QueryHit.event (RowA.program password base original) target row=
      event password target original (RowA.filled password base row) := by
  classical
  unfold QueryHit.event event
  rw [RowA.trace, decide_eq_decide]
  have key (salt : Half) : (RowA.filled password base row).a (password,salt)=row salt := if_pos rfl
  simp only [key]

/-- The target and all other table rows are fixed before the independent row is sampled. -/
theorem probability (password : Password) (base : Tables Password Entropy)
    (original : OracleComp (spec Password Entropy) Result) (target : Key) (limit : Nat)
    (budget : ∀ row : Half → Key,(execute (RowA.filled password base row) original).2.countP
      (QueryCounts.aFor password) ≤ limit) :
    moment (PMF.uniformOfFintype (Half → Key))
      (fun row => if event password target original (RowA.filled password base row) then 1 else 0) ≤
      (limit:ENNReal)/(2^256:ENNReal) := by
  have estimate := QueryHit.probability (0 : Half) (RowA.program password base original) target limit (by
    intro row
    rw [RowA.count]
    exact budget row)
  simp_rw [event_eq] at estimate
  have card : Fintype.card Key=2^256 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Lemma3.bitEquivFin 256)
  simpa only [card,Nat.cast_pow,Nat.cast_ofNat] using estimate

end RowQueryBound

/-! The two terminal inverse keys collide only if the selected independent row hits a fixed target. -/
namespace RowCollision
open Gamma2Model GameExpectation
variable {Password Entropy : Type} [DecidableEq Password]
attribute [local instance] FiniteBits.fintype

def event (focus reference : Password) (round : Nat) (bound : round < 12) (state : State)
    (tables : Tables Password Entropy) : Bool := by
  classical
  exact decide ((execute tables (FinalCut.prepare focus round state bound)).1.key=
    (execute tables (FinalCut.prepare reference round state bound)).1.key)

/-- The reference computation uses no selected-row answer, so its key is a fixed target for that row. -/
theorem covered (focus reference : Password) (different : reference ≠ focus)
    (base : Tables Password Entropy) (round : Nat) (bound : round < 12) (state : State)
    (row : Half → Key) :
    event focus reference round bound state (RowA.filled focus base row)=true →
      RowQueryBound.event focus
        (execute base (FinalCut.prepare reference round state bound)).1.key
        (FinalCut.prepare focus round state bound) (RowA.filled focus base row)=true := by
  classical
  intro same
  have key_equal := same
  simp only [event,decide_eq_true_eq,RowIndependent.cut focus reference different] at key_equal
  obtain ⟨salt,member,answer_equal⟩ := CutKeyFacts.key_queried focus
    (RowA.filled focus base row) round bound state
  unfold RowQueryBound.event
  rw [decide_eq_true_eq]
  refine ⟨salt,List.mem_filterMap.mpr ⟨Point.a focus salt,member,?_⟩,answer_equal.trans key_equal⟩
  exact if_pos rfl

/-- No final-key freshness premise is used: all twelve adaptive A calls are charged, including repeats. -/
theorem probability (focus reference : Password) (different : reference ≠ focus)
    (base : Tables Password Entropy) (round : Nat) (bound : round < 12) (state : State) :
    moment (PMF.uniformOfFintype (Half → Key))
      (fun row => if event focus reference round bound state (RowA.filled focus base row) then 1 else 0) ≤
      ((round+1:Nat):ENNReal)/(2^256:ENNReal) := by
  let target := (execute base (FinalCut.prepare reference round state bound)).1.key
  calc
    _ ≤ moment (PMF.uniformOfFintype (Half → Key)) (fun row =>
      if RowQueryBound.event focus target
        (FinalCut.prepare focus round state bound) (RowA.filled focus base row) then 1 else 0) := by
      apply MomentTools.mono
      intro row
      by_cases same : event focus reference round bound state (RowA.filled focus base row)=true
      · have hit := covered focus reference different base round bound state row same
        change RowQueryBound.event focus target _ _=true at hit
        simp only [same,hit,ite_true,le_refl]
      · rw [if_neg same]
        exact zero_le
    _ ≤ _ := RowQueryBound.probability focus base
      (FinalCut.prepare focus round state bound) target (round+1) (by
        intro row
        exact (CutKeyFacts.count focus (RowA.filled focus base row) round bound state).le)

end RowCollision

/-! Unconditional collision bound for the two actual inverse-prefix keys in the original oracle law. -/
namespace KeyCollision
open Gamma2Model GameExpectation
variable {Password Entropy : Type} [DecidableEq Password] [Fintype Password]
  [Fintype Entropy] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype

/-- Both actual terminal keys are sampled from the original independent ideal functions. -/
theorem probability (focus reference : Password) (different : reference ≠ focus) (round : Nat)
    (bound : round < 12) (state : State) : moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if RowCollision.event focus reference round bound state tables then 1 else 0) ≤
      ((round+1:Nat):ENNReal)/(2^256:ENNReal) := by
  apply RowSampling.probability focus
  intro others
  exact RowCollision.probability focus reference different _ round bound state

/-- In particular all twelve rounds cost only twelve key-hit opportunities. -/
theorem twelve (focus reference : Password) (different : reference ≠ focus) (state : State) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if RowCollision.event focus reference 11 (by omega) state tables then 1 else 0) ≤
      (12:ENNReal)/(2^256:ENNReal) :=
  probability focus reference different 11 (by omega) state

end KeyCollision

/-! An isolated two-candidate observer selects the second H0 before its answer is read. -/
namespace PairMask
open Gamma2Model FinalCut
open G3Fresh G3Programs OracleProjection
variable {Password Entropy : Type}

abbrev HInput := Key × Fin 12 × Half

def selection (reference : Cut Password Entropy) (mask : Half) (focus : Cut Password Entropy) :
    HInput × Option Half :=
  ((focus.key,0,focus.state.1),if focus.key ≠ reference.key then some (reference.state.2 ^^^ mask ^^^ focus.state.2) else none)

variable (focus reference : Password) (round : Nat) (bound : round < 12) (state : State)

def program : OracleComp (spec Password Entropy) (HInput × Option Half) := do
  let referenceCut ← prepare reference round state bound
  let referenceMask ← ask (terminal referenceCut)
  let focusCut ← prepare focus round state bound
  pure (selection referenceCut referenceMask focusCut)

def matching (target : Half) : Finset Half := {target}

/-- The first chain is evaluated completely; the second is stopped strictly before its H0. -/
theorem execution
    (tables : Tables Password Entropy) :
    execute tables (program focus reference round bound state)=
      let referenceCut := (execute tables (prepare reference round state bound)).1
      let focusCut := (execute tables (prepare focus round state bound)).1
      (selection referenceCut (tables.h (referenceCut.key,0,referenceCut.state.1)) focusCut,
        (referenceCut.before ++ [terminal referenceCut]) ++ focusCut.before) := by
  simp only [program,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,execute_pure,answer,terminal,List.append_nil,
    List.singleton_append,FinalCut.trace,List.append_assoc]

/-- Only the already observed reference H0 can conflict; unequal keys exclude that point. -/
theorem certificate (tables : Tables Password Entropy)
    (enabled : (execute tables (program focus reference round bound state)).1.2 ≠ none) :
    embedH (execute tables (program focus reference round bound state)).1.1 ∉
      (execute tables (program focus reference round bound state)).2 := by
  rw [execution] at enabled ⊢
  let refCut := (execute tables (prepare reference round state bound)).1
  let cut := (execute tables (prepare focus round state bound)).1
  change (selection refCut (tables.h (refCut.key,0,refCut.state.1)) cut).2 ≠ none at enabled
  have different : cut.key ≠ refCut.key := by
    by_contra equal
    exact enabled (by simp only [selection,if_neg (not_not.mpr equal)])
  have ref_absent := FinalCut.terminal_absent reference tables round bound state cut.key cut.state.1
  have own_absent := FinalCut.terminal_absent focus tables round bound state cut.key cut.state.1
  have distinct : terminal cut ≠ terminal refCut := by
    intro equal
    change Point.h cut.key 0 cut.state.1=Point.h refCut.key 0 refCut.state.1 at equal
    exact different (Point.h.inj equal).1
  change terminal cut ∉ (refCut.before ++ [terminal refCut]) ++ cut.before
  simp only [List.mem_append,List.mem_singleton,not_or]
  exact ⟨⟨ref_absent,distinct⟩,own_absent⟩

def focused
    (others : OthersH Password Entropy) :=
  FocusedExecution.focused (focusH others.1 others.2.1 others.2.2)
    (program focus reference round bound state)

/-- The focused compiler and actual typed logs establish operational freshness. -/
theorem fresh (others : OthersH Password Entropy) :
    OptionalFresh.EnabledFresh (focused focus reference round bound state others) := by
  apply EnabledProjection.enabled_fresh (focusH others.1 others.2.1 others.2.2)
    (fun h => (⟨others.1,others.2.1,h,others.2.2⟩ : Tables Password Entropy))
    (by intro table point; cases point <;> rfl) (program focus reference round bound state)
    embedH (identifiesH others)
  intro table
  exact certificate focus reference round bound state _

/-- At most one mask completes a left-half match, whether the observer is enabled or not. -/
theorem size (context : Option Half) : (OptionalFresh.optionalSet matching context).card ≤ 1 := by
  cases context <;> simp [OptionalFresh.optionalSet,matching]

end PairMask

/-! The guarded final-mask collision has probability at most 2^-128 without conditioning on the guard. -/
namespace PairMaskBound
open Gamma2Model FinalCut GameExpectation
open PairMask OracleTree OptionalFresh
variable {Password Entropy : Type}
attribute [local instance] FiniteBits.fintype

/-- One XOR mask realizes a prescribed left half. -/
theorem xor_criterion (value target offset : Half) :
    value=target ^^^ offset ↔ offset ^^^ value=target := by
  calc
    _ ↔ offset ^^^ value=offset ^^^ (target ^^^ offset) := (BitVec.xor_right_inj offset).symm
    _ ↔ _ := by rw [BitVec.xor_comm target offset,← BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]

def event (focus reference : Password) (round : Nat) (bound : round < 12) (state : State)
    (tables : Tables Password Entropy) : Bool :=
  rawHit (focused focus reference round bound state (tables.a,tables.b,tables.g)) matching tables.h

/-- The observer's event is the actual left-half equality guarded by unequal terminal keys. -/
theorem actual (focus reference : Password) (round : Nat) (bound : round < 12) (state : State)
    (tables : Tables Password Entropy) :
    event focus reference round bound state tables=
      let referenceCut := (execute tables (prepare reference round state bound)).1
      let focusCut := (execute tables (prepare focus round state bound)).1
      decide (focusCut.key ≠ referenceCut.key ∧ (finish tables focusCut).1=(finish tables referenceCut).1) := by
  unfold event rawHit focused
  rw [FocusedExecution.result_eq (OracleProjection.focusH tables.a tables.b tables.g) tables.h tables
    (by intro point; cases point <;> rfl) (program focus reference round bound state)]
  rw [execution]
  dsimp only
  generalize (execute tables (prepare reference round state bound)).1=referenceCut
  generalize (execute tables (prepare focus round state bound)).1=focusCut
  by_cases different : focusCut.key ≠ referenceCut.key
  · simp only [selection,if_pos different,optionalSet,matching,Finset.mem_singleton]
    rw [decide_eq_decide]
    simp only [finish]
    constructor
    · intro equal
      exact ⟨different,(xor_criterion _ _ _).mp equal⟩
    · intro both
      exact (xor_criterion _ _ _).mpr both.2
  · simp [selection,different,optionalSet]

variable [Fintype Password] [DecidableEq Password] [Fintype Entropy] [DecidableEq Entropy]

/-- Unconditional probability, averaged over every ideal table; no no-key-collision conditioning. -/
theorem probability (focus reference : Password) (round : Nat) (bound : round < 12) (state : State) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if event focus reference round bound state tables then 1 else 0) ≤
      1/(2^128:ENNReal) := by
  have estimate := G3Probability.averaged sampleTables
    (PMF.uniformOfFintype (G3Programs.OthersH Password Entropy))
    (fun others h => (⟨others.1,others.2.1,h,others.2.2⟩ : Tables Password Entropy))
    TableFactors.factor_h (focused focus reference round bound state) matching
    (event focus reference round bound state) (by intro others table; rfl)
    (fresh focus reference round bound state) (fun _ => 1) (by
      intro others table
      exact size _)
  simpa only [G3Probability.card_bits,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,
    MomentTools.constant] using estimate

end PairMaskBound

/-! Actual inverse left-half collisions are covered by a key collision or a fresh-mask hit. -/
namespace InverseCollision
open Gamma2Model FinalCut GameExpectation
variable {Password Entropy : Type} [DecidableEq Password]

def event (focus reference : Password) (round : Nat) (bound : round < 12) (state : State)
    (tables : Tables Password Entropy) : Bool :=
  decide ((execute tables (finalize focus (round+1) state (by omega))).1.1.1=
    (execute tables (finalize reference (round+1) state (by omega))).1.1.1)

omit [DecidableEq Password] in
/-- Cover the actual completed inverses, without conditioning either summand on the other. -/
theorem covered (focus reference : Password) (round : Nat) (bound : round < 12) (state : State)
    (tables : Tables Password Entropy) (same : event focus reference round bound state tables=true) :
    RowCollision.event focus reference round bound state tables=true ∨
      PairMaskBound.event focus reference round bound state tables=true := by
  let refCut := (execute tables (prepare reference round state bound)).1
  let cut := (execute tables (prepare focus round state bound)).1
  simp only [event,decide_eq_true_eq] at same
  rw [FinalCut.finalized focus tables round bound state,FinalCut.finalized reference tables round bound state] at same
  change (finish tables cut).1=(finish tables refCut).1 at same
  by_cases equal : cut.key=refCut.key
  · exact Or.inl (by simpa only [RowCollision.event,decide_eq_true_eq] using equal)
  · apply Or.inr
    rw [PairMaskBound.actual]
    exact decide_eq_true (And.intro equal same)

variable [Fintype Password] [Fintype Entropy] [DecidableEq Entropy]

/-- The two estimates use their own valid integration orders and are added only afterwards. -/
theorem probability (focus reference : Password) (different : reference ≠ focus) (round : Nat)
    (bound : round < 12) (state : State) : moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if event focus reference round bound state tables then 1 else 0) ≤
      ((round+1:Nat):ENNReal)/(2^256:ENNReal)+1/(2^128:ENNReal) := by
  calc
    _ ≤ moment sampleTables (fun tables =>
        (if RowCollision.event focus reference round bound state tables then 1 else 0)+
        (if PairMaskBound.event focus reference round bound state tables then 1 else 0)) := by
      apply MomentTools.mono
      intro tables
      by_cases same : event focus reference round bound state tables=true
      · obtain hit | hit := covered focus reference round bound state tables same
        · simp only [same,hit,ite_true]
          exact le_add_right le_rfl
        · simp only [same,hit,ite_true]
          exact le_add_left le_rfl
      · rw [if_neg same]
        exact zero_le
    _ = _ := MomentTools.add _ _ _
    _ ≤ _ := add_le_add (KeyCollision.probability focus reference different round bound state)
      (PairMaskBound.probability focus reference round bound state)

/-- The exact two terms used by Proposition G8, for all twelve rounds. -/
theorem twelve (focus reference : Password) (different : reference ≠ focus) (state : State) :
    moment (sampleTables (Password := Password) (Entropy := Entropy))
      (fun tables => if event focus reference 11 (by omega) state tables then 1 else 0) ≤
      1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal) := by
  have simpaTerm := probability (Entropy := Entropy) focus reference different 11 (by omega) state
  (try simp only [add_comm] at simpaTerm ⊢)
  exact simpaTerm

end InverseCollision

/-! Entropy equality implies actual left-half equality only through the proved source projection. -/
namespace EntropyCollision
open Gamma2Model GameExpectation
variable {Password E V : Type} [DecidableEq Password] [DecidableEq E]
attribute [local irreducible] finalize

def event (coordinates : (E × V) ≃ State) (focus reference : Password) (state : State)
    (tables : Tables Password E) : Bool :=
  decide (Theorem3.entropy coordinates (execute tables (finalize focus 12 state (by omega))).1.1=
    Theorem3.entropy coordinates (execute tables (finalize reference 12 state (by omega))).1.1)

omit [DecidableEq Password] in
/-- Arbitrary coordinates do not suffice: the leading 128 entropy bits must project to the left half. -/
theorem covered (coordinates : (E × V) ≃ State) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (focus reference : Password) (state : State) (tables : Tables Password E)
    (same : event coordinates focus reference state tables=true) :
    InverseCollision.event focus reference 11 (by omega) state tables=true := by
  simp only [event,decide_eq_true_eq] at same
  have half_equal := congrArg firstHalf same
  simp only [projects] at half_equal
  exact decide_eq_true half_equal

variable [Fintype Password] [Fintype E]

/-- This is the entropy-collision term of G8, independent of the verifier-oracle test. -/
theorem probability (coordinates : (E × V) ≃ State) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (focus reference : Password) (different : reference ≠ focus) (state : State) :
    moment (sampleTables (Password := Password) (Entropy := E))
      (fun tables => if event coordinates focus reference state tables then 1 else 0) ≤
      1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal) := by
  calc
    _ ≤ moment sampleTables (fun tables =>
      if InverseCollision.event focus reference 11 (by omega) state tables then 1 else 0) := by
      apply MomentTools.mono
      intro tables
      by_cases same : event coordinates focus reference state tables=true
      · simp only [same,covered coordinates firstHalf projects focus reference state tables same,ite_true,le_refl]
      · rw [if_neg same]
        exact zero_le
    _ ≤ _ := InverseCollision.twelve focus reference different state

/-- The normative 128/160/192/224-bit source coordinates discharge that projection premise. -/
theorem short_source (tail verifier : Nat) (length : tail+verifier=128) (focus reference : Password)
    (different : reference ≠ focus) (state : State) : moment (sampleTables (Password := Password) (Entropy := BitVec (128+tail)))
      (fun tables => if event (ShortSourceCoordinates.state tail verifier length) focus reference state tables then 1 else 0) ≤
      1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal) := by
  letI := FiniteBits.fintype (128+tail)
  exact probability (ShortSourceCoordinates.state tail verifier length)
    (ShortSourceCoordinates.firstHalf tail)
    (ShortSourceCoordinates.projects tail verifier length) focus reference different state

end EntropyCollision

/-! A fixed wrong password passes only through a fresh verifier hit or an entropy collision. -/
namespace FalsePass
open Gamma2Model CryptoInputs GameExpectation CandidateData
variable {Password E V R : Type} [Fintype Password] [DecidableEq Password]
  [Fintype E] [Nonempty E] [DecidableEq E] [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] finalize

def entropyEvent (coordinates : (E × V) ≃ State) (focus real : Password) (container : State)
    (other : ABH Password) : Bool :=
  decide ((fields coordinates focus other container).1=(fields coordinates real other container).1)

omit [Nonempty E] [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R] in
/-- The pairwise collision bound applies to exactly these pure candidate inverses under the ABH law. -/
theorem collision (coordinates : (E × V) ≃ State) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (focus real : Password) (different : real ≠ focus) (container : State) :
    moment (PMF.uniformOfFintype (ABH Password))
      (fun other => if entropyEvent coordinates focus real container other then 1 else 0) ≤
      1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal) := by
  have estimate := EntropyCollision.probability coordinates firstHalf projects focus real different container
  rw [factor_g,MomentTools.bind] at estimate
  simp_rw [moment_map,Function.comp_def,EntropyCollision.event,
    Theorem3.entropy,CipherExecution.inverse] at estimate
  change moment (PMF.uniformOfFintype (ABH Password))
    (fun other => moment (PMF.uniformOfFintype (E → Hash))
      (fun _ => if entropyEvent coordinates focus real container other then 1 else 0)) ≤ _ at estimate
  simpa only [MomentTools.constant] using estimate

/-- The bound is unconditional for a fixed actual password and any distinct fixed tested password. -/
theorem probability (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (focus real : Password) (different : real ≠ focus) (container : State) :
    moment (PMF.uniformOfFintype (ABH Password)) (fun other =>
      moment (PMF.uniformOfFintype (E → Hash))
        (fun g => if passes coordinates hash real focus other container g then 1 else 0)) ≤
      1/(Fintype.card V:ENNReal)+1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal) := by
  have fixed_bound (other : ABH Password) :
      moment (PMF.uniformOfFintype (E → Hash))
        (fun g => if passes coordinates hash real focus other container g then 1 else 0) ≤
      (if entropyEvent coordinates focus real container other then 1 else 0)+1/(Fintype.card V:ENNReal) := by
    by_cases same : (fields coordinates focus other container).1=(fields coordinates real other container).1
    · have at_most_one : moment (PMF.uniformOfFintype (E → Hash))
        (fun g => if passes coordinates hash real focus other container g then 1 else 0) ≤ 1 := by
        apply MomentTools.bounded
        intro g
        split_ifs <;> simp only [le_refl,zero_le]
      simp only [entropyEvent,same,decide_true,ite_true]
      exact at_most_one.trans (le_add_right le_rfl)
    · rw [CandidateData.distinct_probability coordinates hash real focus other container same]
      simp only [entropyEvent,same,decide_false,Bool.false_eq_true,ite_false,zero_add,le_refl]
  calc
    _ ≤ moment (PMF.uniformOfFintype (ABH Password)) (fun other =>
      (if entropyEvent coordinates focus real container other then 1 else 0)+1/(Fintype.card V:ENNReal)) :=
      MomentTools.mono _ _ _ fixed_bound
    _ = _ := MomentTools.add _ _ _
    _ ≤ (1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal))+1/(Fintype.card V:ENNReal) := by
      rw [MomentTools.constant]
      exact add_le_add (collision coordinates firstHalf projects focus real different container) le_rfl
    _ = _ := by simp only [add_assoc,add_comm]

end FalsePass

/-! G8's per-real-password first-pass lower bound, including the free fallback case. -/
namespace FirstPassSource
open Gamma2Model CryptoInputs CandidateData
open GameExpectation ProbabilityTools
variable {Password E V R : Type} [Fintype Password] [DecidableEq Password]
  [Fintype E] [Nonempty E] [DecidableEq E] [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

abbrev World (Password E : Type) := ABH Password × (E → Hash)

def law : PMF (World Password E) :=
  independentPair (PMF.uniformOfFintype (ABH Password)) (PMF.uniformOfFintype (E → Hash))

def delta : ENNReal := 1/(Fintype.card V:ENNReal)+1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal)

/-- A fixed preceding list gives a finite union; its tests may be arbitrarily correlated. -/
theorem before_bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1) (real : Password)
    (container : State) (earlier : List Password) (no_real : real ∉ earlier)
    (win : World Password E → Bool)
    (rescued : ∀ world,(∀ candidate ∈ earlier, passes coordinates hash real candidate world.1 container world.2=false) → win world=true) :
    1-(earlier.length:ENNReal)*delta (V := V) ≤ moment law (fun world => if win world then 1 else 0) := by
  let bad (i : Fin earlier.length) (world : World Password E) :=
    passes coordinates hash real (earlier.get i) world.1 container world.2
  apply FirstPass.probability law win earlier.length bad (delta (V := V))
  · intro world
    by_cases failed : ∃ i,bad i world=true
    · exact Or.inr failed
    · apply Or.inl
      apply rescued world
      intro candidate member
      obtain ⟨i,equal⟩ := List.mem_iff_get.mp member
      cases hit : passes coordinates hash real candidate world.1 container world.2 with
      | false => rfl
      | true =>
        exact False.elim (failed ⟨i,by simpa only [bad,equal] using hit⟩)
  · intro i
    have different : real ≠ earlier.get i := by
      intro equal
      exact no_real (equal.symm ▸ List.get_mem earlier i)
    have estimate := FalsePass.probability coordinates hash firstHalf projects (earlier.get i) real different container
    simpa only [law,independentPair,MomentTools.bind,moment_map,Function.comp_def,bad,delta] using estimate

/-- A real tested candidate is returned unless an earlier candidate passes. -/
theorem tested (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (real fallback : Password) (container : State) (earlier later : List Password)
    (no_real : real ∉ earlier) : 1-(earlier.length:ENNReal)*delta (V := V) ≤ moment law (fun world =>
      if decide (FirstPass.choose
        (fun candidate => passes coordinates hash real candidate world.1 container world.2)
        fallback (earlier ++ real :: later)=real) then 1 else 0) := by
  apply before_bound coordinates hash firstHalf projects real container earlier no_real
  intro world fail
  apply decide_eq_true
  exact FirstPass.selected _ fallback real earlier later fail
    (CandidateData.real_passes coordinates hash real world.1 container world.2)

/-- The final untested candidate incurs only the false-pass losses of preceding tests. -/
theorem fallback (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1) (real : Password)
    (container : State) (earlier : List Password) (no_real : real ∉ earlier) :
    1-(earlier.length:ENNReal)*delta (V := V) ≤ moment law (fun world =>
      if decide (FirstPass.choose
        (fun candidate => passes coordinates hash real candidate world.1 container world.2)
        real earlier=real) then 1 else 0) := by
  apply before_bound coordinates hash firstHalf projects real container earlier no_real
  intro world fail
  exact decide_eq_true (FirstPass.fallback _ real earlier fail)

end FirstPassSource

/-! Per-real-password success of the concrete oracle attack in the exact programmed experiment. -/
namespace G8Conditional
open Gamma2Model CryptoInputs CandidateData GameExpectation
variable {Password E V R : Type} [DecidableEq E] [DecidableEq V]
attribute [local irreducible] finalize

/-- Replacing G at the genuine source does not affect any candidate's ABH inverse. -/
theorem test (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (real candidate : Password)
    (other : ABH Password) (container : State) (g : E → Hash) :
    G8Attack.test coordinates hash container
      (tables other (programmed coordinates hash real other container g)) candidate=
      passes coordinates hash real candidate other container g := by
  unfold G8Attack.test
  rw [CandidateData.actual]
  rfl

/-- The actual adaptive stopping attack has the same output as the pure first-pass search. -/
theorem result (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (real fallback : Password)
    (candidates : List Password) (other : ABH Password) (container : State) (g : E → Hash) :
    (execute (tables other (programmed coordinates hash real other container g))
      (G8Attack.attack coordinates hash candidates fallback container)).1=
      FirstPass.choose
        (fun candidate => passes coordinates hash real candidate other container g) fallback candidates := by
  rw [G8Attack.attack_result]
  have same : G8Attack.test coordinates hash container
      (tables other (programmed coordinates hash real other container g))=
      fun candidate => passes coordinates hash real candidate other container g := by
    funext candidate
    exact test coordinates hash real candidate other container g
  rw [same]

variable [Fintype Password] [DecidableEq Password] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- Conditional on a fixed genuine tested candidate, only preceding false passes can spoil success. -/
theorem tested (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (real fallback : Password) (container : State) (earlier later : List Password)
    (no_real : real ∉ earlier) : 1-(earlier.length:ENNReal)*FirstPassSource.delta (V := V) ≤
      moment FirstPassSource.law (fun world =>
        if decide ((execute (tables world.1 (programmed coordinates hash real world.1 container world.2))
          (G8Attack.attack coordinates hash (earlier ++ real :: later) fallback container)).1=real)
        then 1 else 0) := by
  simpa only [result] using FirstPassSource.tested coordinates hash firstHalf projects
    real fallback container earlier later no_real

/-- The same bound covers the final free untested candidate. -/
theorem fallback (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1) (real : Password)
    (container : State) (earlier : List Password) (no_real : real ∉ earlier) :
    1-(earlier.length:ENNReal)*FirstPassSource.delta (V := V) ≤
      moment FirstPassSource.law (fun world =>
        if decide ((execute (tables world.1 (programmed coordinates hash real world.1 container world.2))
          (G8Attack.attack coordinates hash earlier real container)).1=real)
        then 1 else 0) := by
  simpa only [result] using FirstPassSource.fallback coordinates hash firstHalf projects
    real container earlier no_real

end G8Conditional

/-! A fixed injective order supplies exactly m tested candidates and one distinct free guess. -/
namespace RankedCandidates
variable {Password : Type} {m : Nat}

def tested (order : Fin (m+1) → Password) : List Password :=
  List.ofFn (fun i : Fin m => order i.castSucc)

def fallback (order : Fin (m+1) → Password) : Password := order (Fin.last m)

/-- Split the tested list immediately before a given tested rank. -/
theorem split (order : Fin (m+1) → Password) (i : Fin m) :
    tested order=(tested order).take i.val ++ order i.castSucc :: (tested order).drop (i.val+1) := by
  have within : i.val < (tested order).length := by simpa only [tested,List.length_ofFn] using i.isLt
  have decomposition := List.take_append_drop (i.val+1) (tested order)
  rw [List.take_succ_eq_append_getElem within,List.append_assoc,List.singleton_append] at decomposition
  simpa only [tested,List.getElem_ofFn,Fin.eta] using decomposition.symm

/-- No earlier tested candidate equals the selected rank, including the free last rank. -/
theorem absent (order : Fin (m+1) → Password) (injective : Function.Injective order)
    (rank : Fin (m+1)) : order rank ∉ (tested order).take rank.val := by
  intro member
  obtain ⟨i,within,equal⟩ := List.mem_take_iff_getElem.mp member
  have below_m : i < m := by simpa only [tested,List.length_ofFn] using lt_of_lt_of_le within (Nat.min_le_right _ _)
  have equal_order : order (Fin.castSucc (⟨i,below_m⟩ : Fin m))=order rank := by
    simpa only [tested,List.getElem_ofFn] using equal
  have positions := congrArg Fin.val (injective equal_order)
  change i=rank.val at positions
  have before := lt_of_lt_of_le within (Nat.min_le_left _ _)
  omega

/-- Each rank has exactly rank.val preceding tests. -/
theorem earlier_length (order : Fin (m+1) → Password) (rank : Fin (m+1)) :
    ((tested order).take rank.val).length=rank.val := by
  simp only [List.length_take,tested,List.length_ofFn]
  exact Nat.min_eq_left (by omega)

/-- The final free guess is absent from all m tests. -/
theorem last_absent (order : Fin (m+1) → Password) (injective : Function.Injective order) :
    fallback order ∉ tested order := by
  have none_before := absent order injective (Fin.last m)
  have length : (tested order).length=m := List.length_ofFn
  have take_all : (tested order).take m=tested order := by
    simpa only [length] using (List.take_length (l := tested order))
  simpa only [Fin.val_last,take_all,fallback] using none_before

/-- A rank-wise success estimate gives its weighted lower bound without assuming independence. -/
theorem weighted_lower [Fintype Password] (passwords : PMF Password) (order : Fin (m+1) → Password)
    (injective : Function.Injective order) (loss : ENNReal) (success : Password → ENNReal)
    (ranked : ∀ rank, 1-(rank.val:ENNReal)*loss ≤ success (order rank)) :
    (∑ rank : Fin (m+1), passwords (order rank)*(1-(rank.val:ENNReal)*loss)) ≤
      GameExpectation.moment passwords success := by
  calc
    _ ≤ ∑ rank : Fin (m+1), passwords (order rank)*success (order rank) := by
      apply Finset.sum_le_sum
      intro rank _
      exact mul_le_mul_right (ranked rank) _
    _ ≤ _ := by
      simpa only [GameExpectation.moment, tsum_fintype] using
        ENNReal.tsum_comp_le_tsum_of_injective injective
          (fun real => passwords real*success real)

/-- Replacing each selected rank by the largest rank yields the common multiplicative loss. -/
theorem coarse_lower [Fintype Password] (passwords : PMF Password) (order : Fin (m+1) → Password)
    (loss : ENNReal) (success : Password → ENNReal)
    (weighted : (∑ rank : Fin (m+1), passwords (order rank)*(1-(rank.val:ENNReal)*loss)) ≤ GameExpectation.moment passwords success) :
    (∑ rank : Fin (m+1), passwords (order rank))*(1-(m:ENNReal)*loss) ≤
      GameExpectation.moment passwords success := by
  calc
    _ = ∑ rank : Fin (m+1), passwords (order rank)*(1-(m:ENNReal)*loss) :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ rank : Fin (m+1), passwords (order rank)*(1-(rank.val:ENNReal)*loss) := by
      apply Finset.sum_le_sum
      intro rank _
      have index_bound : (rank.val:ENNReal) ≤ (m:ENNReal) := by
        exact_mod_cast (show rank.val ≤ m by omega)
      have losses : (rank.val:ENNReal)*loss ≤ (m:ENNReal)*loss := by
        simpa only [mul_comm] using mul_le_mul_right index_bound loss
      exact mul_le_mul_right (tsub_le_tsub_left losses 1) _
    _ ≤ _ := weighted

end RankedCandidates

/-! Rank-by-rank and weighted success of the concrete G8 oracle attack. -/
namespace RankedSearch
open Gamma2Model CryptoInputs CandidateData GameExpectation
variable {Password E V R : Type} {m : Nat} [DecidableEq E] [DecidableEq V]
  [Fintype Password] [DecidableEq Password] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

def conditional (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (order : Fin (m+1) → Password) (container : State) (real : Password) : ENNReal :=
  moment FirstPassSource.law (fun world =>
    if decide ((execute (tables world.1 (programmed coordinates hash real world.1 container world.2))
      (G8Attack.attack coordinates hash (RankedCandidates.tested order)
        (RankedCandidates.fallback order) container)).1=real) then 1 else 0)

/-- Each selected rank loses at most one delta per preceding tested candidate. -/
theorem ranked (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (order : Fin (m+1) → Password) (injective : Function.Injective order) (container : State)
    (rank : Fin (m+1)) : 1-(rank.val:ENNReal)*FirstPassSource.delta (V := V) ≤
      conditional coordinates hash order container (order rank) := by
  by_cases tested_rank : rank.val < m
  · let i : Fin m := ⟨rank.val,tested_rank⟩
    have same_rank : i.castSucc=rank := Fin.ext rfl
    have split : RankedCandidates.tested order=
        (RankedCandidates.tested order).take rank.val ++ order rank ::
          (RankedCandidates.tested order).drop (rank.val+1) := by
      simpa only [same_rank] using RankedCandidates.split order i
    have estimate := G8Conditional.tested coordinates hash firstHalf projects
      (order rank) (RankedCandidates.fallback order) container
      ((RankedCandidates.tested order).take rank.val)
      ((RankedCandidates.tested order).drop (rank.val+1))
      (RankedCandidates.absent order injective rank)
    rw [← split,RankedCandidates.earlier_length] at estimate
    exact estimate
  · have last : rank=Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst rank
    have estimate := G8Conditional.fallback coordinates hash firstHalf projects
      (RankedCandidates.fallback order) container (RankedCandidates.tested order)
      (RankedCandidates.last_absent order injective)
    (try simp only [conditional,Fin.val_last,RankedCandidates.tested,List.length_ofFn, RankedCandidates.fallback] at estimate ⊢)
    exact estimate

/-- Sum over distinct selected ranks; unselected genuine passwords contribute a nonnegative mass. -/
theorem weighted (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF Password) (order : Fin (m+1) → Password) (injective : Function.Injective order)
    (container : State) :
    (∑ rank : Fin (m+1),passwords (order rank)*
      (1-(rank.val:ENNReal)*FirstPassSource.delta (V := V))) ≤
      moment passwords (conditional coordinates hash order container) := by
  exact RankedCandidates.weighted_lower passwords order injective _ _
    (ranked coordinates hash firstHalf projects order injective container)

/-- The simpler multiplicative lower bound uses at most m preceding candidates at every selected rank. -/
theorem coarse (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF Password) (order : Fin (m+1) → Password) (injective : Function.Injective order)
    (container : State) :
    (∑ rank : Fin (m+1),passwords (order rank))*(1-(m:ENNReal)*FirstPassSource.delta (V := V)) ≤
      moment passwords (conditional coordinates hash order container) := by
  exact RankedCandidates.coarse_lower passwords order _ _
    (weighted coordinates hash firstHalf projects passwords order injective container)

end RankedSearch

/-! Exact G1 transport of the concrete matching attack back to the original source experiment. -/
namespace G8Transport
open Gamma2Model CryptoInputs GameExpectation ProbabilityTools

/-- Exchange independent discrete nonnegative expectations without any finite-cost premise. -/
theorem comm {A B : Type} (left : PMF A) (right : PMF B) (value : A → B → ENNReal) :
    moment left (fun a => moment right (value a))=moment right (fun b => moment left (fun a => value a b)) := by
  simp only [moment,← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro a
  exact mul_left_comm _ _ _

variable {N m : Nat} {E V R : Type} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] finalize

/-- Preserve the actual attack and all correlations through G1; only independent draw order changes. -/
theorem source (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (passwords : PMF (Fin N))
    (order : Fin (m+1) → Fin N) :
    (Theorem3.original coordinates hash passwords
      (G8Attack.attack coordinates hash (RankedCandidates.tested order)
        (RankedCandidates.fallback order))) true=
      moment (PMF.uniformOfFintype State)
        (fun container => moment passwords (RankedSearch.conditional coordinates hash order container)) := by
  rw [Theorem3.resampling,← MomentTools.bool]
  unfold Theorem3.programmed
  rw [MomentTools.bind]
  simp_rw [MomentTools.bind,moment_map,Function.comp_def]
  rw [uniform_product (α := State) (β := E → Hash)]
  simp_rw [independentPair,MomentTools.bind,moment_map,Function.comp_def]
  calc
    _ = moment passwords (fun real => moment (PMF.uniformOfFintype State)
        (fun container => RankedSearch.conditional coordinates hash order container real)) := by
      apply congrArg (moment passwords)
      funext real
      change moment (PMF.uniformOfFintype (ABH (Fin N)))
        (fun other => moment (PMF.uniformOfFintype State) (fun container =>
          moment (PMF.uniformOfFintype (E → Hash)) (fun g =>
            if decide ((execute (tables other (CandidateData.programmed coordinates hash real other container g))
              (G8Attack.attack coordinates hash (RankedCandidates.tested order)
                (RankedCandidates.fallback order) container)).1=real) then 1 else 0)))=_
      rw [comm]
      simp only [RankedSearch.conditional,FirstPassSource.law,independentPair,
        MomentTools.bind,moment_map,Function.comp_def]
    _ = _ := comm _ _ _

end G8Transport

/-! Initial ranked dictionaries and exact saturation at a finite password-domain boundary. -/
namespace PasswordPrefix
variable {N m : Nat}

def order (within : m+1 ≤ N) (index : Fin (m+1)) : Fin N := ⟨index.val,lt_of_lt_of_le index.isLt within⟩

/-- Rank inclusion never identifies two selected candidate passwords. -/
theorem injective (within : m+1 ≤ N) : Function.Injective (order within) := by
  intro first second equal
  exact Fin.ext (congrArg (fun index : Fin N => index.val) equal)

/-- The selected rank masses are precisely the top prefix used by the supplement. -/
theorem mass (p : Fin N → ENNReal) (within : m+1 ≤ N) :
    (∑ rank : Fin (m+1),p (order within rank))=RankedMass.top p (m+1) := by
  have shape : Finset.univ.image (order within)=Finset.univ.filter (fun index : Fin N => index.val < m+1) := by
    ext index
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter]
    constructor
    · rintro ⟨rank,equal⟩
      rw [← equal]
      exact rank.isLt
    · intro below
      exact ⟨⟨index.val,below⟩,Fin.ext rfl⟩
  rw [RankedMass.top,← shape,Finset.sum_image]
  intro first _ second _ equal
  exact injective within equal

def count (m N : Nat) : Nat := min m (N-1)

/-- At most N-1 actual tests suffice; the Nth password is the free final guess. -/
theorem within (positive : 0 < N) : count m N+1 ≤ N := by
  unfold count
  omega

/-- Saturation loses no selected probability mass. -/
theorem saturated (p : Fin N → ENNReal) (positive : 0 < N) :
    RankedMass.top p (count m N+1)=RankedMass.top p (m+1) := by
  unfold RankedMass.top
  congr 1
  ext index
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  unfold count
  have bound := index.isLt
  omega

end PasswordPrefix

/-! Proposition G8: the actual matching attack, source-game success and hard query budgets. -/
namespace G8
open Gamma2Model GameExpectation
variable {N m : Nat} {E V R : Type} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- The more precise weighted loss holds for any fixed injective candidate order. -/
theorem weighted (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (order : Fin (m+1) → Fin N) (injective : Function.Injective order) :
    (∑ rank : Fin (m+1),passwords (order rank)*
      (1-(rank.val:ENNReal)*FirstPassSource.delta (V := V))) ≤
    (Theorem3.original coordinates hash passwords
      (G8Attack.attack coordinates hash (RankedCandidates.tested order)
        (RankedCandidates.fallback order))) true := by
  rw [G8Transport.source]
  calc
    _ = moment (PMF.uniformOfFintype State) (fun _ =>
      ∑ rank : Fin (m+1),passwords (order rank)*
        (1-(rank.val:ENNReal)*FirstPassSource.delta (V := V))) :=
      (MomentTools.constant _ _).symm
    _ ≤ _ := MomentTools.mono _ _ _
      (fun container => RankedSearch.weighted coordinates hash firstHalf projects passwords order injective container)

/-- The common multiplicative loss holds in the original source game, not only the programmed game. -/
theorem coarse (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (order : Fin (m+1) → Fin N) (injective : Function.Injective order) :
    (∑ rank : Fin (m+1),passwords (order rank))*
      (1-(m:ENNReal)*FirstPassSource.delta (V := V)) ≤
    (Theorem3.original coordinates hash passwords
      (G8Attack.attack coordinates hash (RankedCandidates.tested order)
        (RankedCandidates.fallback order))) true := by
  rw [G8Transport.source]
  calc
    _ = moment (PMF.uniformOfFintype State) (fun _ =>
      (∑ rank : Fin (m+1),passwords (order rank))*
        (1-(m:ENNReal)*FirstPassSource.delta (V := V))) :=
      (MomentTools.constant _ _).symm
    _ ≤ _ := MomentTools.mono _ _ _
      (fun container => RankedSearch.coarse coordinates hash firstHalf projects passwords order injective container)

def attack (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (m : Nat) (positive : 0 < N) :=
  let order := PasswordPrefix.order (PasswordPrefix.within (m := m) positive)
  G8Attack.attack coordinates hash (RankedCandidates.tested order)
    (RankedCandidates.fallback order)

/-- Arbitrary requested budgets are covered, including empty testing and finite dictionary saturation. -/
theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top passwords (m+1)*(1-(m:ENNReal)*FirstPassSource.delta (V := V)) ≤
      (Theorem3.original coordinates hash passwords (attack coordinates hash m positive)) true := by
  let k := PasswordPrefix.count m N
  have within : k+1 ≤ N := PasswordPrefix.within positive
  let order := PasswordPrefix.order within
  have estimate := coarse coordinates hash firstHalf projects passwords order (PasswordPrefix.injective within)
  rw [PasswordPrefix.mass,PasswordPrefix.saturated passwords positive] at estimate
  have index_bound : (k:ENNReal) ≤ (m:ENNReal) := by exact_mod_cast (Nat.min_le_left m (N-1))
  have loss : (k:ENNReal)*FirstPassSource.delta (V := V) ≤
      (m:ENNReal)*FirstPassSource.delta (V := V) := by
    simpa only [mul_comm] using mul_le_mul_right index_bound (FirstPassSource.delta (V := V))
  exact (mul_le_mul_right (tsub_le_tsub_left loss 1) _).trans estimate

omit [Fintype E] [Nonempty E] [DecidableEq E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] in
/-- The same attack always respects the exact advertised oracle-query caps. -/
theorem budgets (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (m : Nat) (positive : 0 < N) (tables : Tables (Fin N) E) (container : State) :
    let queries := (execute tables (attack coordinates hash m positive container)).2
    queries.countP QueryCounts.isA ≤ 12*m ∧ queries.countP QueryCounts.isB ≤ 11*m+1 ∧
      queries.countP QueryCounts.isH ≤ 12*m ∧ queries.countP InverseCounts.isG ≤ m := by
  let k := PasswordPrefix.count m N
  let order := PasswordPrefix.order (PasswordPrefix.within (m := m) positive)
  have estimate := G8Attack.counts coordinates hash tables
    (RankedCandidates.fallback order) (RankedCandidates.tested order) container
  have length : (RankedCandidates.tested order).length=k := List.length_ofFn
  rw [length] at estimate
  have limit : k ≤ m := Nat.min_le_left m (N-1)
  change (execute tables (G8Attack.attack coordinates hash
    (RankedCandidates.tested order) (RankedCandidates.fallback order) container)).2.countP QueryCounts.isA ≤ 12*m ∧
    (execute tables (G8Attack.attack coordinates hash
      (RankedCandidates.tested order) (RankedCandidates.fallback order) container)).2.countP QueryCounts.isB ≤ 11*m+1 ∧
    (execute tables (G8Attack.attack coordinates hash
      (RankedCandidates.tested order) (RankedCandidates.fallback order) container)).2.countP QueryCounts.isH ≤ 12*m ∧
    (execute tables (G8Attack.attack coordinates hash
      (RankedCandidates.tested order) (RankedCandidates.fallback order) container)).2.countP InverseCounts.isG ≤ m
  omega

end G8

/-! The precise rank-weighted G8 lower bound, including finite dictionary saturation. -/
namespace G8Weighted
open Gamma2Model
variable {N : Nat} {E V R : Type} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- Prefix notation denotes exactly the source's sum of per-rank false-pass losses. -/
theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top (fun rank => passwords rank*
      (1-(rank.val:ENNReal)*FirstPassSource.delta (V := V))) (m+1) ≤
      (Theorem3.original coordinates hash passwords (G8.attack coordinates hash m positive)) true := by
  let k := PasswordPrefix.count m N
  have within : k+1 ≤ N := PasswordPrefix.within positive
  let order := PasswordPrefix.order within
  have estimate := G8.weighted coordinates hash firstHalf projects passwords order
    (PasswordPrefix.injective within)
  have sum_equal : (∑ rank : Fin (k+1),passwords (order rank)*
      (1-(rank.val:ENNReal)*FirstPassSource.delta (V := V)))=
      RankedMass.top (fun rank => passwords rank*
        (1-(rank.val:ENNReal)*FirstPassSource.delta (V := V))) (k+1) :=
    PasswordPrefix.mass (fun rank : Fin N => passwords rank*
      (1-(rank.val:ENNReal)*FirstPassSource.delta (V := V))) within
  rw [sum_equal,PasswordPrefix.saturated _ positive] at estimate
  exact estimate

end G8Weighted

/-! Proposition G8 at the actual short-source entropy/verifier bit widths. -/
namespace G8Bits
open Gamma2Model
variable {N : Nat}
attribute [local instance] FiniteBits.fintype

/-- Actual high/low bit coordinates give delta=2^-r+2^-128+12*2^-256, with source-game success. -/
theorem bound (tail verifier suffix : Nat) (state_length : tail+verifier=128)
    (hash_length : verifier+suffix=256) (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top passwords (m+1)*
      (1-(m:ENNReal)*(1/(2^verifier:ENNReal)+1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal))) ≤
      (Theorem3.original (ShortSourceCoordinates.state tail verifier state_length)
        (BitPacking.hash verifier suffix hash_length) passwords
        (G8.attack (ShortSourceCoordinates.state tail verifier state_length)
          (BitPacking.hash verifier suffix hash_length) m positive)) true := by
  have estimate := G8.bound (ShortSourceCoordinates.state tail verifier state_length)
    (BitPacking.hash verifier suffix hash_length) (ShortSourceCoordinates.firstHalf tail)
    (ShortSourceCoordinates.projects tail verifier state_length) passwords m positive
  (try simp only [FirstPassSource.delta,G3Probability.card_bits,Nat.cast_pow,Nat.cast_ofNat] at estimate ⊢)
  exact estimate

/-- The specialized attack has the same hard caps on every ideal-function table. -/
theorem budgets (tail verifier suffix : Nat) (state_length : tail+verifier=128)
    (hash_length : verifier+suffix=256) (m : Nat) (positive : 0 < N)
    (tables : Tables (Fin N) (BitVec (128+tail))) (container : State) :
    let queries := (execute tables
      (G8.attack (ShortSourceCoordinates.state tail verifier state_length)
        (BitPacking.hash verifier suffix hash_length) m positive container)).2
    queries.countP QueryCounts.isA ≤ 12*m ∧ queries.countP QueryCounts.isB ≤ 11*m+1 ∧
      queries.countP QueryCounts.isH ≤ 12*m ∧ queries.countP InverseCounts.isG ≤ m :=
  G8.budgets _ _ m positive tables container

end G8Bits

end
end MhfeLean
