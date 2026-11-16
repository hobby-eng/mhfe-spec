import Mathlib.Data.Fin.Tuple.Sort
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # Finite password labels and their ranked representation

The equivalence ranges over the whole admissible password alphabet, including
zero-prior labels an adversary can query. It is not a restriction to dictionary
support. Byte encodings and their lengths belong to the labels; relabeling only
changes their mathematical names.
-/

namespace PasswordDomains
open Gamma2Model ProbabilityTools
variable {Password Ranked Entropy Result : Type}

/-- Only the A-query password field is renamed. -/
def point (labels : Password ≃ Ranked) : Point Password Entropy → Point Ranked Entropy
  | .a password salt => .a (labels password) salt
  | .b round right => .b round right
  | .h key round right => .h key round right
  | .g entropy => .g entropy

def tables (labels : Password ≃ Ranked) : Tables Password Entropy ≃ Tables Ranked Entropy where
  toFun crypto := ⟨fun input => crypto.a (labels.symm input.1,input.2),crypto.b,crypto.h,crypto.g⟩
  invFun crypto := ⟨fun input => crypto.a (labels input.1,input.2),crypto.b,crypto.h,crypto.g⟩
  left_inv crypto := by
    cases crypto
    dsimp only
    congr 1
    funext input
    simp only [Equiv.symm_apply_apply]
  right_inv crypto := by
    cases crypto
    dsimp only
    congr 1
    funext input
    simp only [Equiv.apply_symm_apply]

/-- Answer types are unchanged, so the recoder performs exactly one target query. -/
def query (labels : Password ≃ Ranked) : (input : Point Password Entropy) →
    OracleComp (spec Ranked Entropy) (spec Password Entropy input)
  | .a password salt => ask (.a (labels password) salt)
  | .b round right => ask (.b round right)
  | .h key round right => ask (.h key round right)
  | .g entropy => ask (.g entropy)

def program (labels : Password ≃ Ranked) (adversary : OracleComp (spec Password Entropy) Result) :
    OracleComp (spec Ranked Entropy) Result :=
  OracleComp.construct pure (fun input _ recurse => query labels input >>= recurse) adversary

variable (labels : Password ≃ Ranked) (crypto : Tables Password Entropy)

theorem execute_query (input : Point Password Entropy) :
    execute (tables labels crypto) (query labels input)=(answer crypto input,[point labels input]) := by
  cases input <;> simp only [query, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, answer, tables, Equiv.coe_fn_mk, Equiv.symm_apply_apply, point]

/-- The complete adaptive answer and query transcript is preserved, including repeated queries. -/
theorem execution (adversary : OracleComp (spec Password Entropy) Result) :
    execute (tables labels crypto) (program labels adversary)=
      ((execute crypto adversary).1,(execute crypto adversary).2.map (point labels)) := by
  induction adversary using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
    change execute (tables labels crypto) (query labels input >>= fun answer => program labels (next answer)) =
      ((execute crypto (ask input >>= next)).1,(execute crypto (ask input >>= next)).2.map (point labels))
    simp only [execute_bind, execute_query, ih, execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g, List.singleton_append, List.map_cons]

/-- Every resource counter is preserved before a numerical bound is applied. -/
theorem counts (adversary : OracleComp (spec Password Entropy) Result)
    (tag : Point Ranked Entropy → Bool) :
    (execute (tables labels crypto) (program labels adversary)).2.countP tag=
      (execute crypto adversary).2.countP (tag ∘ point labels) := by
  rw [execution, List.countP_map]

variable [Fintype Password] [DecidableEq Password] [Fintype Ranked] [DecidableEq Ranked]
  [Fintype Entropy] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype
local instance : Fintype (Tables Password Entropy) :=
  Fintype.ofEquiv (TableFactors.Quad Password Entropy) TableFactors.tableEquiv.symm
local instance : Fintype (Tables Ranked Entropy) :=
  Fintype.ofEquiv (TableFactors.Quad Ranked Entropy) TableFactors.tableEquiv.symm
local instance : Nonempty (Tables Password Entropy) := ⟨⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩⟩
local instance : Nonempty (Tables Ranked Entropy) := ⟨⟨fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩⟩

/-- Independent ideal function sampling is invariant under renaming the complete password alphabet. -/
theorem table_law (labels : Password ≃ Ranked) : (sampleTables (Password := Password) (Entropy := Entropy)).map (tables labels)=
      sampleTables (Password := Ranked) (Entropy := Entropy) := by
  rw [TableFactors.sample_uniform, TableFactors.sample_uniform]
  exact PMF.uniformOfFintype_map_of_bijective (tables labels) (tables labels).bijective

/-- Any source and winning predicate can retain the entire joint prior and oracle tables through the transport. -/
theorem joint (labels : Password ≃ Ranked) (prior : PMF Password) :
    (prior.bind fun password => (sampleTables (Password := Password) (Entropy := Entropy)).map
      (fun crypto => (labels password,tables labels crypto))) =
    ((prior.map labels).bind fun password => (sampleTables (Password := Ranked) (Entropy := Entropy)).map
      (fun crypto => (password,crypto))) := by
  rw [PMF.bind_map]
  apply congrArg (PMF.bind prior)
  funext password
  have law := congrArg (fun distribution : PMF (Tables Ranked Entropy) => distribution.map
    (fun crypto => (labels password,crypto))) (table_law (Entropy := Entropy) labels)
  simpa only [PMF.map_comp, Function.comp_def] using law

omit [DecidableEq Password] [Fintype Ranked] [DecidableEq Ranked] [Fintype Entropy] [DecidableEq Entropy] in
/-- Sort all labels by descending prior probability; zero-probability labels remain present. -/
def ranking (prior : PMF Password) : Fin (Fintype.card Password) ≃ Password :=
  let enumeration := (Fintype.equivFin Password).symm
  (Tuple.sort (fun index => (OrderDual.toDual (prior (enumeration index))))).trans enumeration

omit [DecidableEq Password] [Fintype Ranked] [DecidableEq Ranked] [Fintype Entropy] [DecidableEq Entropy] in
/-- Ranking supplies exactly the antitone probability sequence required by the finite source theorems. -/
theorem ranking_antitone (prior : PMF Password) :
    Antitone (fun index => prior (ranking prior index)) := by
  exact Tuple.monotone_sort (fun index => OrderDual.toDual (prior ((Fintype.equivFin Password).symm index)))

omit [DecidableEq Password] [Fintype Ranked] [DecidableEq Ranked] [Fintype Entropy] [DecidableEq Entropy] in
/-- The ranked prior's point probabilities are the original label probabilities, with no conditioning. -/
theorem ranked_prior (prior : PMF Password) (index : Fin (Fintype.card Password)) :
    (prior.map (ranking prior).symm) index=prior (ranking prior index) := by
  exact PMFTransport.equiv_apply prior (ranking prior).symm index

omit [DecidableEq Password] [Fintype Ranked] [DecidableEq Ranked] [Fintype Entropy] [DecidableEq Entropy] in
theorem sorted_prior (prior : PMF Password) : Antitone (prior.map (ranking prior).symm) := by
  intro first second ordered
  rw [ranked_prior, ranked_prior]
  exact ranking_antitone prior ordered

/-- The actual mask and Feistel permutation depend on password labels only through A. -/
def sourceCipher (password : Password) (other : CryptoInputs.ABH Password) : Equiv.Perm State :=
  KnownPairModel.roundsEquiv
    (KnownPairModel.allMasks password other.1 other.2.1 other.2.2)

def otherTables (labels : Password ≃ Ranked) : CryptoInputs.ABH Password ≃ CryptoInputs.ABH Ranked where
  toFun other := (fun input => other.1 (labels.symm input.1,input.2),other.2)
  invFun other := (fun input => other.1 (labels input.1,input.2),other.2)
  left_inv other := by
    apply Prod.ext
    · funext input
      exact congrArg (fun value => other.1 (value,input.2)) (labels.symm_apply_apply input.1)
    · rfl
  right_inv other := by
    apply Prod.ext
    · funext input
      exact congrArg (fun value => other.1 (value,input.2)) (labels.apply_symm_apply input.1)
    · rfl

omit [Fintype Password] [DecidableEq Password] [Fintype Ranked] [DecidableEq Ranked]
  [Fintype Entropy] [DecidableEq Entropy] in
theorem cipher_recode (labels : Password ≃ Ranked) (password : Password)
    (other : CryptoInputs.ABH Password) :
    sourceCipher (labels password) (otherTables labels other)=sourceCipher password other := by
  unfold sourceCipher
  congr 1
  unfold KnownPairModel.allMasks
  congr 1
  funext round right
  simp only [KnownPairModel.mask, otherTables, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

variable {V R : Type} [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] [Nonempty Entropy]
attribute [local irreducible] execute Lemma1.encrypt

def attacker (labels : Password ≃ Ranked)
    (adversary : State → OracleComp (spec Password Entropy) Password) (container : State) :
    OracleComp (spec Ranked Entropy) Ranked :=
  labels <$> program labels (adversary container)

/-- The original source game is defined over native password labels, not over a pre-ranked dictionary. -/
def source (state : (Entropy × V) ≃ State) (hash : Hash ≃ (V × R)) (prior : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Password) : PMF Bool :=
  prior.bind fun password => (PMF.uniformOfFintype (CryptoInputs.ABH Password)).bind fun other =>
    ((PMF.uniformOfFintype (Entropy × (Entropy → Hash))).map
      (CoordinateResampling.original state hash (sourceCipher password other))).map
      (fun input => decide ((execute (CryptoInputs.tables other input.2) (adversary input.1)).1=password))

omit [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] in
/-- Both the generated source and the adaptive password-recovery event are invariant under recoding. -/
theorem source_recode (labels : Password ≃ Ranked) (state : (Entropy × V) ≃ State)
    (hash : Hash ≃ (V × R)) (prior : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Password) :
    source state hash prior adversary=source state hash (prior.map labels) (attacker labels adversary) := by
  unfold source
  rw [PMF.bind_map]
  apply congrArg (PMF.bind prior)
  funext password
  dsimp only [Function.comp_def]
  have uniform := PMF.uniformOfFintype_map_of_bijective (otherTables labels)
    (otherTables labels).bijective
  rw [← uniform, PMF.bind_map]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (CryptoInputs.ABH Password)))
  funext other
  dsimp only [Function.comp_def]
  rw [cipher_recode]
  simp only [PMF.map_comp]
  congr 1
  funext input
  have converted := execution labels (CryptoInputs.tables other
    (CoordinateResampling.original state hash (sourceCipher password other) input).2)
    (adversary (CoordinateResampling.original state hash (sourceCipher password other) input).1)
  simp only [Function.comp_def, attacker, execute_map]
  rw [show CryptoInputs.tables (otherTables labels other)
      (CoordinateResampling.original state hash (sourceCipher password other) input).2=
      tables labels (CryptoInputs.tables other
        (CoordinateResampling.original state hash (sourceCipher password other) input).2) from rfl]
  rw [converted]
  simp only [Equiv.apply_eq_iff_eq]

omit [Fintype Password] [DecidableEq Password] [Fintype Ranked] [DecidableEq Ranked]
  [Fintype Entropy] [DecidableEq Entropy] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] [Nonempty Entropy] in
/-- The four counted resource types do not depend on a password's name. -/
theorem resource_tags (labels : Password ≃ Ranked) (input : Point Password Entropy) :
    QueryCounts.isA (point labels input)=QueryCounts.isA input ∧
    QueryCounts.isB (point labels input)=QueryCounts.isB input ∧
    QueryCounts.isH (point labels input)=QueryCounts.isH input ∧
    G4Programs.isG (point labels input)=G4Programs.isG input := by
  cases input <;> exact ⟨rfl,rfl,rfl,rfl⟩

omit [Fintype Ranked] [DecidableEq Ranked] in
/-- The full original-game Theorem3 applies to any finite native password alphabet with every query label retained. -/
theorem theorem3 (state : (Entropy × V) ≃ State) (hash : Hash ≃ (V × R))
    (firstHalf : Entropy → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy state input)=input.1) (prior : PMF Password)
    (adversary : State → OracleComp (spec Password Entropy) Password) (p1 : ENNReal)
    (largest : ∀ password,prior password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container crypto,(execute crypto (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container crypto,(execute crypto (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container crypto,(execute crypto (adversary container)).2.countP QueryCounts.isH ≤ qH)
    (budgetG : ∀ container crypto,(execute crypto (adversary container)).2.countP G4Programs.isG ≤ qG) :
    (source state hash prior adversary) true ≤
      RankedMass.top (prior.map (ranking prior).symm) (kA/12+1)+
        (qG+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  let labels := (ranking prior).symm
  have logs (container : State) (crypto : Tables (Fin (Fintype.card Password)) Entropy) :
      (execute crypto (attacker labels adversary container)).2=
      (execute ((tables labels).symm crypto) (adversary container)).2.map (point labels) := by
    have converted := execution labels ((tables labels).symm crypto) (adversary container)
    rw [Equiv.apply_symm_apply] at converted
    simpa only [attacker, execute_map] using congrArg Prod.snd converted
  have largestRank (index : Fin (Fintype.card Password)) : (prior.map labels) index ≤ p1 := by
    rw [ranked_prior]
    exact largest _
  have actual := Theorem3.bound state hash firstHalf projects (prior.map labels) (sorted_prior prior)
    (attacker labels adversary) p1 largestRank kA qB qH qG
    (fun container crypto => by
      rw [logs, List.countP_map]
      simpa only [Function.comp_def, (resource_tags labels _).1] using budgetA container ((tables labels).symm crypto))
    (fun container crypto => by
      rw [logs, List.countP_map]
      simpa only [Function.comp_def, (resource_tags labels _).2.1] using budgetB container ((tables labels).symm crypto))
    (fun container crypto => by
      rw [logs, List.countP_map]
      simpa only [Function.comp_def, (resource_tags labels _).2.2.1] using budgetH container ((tables labels).symm crypto))
    (fun container crypto => by
      rw [logs, List.countP_map]
      simpa only [Function.comp_def, (resource_tags labels _).2.2.2] using budgetG container ((tables labels).symm crypto))
  rw [source_recode labels state hash prior adversary]
  exact actual

end PasswordDomains

namespace PasswordDomains
open Gamma2Model WalletCryptoCompiler
variable {Password Ranked Entropy Domain Result : Type}

/-- Additional wallet/record query types are unchanged by a password relabeling. -/
def combinedPoint (labels : Password ≃ Ranked) :
    Point Password Entropy ⊕ Domain → Point Ranked Entropy ⊕ Domain :=
  Sum.map (point labels) id

variable (labels : Password ≃ Ranked) (extra : OracleSpec Domain)

/-- The recoder receives oracle access only; neither a sampled table nor the hidden password is available. -/
def combinedQuery : (input : Point Password Entropy ⊕ Domain) → OracleComp (combinedSpec (Password := Ranked) (Entropy := Entropy) extra)
        (combinedSpec (Password := Password) (Entropy := Entropy) extra input)
  | .inl (.a password salt) => TranscriptErasure.ask (spec := combinedSpec (Password := Ranked) (Entropy := Entropy) extra) (.inl (.a (labels password) salt))
  | .inl (.b round right) => TranscriptErasure.ask (spec := combinedSpec (Password := Ranked) (Entropy := Entropy) extra) (.inl (.b round right))
  | .inl (.h key round right) => TranscriptErasure.ask (spec := combinedSpec (Password := Ranked) (Entropy := Entropy) extra) (.inl (.h key round right))
  | .inl (.g entropy) => TranscriptErasure.ask (spec := combinedSpec (Password := Ranked) (Entropy := Entropy) extra) (.inl (.g entropy))
  | .inr value => TranscriptErasure.ask (spec := combinedSpec (Password := Ranked) (Entropy := Entropy) extra) (.inr value)

def combinedProgram
    (adversary : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) extra) Result) :
    OracleComp (combinedSpec (Password := Ranked) (Entropy := Entropy) extra) Result :=
  OracleComp.construct pure (fun input _ recurse => combinedQuery labels extra input >>= recurse) adversary

theorem combined_query (crypto : Tables Password Entropy) (other : (input : Domain) → extra input)
    (input : Point Password Entropy ⊕ Domain) :
    TranscriptErasure.execute (combinedAnswer extra (tables labels crypto) other)
      (combinedQuery labels extra input)=
      (combinedAnswer extra crypto other input,[combinedPoint labels input]) := by
  cases input with
  | inl input => cases input <;>
      simp only [combinedQuery,TranscriptErasure.execute_ask,combinedAnswer,tables,
        Equiv.coe_fn_mk,answer,Equiv.symm_apply_apply,combinedPoint,Sum.map_inl,point]
  | inr value => rfl

/-- Full S/T/Omega or record interactions preserve their answers, order and exact per-resource counts. -/
theorem combined_execution (labels : Password ≃ Ranked) (extra : OracleSpec Domain)
    (crypto : Tables Password Entropy) (other : (input : Domain) → extra input)
    (adversary : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy) extra) Result) :
    TranscriptErasure.execute (combinedAnswer extra (tables labels crypto) other)
      (combinedProgram labels extra adversary)=
      let actual := TranscriptErasure.execute (combinedAnswer extra crypto other) adversary
      (actual.1,actual.2.map (combinedPoint labels)) := by
  induction adversary using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
    change TranscriptErasure.execute (combinedAnswer extra (tables labels crypto) other)
        (combinedQuery labels extra input >>= fun value => combinedProgram labels extra (next value))=
      let actual := TranscriptErasure.execute (combinedAnswer extra crypto other)
        (TranscriptErasure.ask input >>= next)
      (actual.1,actual.2.map (combinedPoint labels))
    simp only [TranscriptErasure.execute_bind,combined_query,ih,
      TranscriptErasure.execute_ask,List.singleton_append,List.map_cons]

/-- Byte strings with an admitted maximum length form a finite full alphabet, irrespective of prior support. -/
abbrev BoundedBytes (limit : Nat) := Σ length : Fin (limit+1), Fin length.val → Fin 256

instance boundedBytesFintype (limit : Nat) : Fintype (BoundedBytes limit) := inferInstance

/-- Validation or normalization selects a subset of the finite encoded-byte alphabet, not an infinite new type. -/
theorem admitted_finite (admitted : BoundedBytes 1024 → Prop) : Finite {bytes // admitted bytes} := by
  infer_instance

end PasswordDomains

end
end MhfeLean
