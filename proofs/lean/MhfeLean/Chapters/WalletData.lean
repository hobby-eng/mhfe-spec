/- long: the wallet-data experiment and its source-specific corollaries share one model. -/
-- long: G10 has one checksum-aware proof and independent-wallet-data specializations, sharing the same operational models and counters.
import MhfeLean.Chapters.CreationRefusal
import MhfeLean.Chapters.BatchQueries
import MhfeLean.Chapters.MatchingAttack
import MhfeLean.Chapters.WalletCollision

namespace MhfeLean
noncomputable section

/-! # G10: one wallet-data proof and its source specializations

The checksum-aware argument covers independent entropy-based wallet data with
identity encoding. The source-game definitions remain the same.
-/

namespace G10Resampling
variable {E V R S H W : Type}

def statePlus (state : (E × V) ≃ S) : (E × (V × W)) ≃ (S × W) where
  toFun fields := (state (fields.1,fields.2.1),fields.2.2)
  invFun output := ((state.symm output.1).1,((state.symm output.1).2,output.2))
  left_inv := by rintro ⟨e,v,w⟩; simp
  right_inv := by rintro ⟨s,w⟩; simp

def hashPlus (hash : H ≃ (V × R)) : (H × W) ≃ ((V × W) × R) where
  toFun output := (((hash output.1).1,output.2),(hash output.1).2)
  invFun fields := (hash.symm (fields.1.1,fields.2),fields.1.2)
  left_inv := by rintro ⟨h,w⟩; simp
  right_inv := by rintro ⟨⟨v,w⟩,r⟩; simp

def cipherPlus (cipher : Equiv.Perm S) : Equiv.Perm (S × W) := Equiv.prodCongr cipher (Equiv.refl W)

def original (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S)
    (seed : E × (E → H × W)) : (S × W) × (E → H × W) :=
  ((cipher (state (seed.1,(hash (seed.2 seed.1).1).1)),(seed.2 seed.1).2),seed.2)

variable [DecidableEq E]

def programmed (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S)
    (seed : (S × W) × (E → H × W)) : (S × W) × (E → H × W) :=
  let recovered := state.symm (cipher.symm seed.1.1)
  (seed.1,Function.update seed.2 recovered.1
    (hash.symm (recovered.2,(hash (seed.2 recovered.1).1).2),seed.1.2))

omit [DecidableEq E] in
/-- The original augmented output contains exactly Y and the wallet data at the genuine entropy. -/
theorem original_agrees (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S)
    (seed : E × (E → H × W)) : CoordinateResampling.original (statePlus (W := W) state) (hashPlus hash) (cipherPlus cipher) seed=
      original state hash cipher seed := rfl

/-- The two values are programmed at the same inverse entropy; the original hash suffix is retained. -/
theorem programmed_agrees (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S)
    (seed : (S × W) × (E → H × W)) :
    CoordinateResampling.programmed (statePlus state) (hashPlus hash) (cipherPlus cipher) seed=
      programmed state hash cipher seed := rfl

variable [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
  [Fintype S] [Nonempty S] [Fintype H] [Nonempty H] [Fintype W] [Nonempty W]

/-- Exact full joint law, including both complete random-function tables, not just Y's marginal. -/
theorem law (state : (E × V) ≃ S) (hash : H ≃ (V × R)) (cipher : Equiv.Perm S) :
    (PMF.uniformOfFintype (E × (E → H × W))).map (original state hash cipher)=
      (PMF.uniformOfFintype ((S × W) × (E → H × W))).map (programmed state hash cipher) := by
  have simpaTerm := CoordinateResampling.fixed (statePlus (W := W) state) (hashPlus hash) (cipherPlus cipher)
  (try simp only [original_agrees,programmed_agrees] at simpaTerm ⊢)
  exact simpaTerm

end G10Resampling

namespace G10JointTables
variable {E H W : Type}

def split : (E → H × W) ≃ ((E → H) × (E → W)) where
  toFun table := (fun e => (table e).1,fun e => (table e).2)
  invFun fields e := (fields.1 e,fields.2 e)
  left_inv := by intro table; funext e; exact Prod.eta (table e)
  right_inv := by intro fields; rfl

variable [DecidableEq E] [Fintype E] [Fintype H] [Nonempty H] [Fintype W] [Nonempty W]

/-- This is the joint full-table law, not two unrelated marginal equalities. -/
theorem law :
    (PMF.uniformOfFintype (E → H × W)).map split=
    ProbabilityTools.independentPair (PMF.uniformOfFintype (E → H)) (PMF.uniformOfFintype (E → W)) := by
  rw [PMF.uniformOfFintype_map_of_bijective split split.bijective]
  exact ProbabilityTools.uniform_product

end G10JointTables

namespace G10WalletCompiler
open Gamma2Model WalletCryptoCompiler
variable {Password E Wallet Result : Type}

def point (source : Wallet → E) : Point Password E ⊕ Wallet → Point Password E
  | .inl query => query
  | .inr query => .g (source query)

def compile (walletSpec : OracleSpec Wallet) (wallet : (query : Wallet) → walletSpec query)
    (source : Wallet → E)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := E) walletSpec) Result) :
    OracleComp (spec Password E) Result :=
  OracleComp.construct (fun result => pure result)
    (fun query _ recurse => match query with
      | .inl query => do
        let value ← ask query
        recurse value
      | .inr query => do
        let _discarded : Hash ← ask (.g (source query))
        recurse (wallet query)) program

/-- A wallet query's padding answer is never used to select the continuation. -/
theorem query (walletSpec : OracleSpec Wallet) (wallet : (query : Wallet) → walletSpec query)
    (source : Wallet → E) (query : Point Password E ⊕ Wallet)
    (next : combinedSpec walletSpec query → OracleComp (combinedSpec walletSpec) Result) :
    compile walletSpec wallet source (TranscriptErasure.ask query >>= next)=
      (match query with
      | .inl query => do
        let value ← ask query
        compile walletSpec wallet source (next value)
      | .inr query => do
        let _discarded : Hash ← ask (.g (source query))
        compile walletSpec wallet source (next (wallet query))) := by
  cases query <;> rfl

theorem compile_pure (walletSpec : OracleSpec Wallet) (wallet : (query : Wallet) → walletSpec query)
    (source : Wallet → E) (result : Result) : compile (Password := Password) walletSpec wallet source (pure result)=pure result := rfl

attribute [local irreducible] compile

/-- Result and complete padded query log are preserved for an arbitrary adaptive original program. -/
theorem execution (walletSpec : OracleSpec Wallet) (wallet : (query : Wallet) → walletSpec query)
    (source : Wallet → E) (tables : Tables Password E)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := E) walletSpec) Result) :
    execute tables (compile walletSpec wallet source program)=
      let full := TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) program
      (full.1,full.2.map (point source)) := by
  induction program using OracleComp.inductionOn with
  | pure result => rw [compile_pure]; rfl
  | query_bind selected next ih =>
    change execute tables (compile walletSpec wallet source (TranscriptErasure.ask selected >>= next))=_
    rw [query]
    cases selected with
    | inl selected =>
      simp only [execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g]
      rw [ih (answer tables selected)]
      rfl
    | inr selected =>
      simp only [execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g]
      rw [ih (wallet selected)]
      rfl

/-- Original G queries and wallet entropy queries both become actual G points in the compiled trace. -/
theorem target (source : Wallet → E) (queries : List (Point Password E ⊕ Wallet)) (selected : E)
    (hit : Sum.inl (Point.g selected) ∈ queries ∨ ∃ query ∈ queries, ∃ wallet,query=Sum.inr wallet ∧ source wallet=selected) :
    Point.g selected ∈ queries.map (point source) := by
  obtain direct | ⟨query,member,wallet,equal,value⟩ := hit
  · exact List.mem_map.mpr ⟨Sum.inl (Point.g selected),direct,rfl⟩
  · refine List.mem_map.mpr ⟨query,member,?_⟩
    rw [equal]
    exact congrArg Point.g value

end G10WalletCompiler

namespace G10Removal
open Gamma2Model WalletCryptoCompiler G10WalletCompiler
variable {Password E Wallet Result : Type}

/-- The discarded-G compiler makes every changed wallet or hash point visible as a target G query. -/
theorem execution (walletSpec : OracleSpec Wallet) (source : Wallet → E)
    (plainWallet changedWallet : (query : Wallet) → walletSpec query)
    (plain : Tables Password E) (changedG : E → Hash) (target : E)
    (g_agrees : ∀ e,e ≠ target → changedG e=plain.g e)
    (wallet_agrees : ∀ query,source query ≠ target → changedWallet query=plainWallet query)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := E) walletSpec) Result)
    (not_bad : Point.g target ∉ (execute plain (compile walletSpec plainWallet source program)).2) :
    TranscriptErasure.execute (combinedAnswer walletSpec {plain with g := changedG} changedWallet) program=
      TranscriptErasure.execute (combinedAnswer walletSpec plain plainWallet) program := by
  have avoids : Point.g target ∉
      (TranscriptErasure.execute (combinedAnswer walletSpec plain plainWallet) program).2.map (point source) := by
    simpa only [G10WalletCompiler.execution] using not_bad
  apply TranscriptErasure.execute_agree
  intro query member
  have unchanged : point source query ≠ Point.g target := by
    intro equal
    exact avoids (List.mem_map.mpr ⟨query,member,equal⟩)
  cases query with
  | inl query =>
    cases query with
    | a password salt => rfl
    | b round right => rfl
    | h key round right => rfl
    | g e =>
      apply g_agrees
      intro equal
      exact unchanged (by rw [equal]; rfl)
  | inr query =>
    apply wallet_agrees
    intro equal
    exact unchanged (congrArg Point.g equal)

/-- Only a plain success or an actual compiled target query can explain a programmed success. -/
theorem success (walletSpec : OracleSpec Wallet) (source : Wallet → E)
    (plainWallet changedWallet : (query : Wallet) → walletSpec query)
    (plain : Tables Password E) (changedG : E → Hash) (target : E)
    (g_agrees : ∀ e,e ≠ target → changedG e=plain.g e)
    (wallet_agrees : ∀ query,source query ≠ target → changedWallet query=plainWallet query)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := E) walletSpec) Result)
    (win : Result → Bool)
    (won : win (TranscriptErasure.execute
      (combinedAnswer walletSpec {plain with g := changedG} changedWallet) program).1=true) :
    win (execute plain (compile walletSpec plainWallet source program)).1=true ∨
      Point.g target ∈ (execute plain (compile walletSpec plainWallet source program)).2 := by
  classical
  by_cases bad : Point.g target ∈ (execute plain (compile walletSpec plainWallet source program)).2
  · exact Or.inr bad
  · apply Or.inl
    have same := execution walletSpec source plainWallet changedWallet plain changedG target g_agrees wallet_agrees program bad
    rw [same] at won
    simpa only [G10WalletCompiler.execution] using won

end G10Removal

namespace G10Model
open Gamma2Model CryptoInputs
variable {N : Nat} {E V R Data : Type}

abbrev JointTable (E Data : Type) := E → Hash × Data

@[reducible] def walletSpec (E Data : Type) : OracleSpec E := fun _ => Data

abbrev Adversary (N : Nat) (E Data : Type) := State → Data →
  OracleComp (WalletCryptoCompiler.combinedSpec (Password := Fin N) (Entropy := E) (walletSpec E Data)) (Fin N)

def crypto (other : ABH (Fin N)) (joint : JointTable E Data) : Tables (Fin N) E :=
  tables other (fun e => (joint e).1)

def combined (other : ABH (Fin N)) (joint : JointTable E Data) :=
  WalletCryptoCompiler.combinedAnswer (walletSpec E Data) (crypto other joint) (fun e => (joint e).2)

def score (real : Fin N) (other : ABH (Fin N)) (adversary : Adversary N E Data)
    (view : (State × Data) × JointTable E Data) : Bool :=
  decide ((TranscriptErasure.execute (combined other view.2) (adversary view.1.1 view.1.2)).1=real)

variable [DecidableEq E]

variable [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
  [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

variable (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (passwords : PMF (Fin N))
  (adversary : Adversary N E Data)

def original : PMF Bool :=
  passwords.bind fun real => (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
    ((PMF.uniformOfFintype (E × JointTable E Data)).map
      (G10Resampling.original coordinates hash (Theorem3.cipher real other))).map
      (score real other adversary)

def programmed : PMF Bool :=
  passwords.bind fun real => (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
    ((PMF.uniformOfFintype ((State × Data) × JointTable E Data)).map
      (G10Resampling.programmed coordinates hash (Theorem3.cipher real other))).map
      (score real other adversary)

/-- Exact equality retains the actual adversary and the full jointly programmed G/Omega table. -/
theorem resampling :
    original coordinates hash passwords adversary=programmed coordinates hash passwords adversary := by
  unfold original programmed
  simp_rw [G10Resampling.law]

end G10Model

namespace G10WalletCounts
open Gamma2Model G10WalletCompiler
variable {Password E Wallet Result : Type}

def crypto (test : Point Password E → Bool) : Point Password E ⊕ Wallet → Bool
  | .inl point => test point
  | .inr _ => false

def isWallet : Point Password E ⊕ Wallet → Bool
  | .inl _ => false
  | .inr _ => true

/-- A/B/H and any predicate ignoring G are unchanged, including all repeated calls. -/
theorem crypto_count (source : Wallet → E) (test : Point Password E → Bool)
    (ignores : ∀ e,test (.g e)=false) (queries : List (Point Password E ⊕ Wallet)) :
    (queries.map (point source)).countP test=queries.countP (crypto test) := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
    cases query <;> simp only [List.map_cons,List.countP_cons,point,crypto,ignores,ih] <;> rfl

theorem g_count (source : Wallet → E) (queries : List (Point Password E ⊕ Wallet)) :
    (queries.map (point source)).countP InverseCounts.isG=
      queries.countP (crypto InverseCounts.isG)+queries.countP isWallet := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
    cases query with
    | inl point =>
      simp only [List.map_cons,List.countP_cons,G10WalletCompiler.point,crypto,isWallet,
        Bool.false_eq_true,ite_false,ih,Nat.add_zero]
      exact Nat.add_right_comm _ _ _
    | inr wallet =>
      simp only [List.map_cons,List.countP_cons,G10WalletCompiler.point,crypto,isWallet,InverseCounts.isG,
        Bool.false_eq_true,ite_false,ite_true,ih]
      omega

end G10WalletCounts

namespace G10BudgetRules
open Gamma2Model WalletCryptoCompiler
variable {Password E Wallet Result : Type}

/-- Any crypto-family predicate ignoring G transfers its original hard cap unchanged. -/
theorem crypto_budget (walletSpec : OracleSpec Wallet) (wallet : (query : Wallet) → walletSpec query)
    (source : Wallet → E) (tables : Tables Password E)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := E) walletSpec) Result)
    (test : Point Password E → Bool) (ignores : ∀ e,test (.g e)=false) (limit : Nat)
    (budget : (TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) program).2.countP
      (G10WalletCounts.crypto test) ≤ limit) :
    (execute tables (G10WalletCompiler.compile walletSpec wallet source program)).2.countP test ≤ limit := by
  rw [G10WalletCompiler.execution]
  dsimp only
  rw [G10WalletCounts.crypto_count source test ignores]
  exact budget

/-- G's original cap and the wallet-query cap add, with no distinct-query discount. -/
theorem g_budget (walletSpec : OracleSpec Wallet) (wallet : (query : Wallet) → walletSpec query)
    (source : Wallet → E) (tables : Tables Password E)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := E) walletSpec) Result)
    (qG qWallet : Nat)
    (g_bound : (TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) program).2.countP
      (G10WalletCounts.crypto InverseCounts.isG) ≤ qG)
    (wallet_bound : (TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) program).2.countP
      G10WalletCounts.isWallet ≤ qWallet) :
    (execute tables (G10WalletCompiler.compile walletSpec wallet source program)).2.countP InverseCounts.isG ≤ qG+qWallet := by
  rw [G10WalletCompiler.execution]
  dsimp only

  rw [G10WalletCounts.g_count]
  exact add_le_add g_bound wallet_bound

end G10BudgetRules

namespace G10Estimate
open Gamma2Model WalletCryptoCompiler G10WalletCounts
variable {N : Nat} {E Wallet : Type} [DecidableEq E] [Fintype E]
attribute [local instance] FiniteBits.fintype

/-- The unchanged G10 Gamma2 estimate, packaged before actual program substitution. -/
def Holds (entropy : State → E) (passwords : PMF (Fin N)) (p1 : ENNReal) (kA qB qH qG qWallet : Nat)
    (program : State → OracleComp (spec (Fin N) E) (Fin N)) : Prop :=
  ((game passwords program).map (Theorem3Assembly.winOrBad entropy)) true ≤
    RankedMass.top passwords (kA/12+1)+
      ((qG:ENNReal)+qWallet+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal)

/-- Unfold only the estimate after program substitution; this keeps kernel checking bounded. -/
theorem expose (entropy : State → E) (passwords : PMF (Fin N)) (p1 : ENNReal)
    (kA qB qH qG qWallet : Nat) (program : State → OracleComp (spec (Fin N) E) (Fin N))
    (certificate : Holds entropy passwords p1 kA qB qH qG qWallet program) :
    ((game passwords program).map (Theorem3Assembly.winOrBad entropy)) true ≤
      RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qWallet+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := certificate

end G10Estimate

namespace G10CompiledBound
open Gamma2Model WalletCryptoCompiler G10WalletCounts
variable {N : Nat} {E Wallet : Type} [DecidableEq E] [Fintype E]
attribute [local instance] FiniteBits.fintype
-- Keep the abstract adversary opaque while applying the shared probability bound.
attribute [local irreducible] Gamma2Model.game Theorem3Assembly.winOrBad
  G10WalletCompiler.compile

set_option maxRecDepth 8192 in
theorem bound (entropy : State → E) (firstHalf : E → Half)
    (projects : ∀ state,firstHalf (entropy state)=state.1)
    (walletSpec : OracleSpec Wallet) (wallet : (query : Wallet) → walletSpec query) (source : Wallet → E)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (combinedSpec (Password := Fin N) (Entropy := E) walletSpec) (Fin N))
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qWallet : Nat)
    (budgetA : ∀ container tables,(TranscriptErasure.execute
      (combinedAnswer walletSpec tables wallet) (adversary container)).2.countP (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ container tables,(TranscriptErasure.execute
      (combinedAnswer walletSpec tables wallet) (adversary container)).2.countP (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ container tables,(TranscriptErasure.execute
      (combinedAnswer walletSpec tables wallet) (adversary container)).2.countP (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ container tables,(TranscriptErasure.execute
      (combinedAnswer walletSpec tables wallet) (adversary container)).2.countP (crypto InverseCounts.isG) ≤ qG)
    (budgetWallet : ∀ container tables,(TranscriptErasure.execute
      (combinedAnswer walletSpec tables wallet) (adversary container)).2.countP isWallet ≤ qWallet) :
    G10Estimate.Holds entropy passwords p1 kA qB qH qG qWallet
      (fun container => G10WalletCompiler.compile walletSpec wallet source (adversary container)) := by
  let compiled := fun container => G10WalletCompiler.compile walletSpec wallet source (adversary container)
  have capA : ∀ container tables,(execute tables (compiled container)).2.countP QueryCounts.isA ≤ kA := by
    intro container tables
    exact G10BudgetRules.crypto_budget walletSpec wallet source tables (adversary container)
      QueryCounts.isA (by intro e; rfl) kA (budgetA container tables)
  have capB : ∀ container tables,(execute tables (compiled container)).2.countP QueryCounts.isB ≤ qB := by
    intro container tables
    exact G10BudgetRules.crypto_budget walletSpec wallet source tables (adversary container)
      QueryCounts.isB (by intro e; rfl) qB (budgetB container tables)
  have capH : ∀ container tables,(execute tables (compiled container)).2.countP QueryCounts.isH ≤ qH := by
    intro container tables
    exact G10BudgetRules.crypto_budget walletSpec wallet source tables (adversary container)
      QueryCounts.isH (by intro e; rfl) qH (budgetH container tables)
  have capG : ∀ container tables,(execute tables (compiled container)).2.countP InverseCounts.isG ≤ qG+qWallet := by
    intro container tables
    exact G10BudgetRules.g_budget walletSpec wallet source tables (adversary container)
      qG qWallet (budgetG container tables) (budgetWallet container tables)
  have g_cap (container : State) (tables : Tables (Fin N) E) :
      (execute tables (compiled container)).2.countP G4Programs.isG ≤ qG+qWallet := by
    have same : (G4Programs.isG : Point (Fin N) E → Bool)=InverseCounts.isG := by
      funext point
      cases point <;> rfl
    rw [same]
    exact capG container tables
  have estimate := Theorem3Assembly.bound entropy firstHalf projects passwords sorted compiled
    p1 largest kA qB qH (qG+qWallet) capA capB capH g_cap
  apply estimate.trans_eq
  simp only [Nat.cast_add]

end G10CompiledBound

namespace G10DirectResampling
variable {E V R S H Phrase Data : Type} [DecidableEq E] [DecidableEq Phrase]

/-- Change only the verifier prefix at one entropy, preserving the hash suffix. -/
def patch (hash : H ≃ V × R) (g : E → H) (e : E) (v : V) : E → H :=
  Function.update g e (hash.symm (v,(hash (g e)).2))

@[simp] theorem patch_here (hash : H ≃ V × R) (g : E → H) (e : E) (v : V) :
    hash (patch hash g e v e)=(v,(hash (g e)).2) := by
  simp [patch]

@[simp] theorem patch_twice (hash : H ≃ V × R) (g : E → H) (e : E) (v w : V) :
    patch hash (patch hash g e v) e w=patch hash g e w := by
  simp [patch]

@[simp] theorem patch_current (hash : H ≃ V × R) (g : E → H) (e : E) :
    patch hash g e (hash (g e)).1=g := by
  simp [patch]

abbrev Input (E H Phrase Data V : Type) := (E × ((E → H) × (Phrase → Data))) × (V × Data)
abbrev Raw (S E H Phrase Data : Type) := (S × Data) × ((E → H) × (Phrase → Data))

variable (state : (E × V) ≃ S) (hash : H ≃ V × R) (cipher : Equiv.Perm S)
  (phrase : (E → H) → E → Phrase)

def forward (seed : Input E H Phrase Data V) : Raw S E H Phrase Data :=
  let e := seed.1.1
  let g := seed.1.2.1
  let d := seed.1.2.2
  let p := phrase g e
  ((cipher (state (e,(hash (g e)).1)),d p),
    (patch hash g e seed.2.1,Function.update d p seed.2.2))

def backward (raw : Raw S E H Phrase Data) : Input E H Phrase Data V :=
  let recovered := state.symm (cipher.symm raw.1.1)
  let g := patch hash raw.2.1 recovered.1 recovered.2
  let p := phrase g recovered.1
  ((recovered.1,(g,Function.update raw.2.2 p raw.1.2)),
    ((hash (raw.2.1 recovered.1)).1,raw.2.2 p))

/-- The full original G is restored before computing the D programming point. -/
theorem left_inverse (state : (E × V) ≃ S) (hash : H ≃ V × R) (cipher : Equiv.Perm S)
    (phrase : (E → H) → E → Phrase) : Function.LeftInverse (backward (Data := Data) state hash cipher phrase) (forward state hash cipher phrase) := by
  rintro ⟨⟨e,g,d⟩,v,w⟩
  simp [forward,backward]

/-- Both fresh auxiliary values and both complete random-function tables are recovered. -/
theorem right_inverse (state : (E × V) ≃ S) (hash : H ≃ V × R) (cipher : Equiv.Perm S)
    (phrase : (E → H) → E → Phrase) : Function.RightInverse (backward (Data := Data) state hash cipher phrase) (forward state hash cipher phrase) := by
  rintro ⟨⟨y,u⟩,g,d⟩
  simp [forward,backward]

/-- A full seed bijection, valid even when phrase reads all of G. -/
def coupling : Input E H Phrase Data V ≃ Raw S E H Phrase Data where
  toFun := forward state hash cipher phrase
  invFun := backward state hash cipher phrase
  left_inv := left_inverse state hash cipher phrase
  right_inv := right_inverse state hash cipher phrase

end G10DirectResampling

namespace G10DirectLaw
open G10DirectResampling ProbabilityTools
variable {E V R S H Phrase Data : Type} [DecidableEq E] [DecidableEq Phrase]

abbrev Base (E H Phrase Data : Type) := E × ((E → H) × (Phrase → Data))

variable (state : (E × V) ≃ S) (hash : H ≃ V × R) (cipher : Equiv.Perm S)
  (phrase : (E → H) → E → Phrase)

def original (seed : Base E H Phrase Data) : Raw S E H Phrase Data :=
  ((cipher (state (seed.1,(hash (seed.2.1 seed.1)).1)),seed.2.2 (phrase seed.2.1 seed.1)),seed.2)

def programmed (raw : Raw S E H Phrase Data) : Raw S E H Phrase Data :=
  (raw.1,(backward state hash cipher phrase raw).1.2)

/-- Equality retains Y, the disclosed data and both whole programmed tables. -/
theorem observations (seed : Input E H Phrase Data V) :
    programmed state hash cipher phrase (coupling state hash cipher phrase seed)=
      original state hash cipher phrase seed.1 := by
  rcases seed with ⟨⟨e,g,d⟩,v,w⟩
  simp [programmed,coupling,forward,backward,original]

variable [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
  [Fintype S] [Nonempty S] [Fintype H] [Nonempty H] [Fintype Phrase] [Nonempty Phrase]
  [Fintype Data] [Nonempty Data]

omit [Fintype R] [Nonempty R] [Nonempty Phrase] in
/-- A proved seed bijection transports the complete law; no independence of phrase from G is assumed. -/
theorem law (state : (E × V) ≃ S) (hash : H ≃ V × R) (cipher : Equiv.Perm S)
    (phrase : (E → H) → E → Phrase) :
    (PMF.uniformOfFintype (Base E H Phrase Data)).map (original state hash cipher phrase)=
      (PMF.uniformOfFintype (Raw S E H Phrase Data)).map (programmed state hash cipher phrase) := by
  have moved := PMF.uniformOfFintype_map_of_bijective
    (coupling (Data := Data) state hash cipher phrase) (coupling state hash cipher phrase).bijective
  calc
    _ = ((PMF.uniformOfFintype (Input E H Phrase Data V)).map Prod.fst).map
        (original state hash cipher phrase) := by rw [uniform_fst]
    _ = (PMF.uniformOfFintype (Input E H Phrase Data V)).map
        (fun seed => original state hash cipher phrase seed.1) := PMF.map_comp _ _ _
    _ = (PMF.uniformOfFintype (Input E H Phrase Data V)).map
        (programmed state hash cipher phrase ∘ coupling state hash cipher phrase) := by
      congr 1
      funext seed
      exact (observations state hash cipher phrase seed).symm
    _ = ((PMF.uniformOfFintype (Input E H Phrase Data V)).map
        (coupling state hash cipher phrase)).map (programmed state hash cipher phrase) :=
      (PMF.map_comp _ _ _).symm
    _ = _ := by rw [moved]

end G10DirectLaw

namespace G10DirectModel
open Gamma2Model CryptoInputs
variable {N : Nat} {E V R Phrase Data : Type}

abbrev Table (E Phrase Data : Type) := (E → Hash) × (Phrase → Data)
abbrev Raw (E Phrase Data : Type) := (State × Data) × Table E Phrase Data
abbrev Adversary (N : Nat) (E Phrase Data : Type) := State → Data →
  OracleComp (WalletCryptoCompiler.combinedSpec (Password := Fin N) (Entropy := E)
    (G10Model.walletSpec Phrase Data)) (Fin N)

def combined (other : ABH (Fin N)) (functions : Table E Phrase Data) :=
  WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data)
    (tables other functions.1) functions.2

def score (real : Fin N) (other : ABH (Fin N)) (adversary : Adversary N E Phrase Data)
    (raw : Raw E Phrase Data) : Bool :=
  decide ((TranscriptErasure.execute (combined other raw.2) (adversary raw.1.1 raw.1.2)).1=real)

def plainProgram (decode : Phrase → E) (d : Phrase → Data) (data : Data)
    (adversary : Adversary N E Phrase Data) (container : State) :
    OracleComp (spec (Fin N) E) (Fin N) :=
  G10WalletCompiler.compile (G10Model.walletSpec Phrase Data) d decode
    (adversary container data)

variable [DecidableEq E] [DecidableEq Phrase]

def plainEvent (coordinates : (E × V) ≃ State) (decode : Phrase → E) (real : Fin N)
    (other : ABH (Fin N)) (adversary : Adversary N E Phrase Data) (raw : Raw E Phrase Data) : Bool :=
  Theorem3Assembly.winOrBad (Theorem3.entropy coordinates)
    (outcome real raw.1.1 (tables other raw.2.1) (plainProgram decode raw.2.2 raw.1.2 adversary))

variable [Fintype E] [Nonempty E] [Fintype V] [Nonempty V]
  [Fintype Phrase] [Nonempty Phrase] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

def original (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (phrase : (E → Hash) → E → Phrase) (passwords : PMF (Fin N))
    (adversary : Adversary N E Phrase Data) : PMF Bool :=
  passwords.bind fun real => (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
    ((PMF.uniformOfFintype (E × Table E Phrase Data)).map
      (G10DirectLaw.original coordinates hash (Theorem3.cipher real other) phrase)).map
      (score real other adversary)

def programmed (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (phrase : (E → Hash) → E → Phrase) (passwords : PMF (Fin N))
    (adversary : Adversary N E Phrase Data) : PMF Bool :=
  passwords.bind fun real => (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
    ((PMF.uniformOfFintype (Raw E Phrase Data)).map
      (G10DirectLaw.programmed coordinates hash (Theorem3.cipher real other) phrase)).map
      (score real other adversary)

omit [Nonempty Phrase] in
/-- Re-sampling keeps the checksum-dependent D point and all independent outer inputs. -/
theorem resampling (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (phrase : (E → Hash) → E → Phrase) (passwords : PMF (Fin N))
    (adversary : Adversary N E Phrase Data) :
    original coordinates hash phrase passwords adversary=programmed coordinates hash phrase passwords adversary := by
  unfold original programmed
  simp_rw [G10DirectLaw.law]

end G10DirectModel

namespace G10DirectTransfer
open Gamma2Model G10DirectModel CryptoInputs
variable {N : Nat} {E V R Phrase Data : Type} [DecidableEq E] [DecidableEq Phrase]
attribute [local irreducible] finalize

/-- Invalid-checksum D queries are covered too: every changed phrase decodes to the genuine entropy. -/
theorem pointwise (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (phrase : (E → Hash) → E → Phrase) (decode : Phrase → E)
    (decodes : ∀ g e,decode (phrase g e)=e)
    (real : Fin N) (other : ABH (Fin N)) (adversary : Adversary N E Phrase Data)
    (raw : Raw E Phrase Data) :
    (if score real other adversary
        (G10DirectLaw.programmed coordinates hash (Theorem3.cipher real other) phrase raw)
      then 1 else 0 : ENNReal) ≤
      (if plainEvent coordinates decode real other adversary raw then 1 else 0) := by
  classical
  let inverse := coordinates.symm ((Theorem3.cipher real other).symm raw.1.1)
  let plain := tables other raw.2.1
  let changedG := G10DirectResampling.patch hash raw.2.1 inverse.1 inverse.2
  let changedD := Function.update raw.2.2 (phrase changedG inverse.1) raw.1.2
  let program := adversary raw.1.1 raw.1.2
  have g_agrees (e : E) (different : e ≠ inverse.1) : changedG e=plain.g e := by
    change Function.update raw.2.1 inverse.1 _ e=raw.2.1 e
    rw [Function.update_of_ne different]
  have wallet_agrees (p : Phrase) (different : decode p ≠ inverse.1) : changedD p=raw.2.2 p := by
    apply Function.update_of_ne
    intro equal
    apply different
    rw [equal,decodes]
  have recovered : (outcome real raw.1.1 plain (plainProgram decode raw.2.2 raw.1.2 adversary)).recovered=
      (Theorem3.cipher real other).symm raw.1.1 :=
    CipherExecution.inverse real raw.1.1 plain
  have target : Theorem3.entropy coordinates
      (outcome real raw.1.1 plain (plainProgram decode raw.2.2 raw.1.2 adversary)).recovered=inverse.1 :=
    congrArg (Theorem3.entropy coordinates) recovered
  by_cases won : score real other adversary
      (G10DirectLaw.programmed coordinates hash (Theorem3.cipher real other) phrase raw)=true
  · have real_win : decide ((TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data)
          {plain with g := changedG} changedD) program).1=real)=true := won
    have split := G10Removal.success (G10Model.walletSpec Phrase Data) decode
      raw.2.2 changedD plain changedG inverse.1 g_agrees wallet_agrees program
      (fun result => decide (result=real)) real_win
    have larger : plainEvent coordinates decode real other adversary raw=true := by
      apply decide_eq_true
      change (execute plain (plainProgram decode raw.2.2 raw.1.2 adversary raw.1.1)).1=real ∨
        Point.g (Theorem3.entropy coordinates
          (outcome real raw.1.1 plain (plainProgram decode raw.2.2 raw.1.2 adversary)).recovered) ∈
          (execute plain (plainProgram decode raw.2.2 raw.1.2 adversary raw.1.1)).2
      rw [target]
      exact split.elim (fun hit => Or.inl (of_decide_eq_true hit)) Or.inr
    simp only [won,larger,ite_true,le_refl]
  · simp only [Bool.eq_false_iff.mpr won,Bool.false_eq_true,ite_false,zero_le]

end G10DirectTransfer

namespace G10DirectContexts
open Gamma2Model G10DirectModel CryptoInputs
open GameExpectation ProbabilityTools
variable {N : Nat} {E V R Phrase Data : Type} [DecidableEq E] [DecidableEq Phrase]
  [Fintype E] [Nonempty E] [Fintype Phrase] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

abbrev Context (Phrase Data : Type) := Data × (Phrase → Data)

def unprogrammed (coordinates : (E × V) ≃ State) (decode : Phrase → E) (passwords : PMF (Fin N))
    (adversary : Adversary N E Phrase Data) : PMF Bool :=
  passwords.bind fun real => (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
    (PMF.uniformOfFintype (Raw E Phrase Data)).map (plainEvent coordinates decode real other adversary)

/-- The genuine source success is covered without transferring separate components of Bad. -/
theorem transfer [Fintype V] [Nonempty V] (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (phrase : (E → Hash) → E → Phrase) (decode : Phrase → E) (decodes : ∀ g e,decode (phrase g e)=e)
    (passwords : PMF (Fin N)) (adversary : Adversary N E Phrase Data) :
    (original coordinates hash phrase passwords adversary) true ≤
      (unprogrammed coordinates decode passwords adversary) true := by
  rw [G10DirectModel.resampling,← MomentTools.bool (programmed coordinates hash phrase passwords adversary),
    ← MomentTools.bool (unprogrammed coordinates decode passwords adversary)]
  unfold programmed unprogrammed
  simp only [MomentTools.bind,moment_map,Function.comp_def]
  apply MomentTools.mono
  intro real
  apply MomentTools.mono
  intro other
  apply MomentTools.mono
  intro raw
  exact G10DirectTransfer.pointwise coordinates hash phrase decode decodes real other adversary raw

/-- Raw D, not the G-dependent composition D(phi(G,e)), is the independent context. -/
def pack : (Context Phrase Data × (State × (E → Hash))) ≃ Raw E Phrase Data where
  toFun fields := ((fields.2.1,fields.1.1),(fields.2.2,fields.1.2))
  invFun raw := ((raw.1.2,raw.2.2),(raw.1.1,raw.2.1))
  left_inv := by intro fields; rfl
  right_inv := by intro raw; rfl

omit [Nonempty E] in
/-- The full raw function tables and the two disclosed values have the exact product law. -/
theorem law :
    PMF.uniformOfFintype (Raw E Phrase Data)=
    (PMF.uniformOfFintype (Context Phrase Data)).bind fun context =>
      (PMF.uniformOfFintype (State × (E → Hash))).map fun seed => pack (context,seed) := by
  have moved := PMF.uniformOfFintype_map_of_bijective
    (pack (E := E) (Phrase := Phrase) (Data := Data)) pack.bijective
  rw [← moved,uniform_product]
  simp only [independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def]

def next (coordinates : (E × V) ≃ State) (decode : Phrase → E) (real : Fin N) (other : ABH (Fin N))
    (adversary : Adversary N E Phrase Data) (context : Context Phrase Data)
    (seed : State × (E → Hash)) : Bool :=
  Theorem3Assembly.winOrBad (Theorem3.entropy coordinates)
    (outcome real seed.1 (tables other seed.2) (plainProgram decode context.2 context.1 adversary))

omit [Nonempty E] in
/-- Exact fixed-password fixed-ABH decomposition, before any averaging argument. -/
theorem fixed (coordinates : (E × V) ≃ State) (decode : Phrase → E) (real : Fin N)
    (other : ABH (Fin N)) (adversary : Adversary N E Phrase Data) :
    (PMF.uniformOfFintype (Raw E Phrase Data)).map (plainEvent coordinates decode real other adversary)=
      (PMF.uniformOfFintype (Context Phrase Data)).bind fun context =>
        (PMF.uniformOfFintype (State × (E → Hash))).map (next coordinates decode real other adversary context) := by
  rw [law,PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def]
  rfl

omit [Nonempty E] in
/-- The raw context is independent of P and G; all D calls are replaced by decoded G padding. -/
theorem contexts (coordinates : (E × V) ≃ State) (decode : Phrase → E) (passwords : PMF (Fin N))
    (adversary : Adversary N E Phrase Data) :
    unprogrammed coordinates decode passwords adversary=
      (PMF.uniformOfFintype (Context Phrase Data)).bind fun context =>
        (Gamma2Model.game passwords (plainProgram decode context.2 context.1 adversary)).map
          (Theorem3Assembly.winOrBad (Theorem3.entropy coordinates)) := by
  unfold unprogrammed
  simp_rw [fixed]
  calc
    _ = passwords.bind (fun real => (PMF.uniformOfFintype (Context Phrase Data)).bind fun context =>
      (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
        (PMF.uniformOfFintype (State × (E → Hash))).map (next coordinates decode real other adversary context)) := by
      apply congrArg (fun f => passwords.bind f)
      funext real
      exact PMF.bind_comm _ _ _
    _ = (PMF.uniformOfFintype (Context Phrase Data)).bind (fun context => passwords.bind fun real =>
      (PMF.uniformOfFintype (ABH (Fin N))).bind fun other =>
        (PMF.uniformOfFintype (State × (E → Hash))).map (next coordinates decode real other adversary context)) :=
      PMF.bind_comm _ _ _
    _ = _ := by
      apply congrArg (fun f => (PMF.uniformOfFintype (Context Phrase Data)).bind f)
      funext context
      rw [CryptoInputs.game]
      simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
      rfl

end G10DirectContexts

namespace G10Direct
open Gamma2Model G10DirectModel G10WalletCounts GameExpectation
variable {N : Nat} {E V R Phrase Data : Type} [decE : DecidableEq E] [finE : Fintype E] [Nonempty E]
  [DecidableEq Phrase] [Fintype Phrase] [Fintype V] [Nonempty V] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype
-- Keep the abstract adversary opaque while applying the shared probability bound.
attribute [local irreducible] Gamma2Model.game Theorem3Assembly.winOrBad
  G10WalletCompiler.compile

set_option maxRecDepth 8192 in
theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (phrase : (E → Hash) → E → Phrase) (decode : Phrase → E) (decodes : ∀ g e,decode (phrase g e)=e)
    (firstHalf : E → Half)
    (projects : ∀ state,firstHalf (Theorem3.entropy coordinates state)=state.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords) (adversary : Adversary N E Phrase Data)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qD : Nat)
    (budgetA : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP isWallet ≤ qD) :
    (original coordinates hash phrase passwords adversary) true ≤
      RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qD+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  have per_context (context : G10DirectContexts.Context Phrase Data) :
      ((Gamma2Model.game passwords (plainProgram decode context.2 context.1 adversary)).map
        (Theorem3Assembly.winOrBad (Theorem3.entropy coordinates))) true ≤
        RankedMass.top passwords (kA/12+1)+
          ((qG:ENNReal)+qD+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
    have native := @G10CompiledBound.bound N E Phrase decE finE
      (Theorem3.entropy coordinates) firstHalf projects
      (G10Model.walletSpec Phrase Data) context.2 decode passwords sorted
      (fun container => adversary container context.1) p1 largest kA qB qH qG qD
    have applied := native (budgetA context.1 context.2) (budgetB context.1 context.2)
      (budgetH context.1 context.2) (budgetG context.1 context.2) (budgetOmega context.1 context.2)
    have same_program :
        (fun container => G10WalletCompiler.compile (G10Model.walletSpec Phrase Data) context.2 decode
          (adversary container context.1))=
          plainProgram decode context.2 context.1 adversary := rfl
    have packaged : G10Estimate.Holds (Theorem3.entropy coordinates)
        passwords p1 kA qB qH qG qD (plainProgram decode context.2 context.1 adversary) :=
      Eq.mp (congrArg (G10Estimate.Holds (Theorem3.entropy coordinates)
        passwords p1 kA qB qH qG qD) same_program) applied
    exact G10Estimate.expose (Theorem3.entropy coordinates) passwords p1
      kA qB qH qG qD (plainProgram decode context.2 context.1 adversary) packaged

  apply (G10DirectContexts.transfer coordinates hash phrase decode decodes passwords adversary).trans
  rw [G10DirectContexts.contexts,PMF.bind_apply]
  change moment (PMF.uniformOfFintype (G10DirectContexts.Context Phrase Data))
    (fun context => ((Gamma2Model.game passwords (plainProgram decode context.2 context.1 adversary)).map
      (Theorem3Assembly.winOrBad (Theorem3.entropy coordinates))) true) ≤ _
  exact MomentTools.bounded _ _ _ per_context

end G10Direct

namespace G10AsDirect
open Gamma2Model CryptoInputs
variable {N : Nat} {E V R Data : Type} [DecidableEq E] [Fintype E] [Nonempty E]
  [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- Keep E and split the complete joint table into its full G and Omega components. -/
def seeds : (E × G10Model.JointTable E Data) ≃ (E × G10DirectModel.Table E E Data) :=
  Equiv.prodCongr (Equiv.refl E) G10JointTables.split

/-- Exact whole-game identity; it does not identify a G-dependent composition with independent Omega. -/
theorem original (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (adversary : G10Model.Adversary N E Data) :
    G10Model.original state hash passwords adversary=
      G10DirectModel.original state hash (fun _ e => e) passwords adversary := by
  have moved := PMF.uniformOfFintype_map_of_bijective
    (seeds (E := E) (Data := Data)) seeds.bijective
  unfold G10Model.original G10DirectModel.original
  apply congrArg (fun f => passwords.bind f)
  funext real
  apply congrArg (fun f => (PMF.uniformOfFintype (ABH (Fin N))).bind f)
  funext other
  rw [← moved]
  simp only [PMF.map_comp,Function.comp_def]
  rfl

end G10AsDirect

namespace G10
open Gamma2Model G10Model G10WalletCounts GameExpectation
variable {N : Nat} {E V R Data : Type} [decE : DecidableEq E] [finE : Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [finR : Fintype R] [nonemptyR : Nonempty R] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

-- Retain the published hypotheses even though the general theorem no longer needs them.
set_option linter.unusedSectionVars false in
set_option maxRecDepth 8192 in
theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ state,firstHalf (Theorem3.entropy coordinates state)=state.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords) (adversary : Adversary N E Data)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qOmega : Nat)
    (budgetA : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP isWallet ≤ qOmega) :
    (original coordinates hash passwords adversary) true ≤
      RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qOmega+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  rw [G10AsDirect.original]
  exact G10Direct.bound coordinates hash (fun _ e => e) id (fun _ _ => rfl)
    firstHalf projects passwords sorted adversary p1 largest kA qB qH qG qOmega
    budgetA budgetB budgetH budgetG budgetOmega

end G10

namespace G10Coins
open Gamma2Model G10Model G10WalletCounts GameExpectation
variable {N : Nat} {E V R Data : Type} [decE : DecidableEq E] [finE : Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

theorem randomized {Strategy : Type} (coins : PMF Strategy) (coordinates : (E × V) ≃ State)
    (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ state,firstHalf (Theorem3.entropy coordinates state)=state.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : Strategy → Adversary N E Data) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qOmega : Nat)
    (budgetA : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP isWallet ≤ qOmega) :
    (coins.bind fun strategy => original coordinates hash passwords (adversary strategy)) true ≤
      RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qOmega+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact G10.bound coordinates hash firstHalf projects passwords sorted (adversary strategy)
    p1 largest kA qB qH qG qOmega (budgetA strategy) (budgetB strategy) (budgetH strategy)
    (budgetG strategy) (budgetOmega strategy)

end G10Coins

namespace G10Bits
open Gamma2Model G10Model G10WalletCounts
variable {N : Nat}
attribute [local instance] FiniteBits.fintype

theorem bound (tail verifier suffix width : Nat) (state_length : tail+verifier=128)
    (hash_length : verifier+suffix=256) (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : Adversary N (BitVec (128+tail)) (BitVec width)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qOmega : Nat)
    (budgetA : ∀ (data : (BitVec width)) (omega : (BitVec (128+tail)) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec (BitVec (128+tail)) (BitVec width)) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (data : (BitVec width)) (omega : (BitVec (128+tail)) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec (BitVec (128+tail)) (BitVec width)) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (data : (BitVec width)) (omega : (BitVec (128+tail)) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec (BitVec (128+tail)) (BitVec width)) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (data : (BitVec width)) (omega : (BitVec (128+tail)) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec (BitVec (128+tail)) (BitVec width)) tables omega) (adversary container data)).2.countP (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (data : (BitVec width)) (omega : (BitVec (128+tail)) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (walletSpec (BitVec (128+tail)) (BitVec width)) tables omega) (adversary container data)).2.countP isWallet ≤ qOmega) :
    (original (ShortSourceCoordinates.state tail verifier state_length)
        (BitPacking.hash verifier suffix hash_length) passwords adversary) true ≤
      RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qOmega+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  exact G10.bound (ShortSourceCoordinates.state tail verifier state_length)
    (BitPacking.hash verifier suffix hash_length) (ShortSourceCoordinates.firstHalf tail)
    (ShortSourceCoordinates.projects tail verifier state_length) passwords sorted adversary
    p1 largest kA qB qH qG qOmega budgetA budgetB budgetH budgetG budgetOmega

/-- All five source widths meet the same packing/projection interface. -/
theorem normative_widths :
    (128+0=128 ∧ 0+128=128 ∧ 128+128=256) ∧
    (128+32=160 ∧ 32+96=128 ∧ 96+160=256) ∧
    (128+64=192 ∧ 64+64=128 ∧ 64+192=256) ∧
    (128+96=224 ∧ 96+32=128 ∧ 32+224=256) ∧
    (128+128=256 ∧ 128+0=128 ∧ 0+256=256) := by decide

end G10Bits

namespace G10NoWallet
open Gamma2Model CryptoInputs
variable {N : Nat} {E V R : Type} [DecidableEq E] [Unique V]

/-- A singleton verifier coordinate cannot change any G value, including at the inverse source. -/
theorem programmed_identity (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (cipher : Equiv.Perm State) (seed : State × (E → Hash)) :
    CoordinateResampling.programmed state hash cipher seed=seed := by
  let recovered := state.symm (cipher.symm seed.1)
  have same : recovered.2=(hash (seed.2 recovered.1)).1 := Subsingleton.elim _ _
  change (seed.1,Function.update seed.2 recovered.1
    (hash.symm (recovered.2,(hash (seed.2 recovered.1)).2)))=seed
  rw [same]
  simp only [Prod.eta,Equiv.symm_apply_apply,Function.update_eq_self]

variable [Fintype E] [Nonempty E] [Fintype V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- Gamma0 already equals the actual unprogrammed Gamma2 win game, with no Bad term. -/
theorem original_plain (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) (Fin N)) :
    Theorem3.original state hash passwords adversary=
      (Gamma2Model.game passwords adversary).map DepthAssembly.wins := by
  rw [Theorem3.resampling]
  unfold Theorem3.programmed
  have same (cipher : Equiv.Perm State) : CoordinateResampling.programmed state hash cipher=
      (id : State × (E → Hash) → State × (E → Hash)) := funext (programmed_identity state hash cipher)
  simp_rw [same,PMF.map_id]
  rw [CryptoInputs.game]
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  rfl

/-- The bound holds for every adaptive program, without any query-budget restriction. -/
theorem bound (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) (Fin N)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) :
    (Theorem3.original state hash passwords adversary) true ≤ p1 := by
  rw [original_plain]
  exact DepthAssembly.guess_bound passwords adversary p1 largest

/-- Arbitrary independent private coins do not change this no-information bound. -/
theorem randomized {Strategy : Type} (coins : PMF Strategy) (state : (E × V) ≃ State)
    (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (adversary : Strategy → State → OracleComp (spec (Fin N) E) (Fin N)) (p1 : ENNReal)
    (largest : ∀ password,passwords password ≤ p1) :
    (coins.bind fun strategy => Theorem3.original state hash passwords (adversary strategy)) true ≤ p1 := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact bound state hash passwords (adversary strategy) p1 largest

end G10NoWallet

namespace G10NoWalletBits
open Gamma2Model
variable {N : Nat}
attribute [local instance] FiniteBits.fintype

/-- The empty verifier has exactly one bit-string value. -/
def uniqueVerifier : Unique (BitVec 0) where
  default := 0
  uniq value := by apply BitVec.eq_of_toNat_eq; omega

/-- No oracle budget can help identify P from an ordinary full-length container alone. -/
theorem bound (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) (BitVec 256)) (Fin N))
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) :
    (Theorem3.original (ShortSourceCoordinates.state 128 0 (by decide))
      (BitPacking.hash 0 256 (by decide)) passwords adversary) true ≤ p1 := by
  letI := uniqueVerifier
  exact G10NoWallet.bound
    (ShortSourceCoordinates.state 128 0 (by decide))
    (BitPacking.hash 0 256 (by decide)) passwords adversary p1 largest

end G10NoWalletBits

namespace G10Phrase
open Gamma2Model WalletCryptoCompiler G10WalletCounts
variable {Password E Data : Type}
abbrev Phrase (E : Type) (checksum : Nat) := E × BitVec checksum

def encode (checksum : Nat) (g : E → Hash) (e : E) : Phrase E checksum :=
  (e,(g e).extractLsb' (256-checksum) checksum)

def decode (checksum : Nat) (phrase : Phrase E checksum) : E := phrase.1

/-- Reading the entropy is valid for every phrase query, including an invalid checksum. -/
theorem decodes (checksum : Nat) (g : E → Hash) (e : E) : decode checksum (encode checksum g e)=e := rfl

/-- The derivation makes its real G call before querying the independent phrase-domain D. -/
def derive (checksum : Nat) (e : E) : OracleComp (combinedSpec (Password := Password) (Entropy := E)
      (G10Model.walletSpec (Phrase E checksum) Data)) Data := do
  let digest : Hash ← TranscriptErasure.ask
    (spec := combinedSpec (Password := Password) (Entropy := E)
      (G10Model.walletSpec (Phrase E checksum) Data)) (.inl (.g e))
  TranscriptErasure.ask
    (spec := combinedSpec (Password := Password) (Entropy := E)
      (G10Model.walletSpec (Phrase E checksum) Data)) (.inr (e,digest.extractLsb' (256-checksum) checksum))

/-- The result and both queries are preserved exactly; checksum work is not treated as free knowledge. -/
theorem execution (checksum : Nat) (tables : Tables Password E) (d : Phrase E checksum → Data)
    (e : E) :
    TranscriptErasure.execute
      (combinedAnswer (G10Model.walletSpec (Phrase E checksum) Data) tables d) (derive checksum e)=
      (d (encode checksum tables.g e),[.inl (.g e),.inr (encode checksum tables.g e)]) := by
  simp only [derive,TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,
    combinedAnswer,answer,encode,List.singleton_append]

/-- One structured derivation consumes one genuine G and one D query, with no Argon2 query. -/
theorem counts (checksum : Nat) (tables : Tables Password E) (d : Phrase E checksum → Data) (e : E) :
    let queries := (TranscriptErasure.execute
      (combinedAnswer (G10Model.walletSpec (Phrase E checksum) Data) tables d) (derive checksum e)).2
    queries.countP (crypto InverseCounts.isG)=1 ∧ queries.countP isWallet=1 ∧
      queries.countP (crypto QueryCounts.isA)=0 := by
  rw [execution]
  simp [crypto,isWallet,InverseCounts.isG,QueryCounts.isA,List.countP_cons]

/-- The analysis compiler adds its discarded padding query and retains the genuine checksum query. -/
theorem compiled_counts (checksum : Nat) (tables : Tables Password E) (d : Phrase E checksum → Data)
    (e : E) :
    (execute tables (G10WalletCompiler.compile
      (G10Model.walletSpec (Phrase E checksum) Data) d (decode checksum) (derive checksum e))).2.countP
        InverseCounts.isG=2 := by
  rw [G10WalletCompiler.execution,execution]
  simp [G10WalletCompiler.point,decode,encode,InverseCounts.isG,List.countP_cons]

/-- The entropy/checksum pair is the exact packed bit string before the public BIP39 word mapping. -/
def bits (entropy checksum : Nat) : Phrase (BitVec entropy) checksum ≃ BitVec (entropy+checksum) :=
  BitPacking.append entropy checksum

/-- These are the BIP39 entropy/checksum sizes and total word-bit lengths. -/
theorem widths : (128+4=12*11) ∧ (160+5=15*11) ∧ (192+6=18*11) ∧ (224+7=21*11) ∧ (256+8=24*11) := by decide

end G10Phrase

namespace G10ChecksumBits
open Gamma2Model G10DirectModel G10WalletCounts
variable {N : Nat}
attribute [local instance] FiniteBits.fintype

theorem bound (tail verifier suffix checksum width : Nat) (state_length : tail+verifier=128)
    (hash_length : verifier+suffix=256) (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : Adversary N (BitVec (128+tail)) (G10Phrase.Phrase (BitVec (128+tail)) checksum) (BitVec width))
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qD : Nat)
    (budgetA : ∀ (data : (BitVec width)) (omega : (G10Phrase.Phrase (BitVec (128+tail)) checksum) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec (G10Phrase.Phrase (BitVec (128+tail)) checksum) (BitVec width)) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (data : (BitVec width)) (omega : (G10Phrase.Phrase (BitVec (128+tail)) checksum) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec (G10Phrase.Phrase (BitVec (128+tail)) checksum) (BitVec width)) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (data : (BitVec width)) (omega : (G10Phrase.Phrase (BitVec (128+tail)) checksum) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec (G10Phrase.Phrase (BitVec (128+tail)) checksum) (BitVec width)) tables omega) (adversary container data)).2.countP (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (data : (BitVec width)) (omega : (G10Phrase.Phrase (BitVec (128+tail)) checksum) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec (G10Phrase.Phrase (BitVec (128+tail)) checksum) (BitVec width)) tables omega) (adversary container data)).2.countP (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (data : (BitVec width)) (omega : (G10Phrase.Phrase (BitVec (128+tail)) checksum) → (BitVec width)) container (tables : Tables (Fin N) (BitVec (128+tail))), (TranscriptErasure.execute (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec (G10Phrase.Phrase (BitVec (128+tail)) checksum) (BitVec width)) tables omega) (adversary container data)).2.countP isWallet ≤ qD) :
    (original (ShortSourceCoordinates.state tail verifier state_length)
        (BitPacking.hash verifier suffix hash_length) (G10Phrase.encode checksum) passwords adversary) true ≤
      RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qD+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal) := by
  exact G10Direct.bound (ShortSourceCoordinates.state tail verifier state_length)
    (BitPacking.hash verifier suffix hash_length) (G10Phrase.encode checksum)
    (G10Phrase.decode checksum) (G10Phrase.decodes checksum)
    (ShortSourceCoordinates.firstHalf tail)
    (ShortSourceCoordinates.projects tail verifier state_length) passwords sorted adversary
    p1 largest kA qB qH qG qD budgetA budgetB budgetH budgetG budgetOmega

end G10ChecksumBits

namespace G10DirectEnvironment
open Gamma2Model TableFactors CryptoInputs ProbabilityTools
variable {N : Nat} {E V R Phrase Data : Type}
attribute [local instance] FiniteBits.fintype
abbrev AB := ShortSourceEnvironment.AB (N := N)
abbrev Context := Fin N × AB (N := N) × (E × G10DirectModel.Table E Phrase Data)

def packed (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (context : Context (N := N) (E := E) (Phrase := Phrase) (Data := Data)) : State :=
  state (context.2.2.1,(hash (context.2.2.2.1 context.2.2.1)).1)

def crypto (context : Context (N := N) (E := E) (Phrase := Phrase) (Data := Data)) (h : HTable) : Tables (Fin N) E :=
  ⟨context.2.1.1,context.2.1.2,h,context.2.2.2.1⟩

def score (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (phrase : (E → Hash) → E → Phrase)
    (adversary : G10DirectModel.Adversary N E Phrase Data)
    (sample : Context (N := N) (E := E) (Phrase := Phrase) (Data := Data) × HTable) : Bool :=
  let context := sample.1
  decide ((TranscriptErasure.execute
    (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data)
      (crypto context sample.2) context.2.2.2.2)
    (adversary (KnownPairModel.cipher context.1 context.2.1.1 context.2.1.2 sample.2 (packed state hash context))
      (context.2.2.2.2 (phrase context.2.2.2.1 context.2.2.1)))).1=context.1)

variable [DecidableEq E] [DecidableEq Phrase] [Fintype E] [Nonempty E] [Fintype Phrase] [Fintype Data] [Nonempty Data]

def contexts (passwords : PMF (Fin N)) : PMF (Context (N := N) (E := E) (Phrase := Phrase) (Data := Data)) :=
  passwords.bind fun password => (PMF.uniformOfFintype (AB (N := N))).bind fun ab =>
    (PMF.uniformOfFintype (E × G10DirectModel.Table E Phrase Data)).map fun input => (password,ab,input)

def initial (passwords : PMF (Fin N)) :=
  ExactRefusalLift.initial (contexts (E := E) (Phrase := Phrase) (Data := Data) passwords) CryptoUniform.h

/-- This is the same AB/H product factor as the short-source environment, retaining the actual H sampler. -/
theorem factor : PMF.uniformOfFintype (ABH (Fin N))= (PMF.uniformOfFintype (AB (N := N))).bind fun ab =>
      CryptoUniform.h.map fun h => (ab.1,ab.2,h) := by
  have moved := PMF.uniformOfFintype_map_of_bijective
    (Equiv.prodAssoc (ATable (Fin N)) BTable HTable) (Equiv.prodAssoc (ATable (Fin N)) BTable HTable).bijective
  rw [← moved,uniform_product]
  simp only [independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def,CryptoUniform.h]
  rfl

/-- The complete direct-D source experiment has exactly this H-last environment law. -/
theorem original (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (phrase : (E → Hash) → E → Phrase)
    (passwords : PMF (Fin N)) (adversary : G10DirectModel.Adversary N E Phrase Data) :
    G10DirectModel.original state hash phrase passwords adversary=
      (initial passwords).map (score state hash phrase adversary) := by
  unfold G10DirectModel.original
  rw [factor]
  unfold initial ExactRefusalLift.initial contexts
  simp only [PMF.map_bind,PMF.map_comp,PMF.bind_bind,PMF.bind_map,Function.comp_def,score,crypto,packed,
    G10DirectModel.score,G10DirectModel.combined,G10DirectLaw.original,
    Theorem3.cipher,tables]
  apply congrArg (fun next => passwords.bind next)
  funext password
  apply congrArg (fun next => (PMF.uniformOfFintype (AB (N := N))).bind next)
  funext ab
  exact PMF.bind_comm _ _ _

end G10DirectEnvironment

namespace G10DirectRefusal
open Gamma2Model TableFactors G10DirectEnvironment
variable {N : Nat} {E V R Phrase Data : Type}

def refused (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (sample : Context (N := N) (E := E) (Phrase := Phrase) (Data := Data) × HTable) : Bool :=
  ExactRefusalLift.refused (fun context h =>
    KnownPairModel.cipher context.1 context.2.1.1 context.2.1.2 h (packed state hash context))
    (packed state hash) sample

variable [DecidableEq E] [DecidableEq Phrase] [Fintype E] [Nonempty E]
  [Fintype Phrase] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- The comparison is on the original256-bit packed state; public data is not added to that state. -/
theorem probability (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N)) :
    ((initial (E := E) (Phrase := Phrase) (Data := Data) passwords).map (refused state hash)) true=
      (2^256:ENNReal)⁻¹ :=
  G9Game.probability (contexts passwords) (fun context => context.1)
    (fun context => context.2.1.1) (fun context => context.2.1.2) (packed state hash)

def game (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (phrase : (E → Hash) → E → Phrase)
    (passwords : PMF (Fin N)) (adversary : G10DirectModel.Adversary N E Phrase Data)
    (later : Context (N := N) (E := E) (Phrase := Phrase) (Data := Data) × HTable → PMF Bool) : PMF Bool :=
  RefusalResponse.game (initial passwords) (refused state hash) (score state hash phrase adversary) later

/-- Arbitrary reporting/retry behavior after the first refusal costs at most the exact G9 term. -/
theorem bound (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (phrase : (E → Hash) → E → Phrase)
    (passwords : PMF (Fin N)) (adversary : G10DirectModel.Adversary N E Phrase Data)
    (later : Context (N := N) (E := E) (Phrase := Phrase) (Data := Data) × HTable → PMF Bool)
    (upper : ENNReal)
    (source : (G10DirectModel.original state hash phrase passwords adversary) true ≤ upper) :
    (game state hash phrase passwords adversary later) true ≤ upper+(2^256:ENNReal)⁻¹ := by
  rw [G10DirectEnvironment.original] at source
  have result := RefusalResponse.bound (initial passwords) (refused state hash)
    (score state hash phrase adversary) later upper source
  rw [probability] at result
  exact result

end G10DirectRefusal

namespace G10DirectRefusalBound
open Gamma2Model G10DirectModel G10WalletCounts GameExpectation
variable {N : Nat} {E V R Phrase Data : Type} [decE : DecidableEq E] [finE : Fintype E] [Nonempty E]
  [DecidableEq Phrase] [Fintype Phrase] [Fintype V] [Nonempty V] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (phrase : (E → Hash) → E → Phrase) (decode : Phrase → E) (decodes : ∀ g e,decode (phrase g e)=e)
    (firstHalf : E → Half) (projects : ∀ state,firstHalf (Theorem3.entropy coordinates state)=state.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords) (adversary : Adversary N E Phrase Data)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qD : Nat)
    (budgetA : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP
          (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP
          (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP
          (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP
          (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary container data)).2.countP
          isWallet ≤ qD)    (later : G10DirectEnvironment.Context (N := N) (E := E) (Phrase := Phrase) (Data := Data)
      × TableFactors.HTable → PMF Bool) :
    (G10DirectRefusal.game coordinates hash phrase passwords adversary later) true ≤
      (RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qD+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal))+(2^256:ENNReal)⁻¹ := by
  apply G10DirectRefusal.bound coordinates hash phrase passwords adversary later
  exact G10Direct.bound coordinates hash phrase decode decodes firstHalf projects passwords sorted adversary
    p1 largest kA qB qH qG qD budgetA budgetB budgetH budgetG budgetOmega

end G10DirectRefusalBound

namespace G10DirectRefusalCoins
open Gamma2Model G10DirectModel G10WalletCounts GameExpectation
variable {N : Nat} {E V R Phrase Data : Type} [decE : DecidableEq E] [finE : Fintype E] [Nonempty E]
  [DecidableEq Phrase] [Fintype Phrase] [Fintype V] [Nonempty V] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

theorem randomized {Strategy : Type} (coins : PMF Strategy) (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (phrase : (E → Hash) → E → Phrase) (decode : Phrase → E) (decodes : ∀ g e,decode (phrase g e)=e)
    (firstHalf : E → Half) (projects : ∀ state,firstHalf (Theorem3.entropy coordinates state)=state.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords) (adversary : Strategy → Adversary N E Phrase Data)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qD : Nat)
    (budgetA : ∀ (strategy : Strategy) (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary strategy container data)).2.countP
          (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (strategy : Strategy) (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary strategy container data)).2.countP
          (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (strategy : Strategy) (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary strategy container data)).2.countP
          (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (strategy : Strategy) (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary strategy container data)).2.countP
          (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (strategy : Strategy) (data : Data) (omega : Phrase → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec Phrase Data) tables omega) (adversary strategy container data)).2.countP
          isWallet ≤ qD)    (later : Strategy → G10DirectEnvironment.Context (N := N) (E := E) (Phrase := Phrase) (Data := Data)
      × TableFactors.HTable → PMF Bool) :
    (coins.bind fun strategy => G10DirectRefusal.game coordinates hash phrase passwords (adversary strategy) (later strategy)) true ≤
      (RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qD+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal))+(2^256:ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact G10DirectRefusalBound.bound coordinates hash phrase decode decodes firstHalf projects
    passwords sorted (adversary strategy) p1 largest kA qB qH qG qD
    (budgetA strategy) (budgetB strategy) (budgetH strategy) (budgetG strategy) (budgetOmega strategy) (later strategy)

end G10DirectRefusalCoins

namespace G10Refusal
open Gamma2Model G10Model G10WalletCounts GameExpectation
variable {N : Nat} {E V R Data : Type} [decE : DecidableEq E] [finE : Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (firstHalf : E → Half) (projects : ∀ state,firstHalf (Theorem3.entropy coordinates state)=state.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords) (adversary : Adversary N E Data)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qOmega : Nat)
    (budgetA : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP
          (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP
          (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP
          (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP
          (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary container data)).2.countP
          isWallet ≤ qOmega)    (later : G10DirectEnvironment.Context (N := N) (E := E) (Phrase := E) (Data := Data)
      × TableFactors.HTable → PMF Bool) :
    (G10DirectRefusal.game coordinates hash (fun _ e => e) passwords adversary later) true ≤
      (RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qOmega+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal))+(2^256:ENNReal)⁻¹ := by
  apply G10DirectRefusal.bound coordinates hash (fun _ e => e) passwords adversary later
  rw [← G10AsDirect.original]
  exact G10.bound coordinates hash firstHalf projects passwords sorted adversary
    p1 largest kA qB qH qG qOmega budgetA budgetB budgetH budgetG budgetOmega

end G10Refusal

namespace G10RefusalCoins
open Gamma2Model G10Model G10WalletCounts GameExpectation
variable {N : Nat} {E V R Data : Type} [decE : DecidableEq E] [finE : Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

theorem randomized {Strategy : Type} (coins : PMF Strategy) (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R))
    (firstHalf : E → Half) (projects : ∀ state,firstHalf (Theorem3.entropy coordinates state)=state.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords) (adversary : Strategy → Adversary N E Data)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG qOmega : Nat)
    (budgetA : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP
          (crypto QueryCounts.isA) ≤ kA)
    (budgetB : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP
          (crypto QueryCounts.isB) ≤ qB)
    (budgetH : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP
          (crypto QueryCounts.isH) ≤ qH)
    (budgetG : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP
          (crypto InverseCounts.isG) ≤ qG)
    (budgetOmega : ∀ (strategy : Strategy) (data : Data) (omega : E → Data) container (tables : Tables (Fin N) E),
      (TranscriptErasure.execute
        (WalletCryptoCompiler.combinedAnswer (walletSpec E Data) tables omega) (adversary strategy container data)).2.countP
          isWallet ≤ qOmega)    (later : Strategy → G10DirectEnvironment.Context (N := N) (E := E) (Phrase := E) (Data := Data)
      × TableFactors.HTable → PMF Bool) :
    (coins.bind fun strategy => G10DirectRefusal.game coordinates hash (fun _ e => e) passwords (adversary strategy) (later strategy)) true ≤
      (RankedMass.top passwords (kA/12+1)+
        ((qG:ENNReal)+qOmega+qB+12*p1*kA+66)/(2^128:ENNReal)+qH/(2^256:ENNReal))+(2^256:ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact G10Refusal.bound coordinates hash firstHalf projects passwords sorted (adversary strategy)
    p1 largest kA qB qH qG qOmega (budgetA strategy) (budgetB strategy) (budgetH strategy)
    (budgetG strategy) (budgetOmega strategy) (later strategy)

end G10RefusalCoins

end
end MhfeLean
