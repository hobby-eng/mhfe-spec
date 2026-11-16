/- long: the original wallet-check source game and Theorem 5 assembly share one context. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Data.Fin.Tuple.Basic
import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.GenerationBound
import MhfeLean.Chapters.GenerationSampling
import MhfeLean.Chapters.OracleModel
import MhfeLean.Chapters.PasswordPairs
import MhfeLean.Chapters.Probability
import MhfeLean.Chapters.SeedPairs
import MhfeLean.Chapters.ShortSources
import MhfeLean.Chapters.WalletCollision
import MhfeLean.Chapters.WalletResampling

namespace MhfeLean
noncomputable section

/-! # Theorem 5: original source games, refusal, coins and bit widths
-/

/-! Identical-until-query for the three actual wallet-oracle points programmed in Theta1. -/
namespace WalletProgramming
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

abbrev WalletTables := SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data
abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data

/-- T retains its original suffix, exactly as in Theta1. -/
def updated (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (target : Check) (data : Data) : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) :=
  ⟨Function.update wallet.s (entropy,phrase) seed,
   Function.update wallet.t seed (target,(wallet.t seed).2),Function.update wallet.omega seed data⟩

/-- The real output and the entire full query log agree unless one of the three changed points was read. -/
theorem execution (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result)
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (target : Check) (data : Data)
    (missingS : Sum.inr (.s entropy phrase) ∉ (TranscriptErasure.execute
      (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2)
    (missingT : Sum.inr (.t seed) ∉ (TranscriptErasure.execute
      (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2)
    (missingOmega : Sum.inr (.omega seed) ∉ (TranscriptErasure.execute
      (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2) :
    TranscriptErasure.execute (combinedAnswer WalletSpec crypto
      (SeedWalletModel.answer (updated wallet entropy phrase seed target data))) program =
    TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program := by
  apply TranscriptErasure.execute_agree program
    (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet))
    (combinedAnswer WalletSpec crypto (SeedWalletModel.answer (updated wallet entropy phrase seed target data)))
  intro point member
  cases point with
  | inl point => rfl
  | inr point =>
    cases point with
    | s candidate guess =>
      have different : (candidate,guess) ≠ (entropy,phrase) := by
        intro equal
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
        exact missingS member
      exact Function.update_of_ne different _ _
    | t candidate =>
      have different : candidate ≠ seed := by intro equal; subst candidate; exact missingT member
      exact Function.update_of_ne different _ _
    | omega candidate =>
      have different : candidate ≠ seed := by intro equal; subst candidate; exact missingOmega member
      exact Function.update_of_ne different _ _

end WalletProgramming

/-! Freeze crypto and Omega while keeping actual S/T calls available to the generation-coupling proof. -/
namespace WalletGenerationCompiler
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
abbrev WalletPoint := SeedWalletModel.Point Entropy Passphrase Seed
abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev GenerationSpec := WalletGeneration.spec Entropy Passphrase Seed Check Tail
abbrev FullPoint := Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed

/-- Read only S/T from the selected oracle; the independent tables are fixed external context. -/
def compile (crypto : Tables Password Entropy) (omega : Seed → Data)
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result) :
    OracleComp (GenerationSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))
      (Result × List (FullPoint (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))) :=
  OracleComp.construct (fun result => pure (result,[]))
    (fun point _ recurse => match point with
      | .inl point => do
        let later ← recurse (answer crypto point)
        pure (later.1,Sum.inl point::later.2)
      | .inr (.s entropy phrase) => do
        let value : Seed ← TranscriptErasure.ask (spec := GenerationSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) (.s entropy phrase)
        let later ← recurse value
        pure (later.1,Sum.inr (.s entropy phrase)::later.2)
      | .inr (.t seed) => do
        let value : Check × Tail ← TranscriptErasure.ask (spec := GenerationSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) (.t seed)
        let later ← recurse value
        pure (later.1,Sum.inr (.t seed)::later.2)
      | .inr (.omega seed) => do
        let later ← recurse (omega seed)
        pure (later.1,Sum.inr (.omega seed)::later.2)) program

def selected : FullPoint (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) →
    Option (WalletGeneration.Point Entropy Passphrase Seed)
  | .inr (.s entropy phrase) => some (.s entropy phrase)
  | .inr (.t seed) => some (.t seed)
  | _ => none

def wallet (table : TranscriptErasure.Table
    (GenerationSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)))
    (omega : Seed → Data) : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data :=
  ⟨fun pair => table (.s pair.1 pair.2),fun seed => table (.t seed),omega⟩

theorem compile_query (crypto : Tables Password Entropy) (omega : Seed → Data)
    (point : FullPoint (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))
    (next : combinedSpec (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) point →
      OracleComp (combinedSpec (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result) :
    compile crypto omega (TranscriptErasure.ask point >>= next) =
      (match point with
      | .inl point => do
        let later ← compile crypto omega (next (answer crypto point))
        pure (later.1,Sum.inl point::later.2)
      | .inr (.s entropy phrase) => do
        let value : Seed ← TranscriptErasure.ask (spec := GenerationSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) (.s entropy phrase)
        let later ← compile crypto omega (next value)
        pure (later.1,Sum.inr (.s entropy phrase)::later.2)
      | .inr (.t seed) => do
        let value : Check × Tail ← TranscriptErasure.ask (spec := GenerationSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) (.t seed)
        let later ← compile crypto omega (next value)
        pure (later.1,Sum.inr (.t seed)::later.2)
      | .inr (.omega seed) => do
        let later ← compile crypto omega (next (omega seed))
        pure (later.1,Sum.inr (.omega seed)::later.2)) := by
  cases point with
  | inl point => rfl
  | inr point => cases point <;> rfl

theorem compile_pure (crypto : Tables Password Entropy) (omega : Seed → Data) (result : Result) :
    compile (Entropy := Entropy) (Passphrase := Passphrase) (Check := Check) (Tail := Tail) crypto omega (pure result)=pure (result,[]) := rfl

attribute [local irreducible] compile

/-- The retained full trace and the emitted S/T trace both match the actual adaptive execution. -/
theorem execution (crypto : Tables Password Entropy) (omega : Seed → Data)
    (table : TranscriptErasure.Table
      (GenerationSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)))
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result) :
    TranscriptErasure.execute table (compile crypto omega program)=
      let full := TranscriptErasure.execute (combinedAnswer WalletSpec crypto
        (SeedWalletModel.answer (wallet table omega))) program
      ((full.1,full.2),full.2.filterMap selected) := by
  induction program using OracleComp.inductionOn with
  | pure result => rw [compile_pure]; rfl
  | query_bind point next ih =>
    change TranscriptErasure.execute table (compile crypto omega (TranscriptErasure.ask point >>= next)) =
      let full := TranscriptErasure.execute (combinedAnswer WalletSpec crypto
        (SeedWalletModel.answer (wallet table omega))) (TranscriptErasure.ask point >>= next)
      ((full.1,full.2),full.2.filterMap selected)
    rw [compile_query]
    cases point with
    | inl point =>
      simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_pure,ih,List.append_nil]
      rfl
    | inr point =>
      cases point with
      | s entropy phrase =>
        simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,
          TranscriptErasure.execute_pure,ih,List.append_nil,List.singleton_append]
        rfl
      | t seed =>
        simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,
          TranscriptErasure.execute_pure,ih,List.append_nil,List.singleton_append]
        rfl
      | omega seed =>
        simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_pure,ih,List.append_nil]
        rfl

end WalletGenerationCompiler

/-! The S/T generation compiler preserves both budgets used in delta_gen. -/
namespace GenerationQueryCounts
open WalletGenerationCompiler
variable {Password Entropy Passphrase Seed : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

omit [DecidableEq Entropy] [DecidableEq Seed] in
/-- Selecting one hidden passphrase and deduplicating can only reduce the full seed-query budget. -/
theorem seed_length (phrase : Passphrase)
    (queries : List (FullPoint (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))) :
    (WalletQuerySets.sList phrase (queries.filterMap selected)).length ≤
      (SeedWalletModel.seedPairs queries).length := by
  induction queries with
  | nil => rfl
  | cons point rest ih =>
    cases point with
    | inl point => simpa [selected,WalletQuerySets.sList,SeedWalletModel.seedPairs,
        SeedQueryMetadata.extract,SeedWalletModel.seedPair,List.filterMap_cons] using ih
    | inr point =>
      cases point with
      | s entropy guess =>
        by_cases same : guess=phrase <;>
          simp [selected,WalletQuerySets.sList,SeedWalletModel.seedPairs,
            SeedQueryMetadata.extract,SeedWalletModel.seedPair,same,List.filterMap_cons] at ih ⊢ <;> omega
      | t seed => simpa [selected,WalletQuerySets.sList,SeedWalletModel.seedPairs,
          SeedQueryMetadata.extract,SeedWalletModel.seedPair,List.filterMap_cons] using ih
      | omega seed => simpa [selected,WalletQuerySets.sList,SeedWalletModel.seedPairs,
          SeedQueryMetadata.extract,SeedWalletModel.seedPair,List.filterMap_cons] using ih

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] in
/-- Omega reads are fixed context, so they are not inadvertently charged as T queries. -/
theorem tag_length
    (queries : List (FullPoint (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))) :
    (WalletQuerySets.tList (queries.filterMap selected)).length =
      queries.countP SeedWalletModel.isT := by
  induction queries with
  | nil => rfl
  | cons point rest ih =>
    cases point with
    | inl point => simpa [selected,WalletQuerySets.tList,SeedWalletModel.isT,List.filterMap_cons,
        List.countP_cons] using ih
    | inr point => cases point <;> simpa [selected,WalletQuerySets.tList,SeedWalletModel.isT,
        List.filterMap_cons,List.countP_cons] using ih

/-- These are consequences of actual full-trace budgets, including all repeated primitive calls. -/
theorem bounds (phrase : Passphrase)
    (queries : List (FullPoint (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)))
    (kS qT : Nat) (sBudget : (SeedWalletModel.seedPairs queries).length ≤ kS)
    (tBudget : queries.countP SeedWalletModel.isT ≤ qT) :
    (WalletQuerySets.sSet phrase (queries.filterMap selected)).card ≤ kS ∧
      (WalletQuerySets.tSet (queries.filterMap selected)).card ≤ qT := by
  constructor
  · exact (List.toFinset_card_le _).trans ((seed_length phrase queries).trans sBudget)
  · exact (List.toFinset_card_le _).trans ((tag_length queries).le.trans tBudget)

end GenerationQueryCounts

/-! W2 applies to the actual crypto+wallet adversary, including the public wallet data of the selected seed. -/
namespace FullGenerationCoupling
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}

/-- Only Y and Omega(seed*) are supplied to the actual program; rejected trials are never supplied. -/
def program (crypto : Tables Password Entropy) (omega : Seed → Data) (container : Entropy → State)
    (adversary : Data → State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data)) Result)
    (chosen : WalletGeneration.Selected Entropy Seed Tail) :=
  WalletGenerationCompiler.compile crypto omega (adversary (omega chosen.seed) (container chosen.entropy))

variable [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

/-- The entire chosen triple, adversary output and both exact logs have distance at most delta_gen. -/
theorem bound (crypto : Tables Password Entropy) (omega : Seed → Data) (container : Entropy → State)
    (adversary : Data → State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data)) Result)
    (phrase : Passphrase) (target : Check) (kS qT : Nat)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16)
    (sBudget : ∀ (chosen : WalletGeneration.Selected Entropy Seed Tail) table,
      (SeedWalletModel.seedPairs (TranscriptErasure.execute
        (combinedAnswer (SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data) crypto
          (SeedWalletModel.answer (WalletGenerationCompiler.wallet table omega)))
        (adversary (omega chosen.seed) (container chosen.entropy))).2).length ≤ kS)
    (tBudget : ∀ (chosen : WalletGeneration.Selected Entropy Seed Tail) table,
      (TranscriptErasure.execute
        (combinedAnswer (SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data) crypto
          (SeedWalletModel.answer (WalletGenerationCompiler.wallet table omega)))
        (adversary (omega chosen.seed) (container chosen.entropy))).2.countP SeedWalletModel.isT ≤ qT) :
    StatisticalClose.Close
      (WalletUnbounded.real phrase target (program crypto omega container adversary))
      (WalletCapped.planted phrase target (program crypto omega container adversary))
      (W2.delta kS qT) := by
  apply W2.finite_generation_bound phrase target (program crypto omega container adversary)
    entropyWidth seedWidth checkWidth kS qT
  · intro chosen table
    rw [program,WalletGenerationCompiler.execution]
    exact (GenerationQueryCounts.bounds phrase _ kS qT (sBudget chosen table) (tBudget chosen table)).1
  · intro chosen table
    rw [program,WalletGenerationCompiler.execution]
    exact (GenerationQueryCounts.bounds phrase _ kS qT (sBudget chosen table) (tBudget chosen table)).2

end FullGenerationCoupling

/-! Full 256-bit source coordinates and the actual inverse source used in Theorem 5. -/
namespace FullSourceCoordinates
open Gamma2Model KnownPairModel
variable {Entropy Password : Type}
attribute [local irreducible] finalize

/-- The 24-word source has no padding or verifier bits. -/
def bits : BitVec 256 ≃ State := (BitPacking.append 128 128).symm

def firstHalf (coordinates : Entropy ≃ State) (entropy : Entropy) : Half := (coordinates entropy).1

/-- The state-to-entropy map is a bijection, and preserves the exact leading half. -/
theorem projects (coordinates : Entropy ≃ State) (state : State) :
    firstHalf coordinates (coordinates.symm state)=state.1 := by
  rw [firstHalf,Equiv.apply_symm_apply]

def cipher (coordinates : Entropy ≃ State) (password : Password) (tables : Tables Password Entropy) :
    Equiv.Perm Entropy :=
  (coordinates.trans (roundsEquiv (allMasks password tables.a tables.b tables.h))).trans coordinates.symm

/-- The programmed S input is the original entropy of the actual inverse chain, not a guessed source. -/
theorem inverse (coordinates : Entropy ≃ State) (password : Password)
    (tables : Tables Password Entropy) (container : Entropy) :
    (cipher coordinates password tables).symm container=
      coordinates.symm (W4Model.recovered password (coordinates container) tables) := by
  apply congrArg coordinates.symm
  exact (CipherExecution.inverse password (coordinates container) tables).symm

end FullSourceCoordinates

/-! The planted generation experiment is exactly W3's full joint source observation. -/
namespace FullPlantedResampling
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev Program := Data → State → OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
  (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result
abbrev Observation := W3.Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
  (Check := Check) (Tail := Tail) (Wallet := Data)

/-- Only the container and the challenged wallet data enter the actual adversary. -/
def score (coordinates : Entropy ≃ State) (crypto : Tables Password Entropy)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Seed → Result → Bool)
    (observation : Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) : Bool :=
  let ⟨_,container,seed,s,t,omega,data⟩ := observation
  test seed (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
    (SeedWalletModel.answer ⟨s,t,omega⟩)) (adversary data (coordinates container))).1

/-- Selected-triple instrumentation adds no information to the actual program inputs. -/
theorem planted_score (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check) (omega : Seed → Data)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Seed → Result → Bool) (chosen : WalletGeneration.Selected Entropy Seed Tail)
    (table : TranscriptErasure.Table (WalletGeneration.spec Entropy Passphrase Seed Check Tail)) :
    test chosen.seed
      (TranscriptErasure.execute (WalletGeneration.restore phrase target (some chosen) table)
        (FullGenerationCoupling.program crypto omega
          (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates password crypto entropy)) adversary chosen)).1.1 =
    score coordinates crypto adversary test
      (W3Source.observation (FullSourceCoordinates.cipher coordinates password crypto) phrase target chosen table omega) := by
  rw [FullGenerationCoupling.program,WalletGenerationCompiler.execution]
  rfl

variable [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]

def original (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool) : PMF Bool :=
  (W3Source.original (Tail := Tail) (Wallet := Data)
    (FullSourceCoordinates.cipher coordinates password crypto) phrase target).map (score coordinates crypto adversary test)

def programmed (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool) : PMF Bool :=
  ((PMF.uniformOfFintype (W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind
    (W3.programmed (Tail := Tail) (Wallet := Data)
      (FullSourceCoordinates.cipher coordinates password crypto) phrase target)).map (score coordinates crypto adversary test)

/-- This is actual W3 applied to the concrete twelve-round cipher in the source's bit coordinates. -/
theorem resampling (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool) :
    original coordinates password crypto phrase target adversary test=
      programmed coordinates password crypto phrase target adversary test := by
  unfold original programmed
  rw [W3Source.resampling]

end FullPlantedResampling

/-! Membership views of the actual full S/T/Omega query log. -/
namespace WalletQueryMembership
variable {Password Entropy Passphrase Seed : Type}

theorem seed_pair
    (queries : List (Gamma2Model.Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed))
    (entropy : Entropy) (phrase : Passphrase) :
    (entropy,phrase) ∈ SeedWalletModel.seedPairs queries ↔ Sum.inr (.s entropy phrase) ∈ queries := by
  induction queries with
  | nil => simp [SeedWalletModel.seedPairs]
  | cons point rest ih =>
    simp only [SeedWalletModel.seedPairs] at ih ⊢
    cases point with
    | inl point => simpa [SeedQueryMetadata.extract,SeedWalletModel.seedPair,List.filterMap_cons] using ih
    | inr point => cases point <;> simp [SeedQueryMetadata.extract,SeedWalletModel.seedPair,ih,
        List.filterMap_cons]

theorem blind_seed
    (queries : List (Gamma2Model.Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed))
    (seed : Seed) :
    seed ∈ SeedWalletModel.blindSeeds queries ↔ Sum.inr (.t seed) ∈ queries ∨ Sum.inr (.omega seed) ∈ queries := by
  induction queries with
  | nil => simp [SeedWalletModel.blindSeeds]
  | cons point rest ih =>
    simp only [SeedWalletModel.blindSeeds] at ih ⊢
    cases point with
    | inl point => simpa [SeedWalletModel.blindSeed,List.filterMap_cons] using ih
    | inr point => cases point <;> simp [SeedWalletModel.blindSeed,ih,or_assoc,or_comm,or_left_comm,
        List.filterMap_cons]

end WalletQueryMembership

/-! Only the combined win-or-Bad event is used to remove the three programmed wallet points. -/
namespace WalletProgrammingTransfer
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev WalletTables := SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data

def bad (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result)
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) : Bool := by
  classical
  let queries := (TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2
  exact decide (Sum.inr (.s entropy phrase) ∈ queries ∨ Sum.inr (.t seed) ∈ queries ∨ Sum.inr (.omega seed) ∈ queries)

/-- Both the adaptive result and the transcript are preserved off Bad, even when the test uses P,Q or seed*. -/
theorem pointwise (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result)
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (target : Check) (data : Data) (test : Result → Bool) :
    (if test (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
        (SeedWalletModel.answer (WalletProgramming.updated wallet entropy phrase seed target data))) program).1 then 1 else 0 : ENNReal) ≤
    if test (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
        (SeedWalletModel.answer wallet)) program).1 || bad crypto wallet program entropy phrase seed then 1 else 0 := by
  classical
  by_cases changed : bad crypto wallet program entropy phrase seed=true
  · simp only [changed,Bool.or_true]
    split_ifs <;> simp only [le_refl,zero_le]
  · have missing : ¬(Sum.inr (.s entropy phrase) ∈
        (TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2 ∨
        Sum.inr (.t seed) ∈ (TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2 ∨
        Sum.inr (.omega seed) ∈ (TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2) := by
      exact of_decide_eq_false (Bool.eq_false_iff.mpr changed)
    have same := WalletProgramming.execution crypto wallet program entropy phrase seed target data
      (fun member => missing (Or.inl member)) (fun member => missing (Or.inr (Or.inl member)))
      (fun member => missing (Or.inr (Or.inr member)))
    rw [same]
    simp only [Bool.eq_false_iff.mpr changed,Bool.or_false,le_refl]

end WalletProgrammingTransfer

/-! Express the programming transfer in the exact S-pair and blind-seed events of Theta2. -/
namespace WalletQueryEvent
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev WalletTables := SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data

def winOrBad (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result)
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (test : Result → Bool) : Bool := by
  classical
  let run := TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program
  exact decide (test run.1=true ∨ (entropy,phrase) ∈ SeedWalletModel.seedPairs run.2 ∨
    seed ∈ SeedWalletModel.blindSeeds run.2)

/-- This transfers the union only; it makes no assertion that separate Bad components retain their probabilities. -/
theorem pointwise (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
      (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result)
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (target : Check) (data : Data) (test : Result → Bool) :
    (if test (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
        (SeedWalletModel.answer (WalletProgramming.updated wallet entropy phrase seed target data))) program).1 then 1 else 0 : ENNReal) ≤
      if winOrBad crypto wallet program entropy phrase seed test then 1 else 0 := by
  classical
  apply (WalletProgrammingTransfer.pointwise crypto wallet program entropy phrase seed target data test).trans
  let run := TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program
  by_cases enabled : (test run.1 || WalletProgrammingTransfer.bad crypto wallet program entropy phrase seed)=true
  · have good : winOrBad crypto wallet program entropy phrase seed test=true := by
      unfold winOrBad
      simp only [decide_eq_true_eq]
      rcases Bool.or_eq_true_iff.mp enabled with win | bad
      · exact Or.inl win
      · have details : Sum.inr (.s entropy phrase) ∈ run.2 ∨ Sum.inr (.t seed) ∈ run.2 ∨ Sum.inr (.omega seed) ∈ run.2 :=
          of_decide_eq_true bad
        rcases details with s | t | omega
        · exact Or.inr (Or.inl ((WalletQueryMembership.seed_pair run.2 entropy phrase).mpr s))
        · exact Or.inr (Or.inr ((WalletQueryMembership.blind_seed run.2 seed).mpr (Or.inl t)))
        · exact Or.inr (Or.inr ((WalletQueryMembership.blind_seed run.2 seed).mpr (Or.inr omega)))
    change (if test run.1 || WalletProgrammingTransfer.bad crypto wallet program entropy phrase seed then 1 else 0 : ENNReal) ≤ _
    rw [enabled,good]
  · change (if test run.1 || WalletProgrammingTransfer.bad crypto wallet program entropy phrase seed then 1 else 0 : ENNReal) ≤ _
    simp only [Bool.eq_false_iff.mpr enabled,Bool.false_eq_true,if_false,zero_le]

end WalletQueryEvent

/-! Remove the three programmed wallet points while retaining the exact source coordinate of the real inverse. -/
namespace FullPlantedTransfer
open Gamma2Model GameExpectation MomentTools
open FullPlantedResampling
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

/-- All unprogrammed functions and public data are retained; only the win-or-Bad test reads the real secrets. -/
def rawScore (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool)
    (container : Entropy) (seed : Seed) (s : W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))
    (t : W3.TTable (Seed := Seed) (Check := Check) (Tail := Tail)) (omega : Seed → Data) (data : Data) : Bool :=
  WalletQueryEvent.winOrBad crypto ⟨s,t,omega⟩ (adversary data (coordinates container))
    ((FullSourceCoordinates.cipher coordinates password crypto).symm container) phrase seed (test seed)

/-- This is the actual operational programming argument, before any exchange of probability samplers. -/
theorem pointwise (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool)
    (container : Entropy) (seed : Seed) (s : W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))
    (t : W3.TTable (Seed := Seed) (Check := Check) (Tail := Tail)) (omega : Seed → Data) (data : Data) :
    (if score coordinates crypto adversary test
      ((FullSourceCoordinates.cipher coordinates password crypto).symm container,container,seed,
        Function.update s ((FullSourceCoordinates.cipher coordinates password crypto).symm container,phrase) seed,
        Function.update t seed (target,(t seed).2),Function.update omega seed data,data) then 1 else 0 : ENNReal) ≤
      if rawScore coordinates password crypto phrase adversary test container seed s t omega data then 1 else 0 :=
  WalletQueryEvent.pointwise crypto ⟨s,t,omega⟩ (adversary data (coordinates container))
    ((FullSourceCoordinates.cipher coordinates password crypto).symm container) phrase seed target data (test seed)

variable [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]

def raw (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool) : PMF Bool :=
  (PMF.uniformOfFintype (W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind fun s =>
    (PMF.uniformOfFintype Entropy).bind fun container =>
      (PMF.uniformOfFintype Seed).bind fun seed =>
        (PMF.uniformOfFintype (W3.TTable (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun t =>
          (PMF.uniformOfFintype Data).bind fun data =>
            (PMF.uniformOfFintype (Seed → Data)).map fun omega =>
              rawScore coordinates password crypto phrase adversary test container seed s t omega data

/-- The planted-source success probability is bounded by unprogrammed win-or-Bad for the same exact samplers. -/
theorem transfer (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool) :
    (original coordinates password crypto phrase target adversary test) true ≤
      (raw coordinates password crypto phrase adversary test) true := by
  rw [resampling,← MomentTools.bool (programmed coordinates password crypto phrase target adversary test),
    ← MomentTools.bool (raw coordinates password crypto phrase adversary test)]
  unfold programmed raw W3.programmed W3.payload W3.tagProgrammed W3.omegaProgrammed
  simp only [MomentTools.bind,moment_map,Function.comp_def,PMF.bind_map ]
  apply mono
  intro s
  apply mono
  intro container
  apply mono
  intro seed
  apply mono
  intro t
  apply mono
  intro data
  apply mono
  intro omega
  exact pointwise coordinates password crypto phrase target adversary test container seed s t omega data

end FullPlantedTransfer

/-! The transferred win-or-Bad is exactly the event used by the checked Theta2 seed and pair bounds. -/
namespace FullPlantedEvents
open Gamma2Model FullPlantedResampling FullPlantedTransfer
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
attribute [local irreducible] finalize FinalCut.prepare

/-- The S target is the entropy of the actual inverse state in Theta2. -/
theorem seed_score (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy)
    (phrase : Passphrase)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (output : Result → Seed)
    (container : Entropy) (seed : Seed) (s : W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))
    (t : W3.TTable (Seed := Seed) (Check := Check) (Tail := Tail)) (omega : Seed → Data) (data : Data) :
    rawScore coordinates password crypto phrase adversary (fun target result => decide (output result=target)) container seed s t omega data=
      Theta2SeedBound.winOrBad coordinates.symm output ⟨s,t,omega⟩ (adversary data)
        (((password,phrase),(coordinates container,crypto)),seed) := by
  apply Bool.eq_iff_iff.mpr
  unfold rawScore WalletQueryEvent.winOrBad Theta2SeedBound.winOrBad
  simp only [decide_eq_true_eq]
  rw [FullSourceCoordinates.inverse]
  simp only [SeedQueryRun.bad,decide_eq_true_eq]
  simp only [SeedQueryRun.pairs,SeedQueryRun.full]

/-- Pair output uses the same inverse S target and the same independent blind seed target. -/
theorem pair_score (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy)
    (phrase : Passphrase)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (output : Result → Fin N × Passphrase)
    (container : Entropy) (seed : Seed) (s : W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))
    (t : W3.TTable (Seed := Seed) (Check := Check) (Tail := Tail)) (omega : Seed → Data) (data : Data) :
    rawScore coordinates password crypto phrase adversary (fun _ result => decide (output result=(password,phrase))) container seed s t omega data=
      Theta2PairBound.winOrBad coordinates.symm output ⟨s,t,omega⟩ (adversary data)
        (((password,phrase),(coordinates container,crypto)),seed) := by
  apply Bool.eq_iff_iff.mpr
  unfold rawScore WalletQueryEvent.winOrBad Theta2PairBound.winOrBad
  simp only [decide_eq_true_eq]
  rw [FullSourceCoordinates.inverse]
  simp only [SeedQueryRun.bad,decide_eq_true_eq]
  simp only [SeedQueryRun.pairs,SeedQueryRun.full]

end FullPlantedEvents

/-! The public container has exactly the same uniform law in entropy and Feistel-state coordinates. -/
namespace FullSourceUniform
open Gamma2Model GameExpectation
attribute [local instance] FiniteBits.fintype
variable {Entropy : Type} [Fintype Entropy] [Nonempty Entropy]

theorem law (coordinates : Entropy ≃ State) :
    (PMF.uniformOfFintype Entropy).map coordinates=PMF.uniformOfFintype State :=
  PMF.uniformOfFintype_map_of_bijective coordinates coordinates.bijective

/-- Applying coordinates changes the representation, not any success probability. -/
theorem expectation (coordinates : Entropy ≃ State) (value : State → ENNReal) :
    moment (PMF.uniformOfFintype Entropy) (fun entropy => value (coordinates entropy))=
      moment (PMF.uniformOfFintype State) value := by
  have transported := congrArg (fun distribution : PMF State => moment distribution value) (law coordinates)
  try dsimp only at transported
  rw [moment_map] at transported
  exact transported

end FullSourceUniform

/-! Transport point masses through a bijection without enumerating its domain. -/
namespace PMFTransport

theorem equiv_apply {First Second : Type} (law : PMF First) (equiv : First ≃ Second)
    (value : Second) : (law.map equiv) value=law (equiv.symm value) :=
  ProbabilityTools.equiv_apply law equiv value

end PMFTransport

/-! One exact reordering of all independent samplers used in the final Theta2 integration. -/
namespace IndependentReorder
open ProbabilityTools GameExpectation
variable {P Q C S Y R T D O : Type}
abbrev Raw := P × Q × C × S × Y × R × T × D × O
abbrev Normal := (S × T × D × O) × ((P × Q) × (Y × (C × R)))

def reorder : Normal (P := P) (Q := Q) (C := C) (S := S) (Y := Y) (R := R) (T := T) (D := D) (O := O) ≃
    Raw (P := P) (Q := Q) (C := C) (S := S) (Y := Y) (R := R) (T := T) (D := D) (O := O) where
  toFun := fun ⟨⟨s,t,d,o⟩,⟨⟨p,q⟩,⟨y,⟨c,r⟩⟩⟩⟩ => (p,q,c,s,y,r,t,d,o)
  invFun := fun ⟨p,q,c,s,y,r,t,d,o⟩ => ((s,t,d,o),((p,q),(y,(c,r))))
  left_inv := by rintro ⟨⟨s,t,d,o⟩,⟨⟨p,q⟩,⟨y,⟨c,r⟩⟩⟩⟩; rfl
  right_inv := by rintro ⟨p,q,c,s,y,r,t,d,o⟩; rfl

variable (p : PMF P) (q : PMF Q) (c : PMF C) (s : PMF S) (y : PMF Y) (r : PMF R) (t : PMF T)
  (d : PMF D) (o : PMF O)

def raw :=
  independentPair p (independentPair q (independentPair c (independentPair s
    (independentPair y (independentPair r (independentPair t (independentPair d o)))))))

def normal :=
  independentPair (independentPair s (independentPair t (independentPair d o)))
    (independentPair (independentPair p q) (independentPair y (independentPair c r)))

/-- No independence is postulated after the fact: both laws explicitly sample the same independent factors. -/
theorem distribution : (normal p q c s y r t d o).map reorder=raw p q c s y r t d o := by
  ext value
  rw [PMFTransport.equiv_apply]
  rcases value with ⟨pValue,qValue,cValue,sValue,yValue,rValue,tValue,dValue,oValue⟩
  simp only [normal,raw,ProbabilityTools.independentPair_apply,reorder,Equiv.coe_fn_symm_mk]
  ac_rfl

/-- Nonnegative success indicators may be integrated in the order used by the checked Theta2 bounds. -/
theorem moments (p : PMF P) (q : PMF Q) (c : PMF C) (s : PMF S) (y : PMF Y) (r : PMF R)
    (t : PMF T) (d : PMF D) (o : PMF O)
    (score : Raw (P := P) (Q := Q) (C := C) (S := S) (Y := Y) (R := R) (T := T) (D := D) (O := O) → ENNReal) :
    moment (raw p q c s y r t d o) score=moment (normal p q c s y r t d o) (score ∘ reorder) := by
  rw [← distribution,moment_map]

end IndependentReorder

/-! Reorder the actual raw experiment into fixed wallet context and the checked Theta2 sampling law. -/
namespace FullRawInputs
open Gamma2Model GameExpectation MomentTools ProbabilityTools
open FullPlantedResampling FullPlantedTransfer
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
attribute [local instance] FiniteBits.fintype
abbrev RawInput := IndependentReorder.Raw (P := Fin N) (Q := Passphrase) (C := Tables (Fin N) Entropy)
  (S := Entropy × Passphrase → Seed) (Y := Entropy) (R := Seed) (T := Seed → Check × Tail) (D := Data) (O := Seed → Data)

def score (coordinates : Entropy ≃ State)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool)
    (input : RawInput (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) : Bool :=
  let ⟨password,phrase,crypto,s,container,seed,t,data,omega⟩ := input
  rawScore coordinates password crypto phrase adversary (test password phrase) container seed s t omega data

def stateScore (coordinates : Entropy ≃ State)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool)
    (sample : SeedQueryRun.World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) : Bool :=
  rawScore coordinates sample.1.1.1 sample.1.2.2 sample.1.1.2 adversary (test sample.1.1.1 sample.1.1.2)
    (coordinates.symm sample.1.2.1) sample.2 wallet.s wallet.t wallet.omega data

variable [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]

def inputLaw (passwords : PMF (Fin N)) (phrases : PMF Passphrase) :=
  IndependentReorder.raw passwords phrases (sampleTables (Password := Fin N) (Entropy := Entropy))
    (PMF.uniformOfFintype (Entropy × Passphrase → Seed)) (PMF.uniformOfFintype Entropy) (PMF.uniformOfFintype Seed)
    (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype Data) (PMF.uniformOfFintype (Seed → Data))

def normalLaw (passwords : PMF (Fin N)) (phrases : PMF Passphrase) :=
  IndependentReorder.normal passwords phrases (sampleTables (Password := Fin N) (Entropy := Entropy))
    (PMF.uniformOfFintype (Entropy × Passphrase → Seed)) (PMF.uniformOfFintype Entropy) (PMF.uniformOfFintype Seed)
    (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype Data) (PMF.uniformOfFintype (Seed → Data))

def rawGame (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool) : PMF Bool :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    raw coordinates password crypto phrase adversary (test password phrase)

/-- All hidden values and all independently sampled function tables are present in one retained input. -/
theorem input_map (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool) :
    rawGame coordinates passwords phrases adversary test=(inputLaw passwords phrases).map (score coordinates adversary test) := by
  simp only [rawGame,inputLaw,raw,IndependentReorder.raw,independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def,score]

/-- This exchanges only independent factors; it does not condition the run on the secret pair or a success event. -/
theorem reordered (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool) :
    (rawGame coordinates passwords phrases adversary test) true=
      moment (normalLaw passwords phrases)
        (fun input => if score coordinates adversary test (IndependentReorder.reorder input) then 1 else 0) := by
  rw [input_map,probability]
  exact IndependentReorder.moments passwords phrases sampleTables
    (PMF.uniformOfFintype (Entropy × Passphrase → Seed)) (PMF.uniformOfFintype Entropy) (PMF.uniformOfFintype Seed)
    (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype Data) (PMF.uniformOfFintype (Seed → Data))
    (fun input => if score coordinates adversary test input then 1 else 0)

omit [Fintype Passphrase] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
/-- For each fixed wallet-table tuple and public reference, the remaining law is exactly Theta2. -/
theorem fixed_wallet (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool) :
    moment (independentPair (independentPair passwords phrases)
      (independentPair (PMF.uniformOfFintype Entropy) (independentPair sampleTables (PMF.uniformOfFintype Seed))))
      (fun input => if score coordinates adversary test
        (IndependentReorder.reorder ((wallet.s,wallet.t,data,wallet.omega),input)) then 1 else 0) =
    moment (independentPair (SeedQueryBounds.worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if stateScore coordinates wallet data adversary test sample then 1 else 0) := by
  simp only [SeedQueryBounds.worlds,SeedQueryBounds.views,independentPair,
    MomentTools.bind,moment_map,Function.comp_def,score,IndependentReorder.reorder,stateScore]
  apply congrArg (moment passwords)
  funext password
  apply congrArg (moment phrases)
  funext phrase
  have transport := FullSourceUniform.expectation coordinates
    (fun container => moment (sampleTables (Password := Fin N) (Entropy := Entropy)) (fun crypto =>
      moment (PMF.uniformOfFintype Seed) (fun seed =>
        if rawScore coordinates password crypto phrase adversary (test password phrase)
          (coordinates.symm container) seed wallet.s wallet.t wallet.omega data then 1 else 0)))
  (try simp only [Equiv.symm_apply_apply] at transport ⊢)
  exact transport

end FullRawInputs

/-! Both final event instantiations of the common source-game sampler. -/
namespace FullRawEvents
open Gamma2Model FullPlantedResampling
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

theorem seed_event (coordinates : Entropy ≃ State)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (output : Result → Seed)
    (sample : SeedQueryRun.World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) :
    FullRawInputs.stateScore coordinates wallet data adversary
      (fun _ _ target result => decide (output result=target)) sample=
      Theta2SeedBound.winOrBad coordinates.symm output wallet (adversary data) sample := by
  rcases sample with ⟨⟨⟨password,phrase⟩,⟨container,crypto⟩⟩,seed⟩
  simpa only [FullRawInputs.stateScore,Equiv.apply_symm_apply] using
    FullPlantedEvents.seed_score coordinates password crypto phrase adversary output
      (coordinates.symm container) seed wallet.s wallet.t wallet.omega data

theorem pair_event (coordinates : Entropy ≃ State)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (output : Result → Fin N × Passphrase)
    (sample : SeedQueryRun.World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) :
    FullRawInputs.stateScore coordinates wallet data adversary
      (fun password phrase _ result => decide (output result=(password,phrase))) sample=
      Theta2PairBound.winOrBad coordinates.symm output wallet (adversary data) sample := by
  rcases sample with ⟨⟨⟨password,phrase⟩,⟨container,crypto⟩⟩,seed⟩
  simpa only [FullRawInputs.stateScore,Equiv.apply_symm_apply] using
    FullPlantedEvents.pair_score coordinates password crypto phrase adversary output
      (coordinates.symm container) seed wallet.s wallet.t wallet.omega data

end FullRawEvents

/-! Global raw-game numerical bounds after exact reordering, with one shared set of actual hard budgets. -/
namespace FullRawBound
open Gamma2Model GameExpectation MomentTools ProbabilityTools
open FullPlantedResampling SeedQueryRun QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

abbrev FullProgram := FullPlantedResampling.Program (Password := Fin N) (Entropy := Entropy)
  (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)
abbrev WalletTables := SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data

/-- Bounds hold for every table and public input, count repeated calls, and never charge owner-generation calls. -/
structure Budgets (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
    (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (kA kS qB qH qT qOmega : Nat) : Prop where
  a : ∀ (wallet : WalletTables) data container crypto,
    (execute crypto (compiled wallet (adversary data) container)).2.countP isA ≤ kA
  b : ∀ (wallet : WalletTables) data container crypto,
    (execute crypto (compiled wallet (adversary data) container)).2.countP isB ≤ qB
  h : ∀ (wallet : WalletTables) data container crypto,
    (execute crypto (compiled wallet (adversary data) container)).2.countP isH ≤ qH
  s : ∀ (wallet : WalletTables) data input,(pairs wallet (adversary data) input).length ≤ kS
  t : ∀ (wallet : WalletTables) data input,(full wallet (adversary data) input).2.countP SeedWalletModel.isT ≤ qT
  omega : ∀ (wallet : WalletTables) data input,(full wallet (adversary data) input).2.countP SeedWalletModel.isOmega ≤ qOmega

variable [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- The actual source sampler supplies the independence needed by each fixed-wallet Theta2 theorem. -/
theorem shared (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool) (upper : ENNReal)
    (fixed : ∀ (wallet : WalletTables) data,
      moment (independentPair (SeedQueryBounds.worlds passwords phrases) (PMF.uniformOfFintype Seed))
        (fun sample => if FullRawInputs.stateScore coordinates wallet data adversary test sample then 1 else 0) ≤ upper) :
    (FullRawInputs.rawGame coordinates passwords phrases adversary test) true ≤ upper := by
  rw [FullRawInputs.reordered]
  unfold FullRawInputs.normalLaw IndependentReorder.normal
  rw [independentPair,MomentTools.bind]
  apply bounded
  rintro ⟨s,t,data,omega⟩
  rw [moment_map]
  change moment (independentPair (independentPair passwords phrases)
    (independentPair (PMF.uniformOfFintype Entropy) (independentPair sampleTables (PMF.uniformOfFintype Seed))))
    (fun input => if FullRawInputs.score coordinates adversary test
      (IndependentReorder.reorder ((s,t,data,omega),input)) then 1 else 0) ≤ upper
  rw [FullRawInputs.fixed_wallet coordinates passwords phrases ⟨s,t,omega⟩ data adversary test]
  exact fixed ⟨s,t,omega⟩ data

variable [Inhabited (Fin N)]

/-- Exact seed-game raw bound; delta_gen and creation refusal are added by the source-game couplings. -/
theorem seed_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullRawInputs.rawGame coordinates passwords phrases adversary
      (fun _ _ target result => decide (output result=target))) true ≤
      W1.top2 passwords phrases (kA/12) kS+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+
      (qT+qOmega)/(2^512:ENNReal)+(2^512:ENNReal)⁻¹ := by
  apply shared coordinates passwords phrases adversary _ _
  intro wallet data
  simp_rw [FullRawEvents.seed_event]
  exact Theta2SeedBound.bound coordinates.symm coordinates.symm.injective
    (FullSourceCoordinates.firstHalf coordinates) (FullSourceCoordinates.projects coordinates)
    passwords phrases sorted output wallet (adversary data) p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth
    (budget.a wallet data) (budget.b wallet data) (budget.h wallet data) (budget.s wallet data)
    (budget.t wallet data) (budget.omega wallet data)

/-- Exact pair-game raw bound, including both expressions inside the source theorem's minimum. -/
theorem pair_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Fin N × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullRawInputs.rawGame coordinates passwords phrases adversary
      (fun password phrase _ result => decide (output result=(password,phrase)))) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+(qT+qOmega)/(2^512:ENNReal) := by
  apply shared coordinates passwords phrases adversary _ _
  intro wallet data
  simp_rw [FullRawEvents.pair_event]
  exact Theta2PairBound.bound coordinates.symm coordinates.symm.injective
    (FullSourceCoordinates.firstHalf coordinates) (FullSourceCoordinates.projects coordinates)
    passwords phrases sorted output wallet (adversary data) p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth
    (budget.a wallet data) (budget.b wallet data) (budget.h wallet data) (budget.s wallet data)
    (budget.t wallet data) (budget.omega wallet data)

end FullRawBound

/-! Exact score-law bridge between the generation compiler and the W3 planted experiment. -/
namespace FullGenerationResampling
open Gamma2Model WalletCryptoCompiler
open FullPlantedResampling
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]

def planted (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool) : PMF Bool :=
  (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
    (WalletCapped.planted phrase target (FullGenerationCoupling.program crypto omega
      (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates password crypto entropy)) adversary)).map
      (fun view => test view.1.seed view.2.1.1)

/-- Omega can be sampled outside generation because the generation loop never reads it. -/
theorem planted_equal (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool) :
    planted coordinates password crypto phrase target adversary test=
      original coordinates password crypto phrase target adversary test := by
  unfold planted WalletCapped.planted original W3Source.original
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext chosen
  simp only [PMF.map,Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext table
  congr 1
  funext omega
  exact congrArg PMF.pure (planted_score coordinates password crypto phrase target omega adversary test chosen table)

variable [DecidableEq Check]

def actual (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool) : PMF Bool :=
  (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
    (WalletUnbounded.real phrase target (FullGenerationCoupling.program crypto omega
      (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates password crypto entropy)) adversary)).map
      (fun view => test view.1.seed view.2.1.1)

/-- This transfer uses actual rejection generation and public wallet data, not an assumed planted source. -/
theorem bound (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Seed → Result → Bool)
    (kS qT : Nat) (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16)
    (sBudget : ∀ (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) data container,
      (SeedWalletModel.seedPairs (TranscriptErasure.execute
        (combinedAnswer (SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data) crypto
          (SeedWalletModel.answer wallet)) (adversary data container)).2).length ≤ kS)
    (tBudget : ∀ (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) data container,
      (TranscriptErasure.execute
        (combinedAnswer (SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data) crypto
          (SeedWalletModel.answer wallet)) (adversary data container)).2.countP SeedWalletModel.isT ≤ qT) :
    StatisticalClose.Close (actual coordinates password crypto phrase target adversary test)
      (original coordinates password crypto phrase target adversary test) (W2.delta kS qT) := by
  rw [← planted_equal]
  have averaged := CloseComposition.bind (PMF.uniformOfFintype (Seed → Data)) _ _
    (fun _ => W2.delta kS qT) (fun omega => CloseComposition.map _ _ _
      (FullGenerationCoupling.bound crypto omega
        (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates password crypto entropy)) adversary
        phrase target kS qT entropyWidth seedWidth checkWidth
        (fun chosen table => sBudget (WalletGenerationCompiler.wallet table omega) (omega chosen.seed) _)
        (fun chosen table => tBudget (WalletGenerationCompiler.wallet table omega) (omega chosen.seed) _))
      (fun view => test view.1.seed view.2.1.1))
  simpa only [actual,planted,MomentTools.constant] using averaged

end FullGenerationResampling

/-! Connect the actual rejection-generated source game to the globally bounded unprogrammed game. -/
namespace FullSourceTransfer
open Gamma2Model GameExpectation MomentTools
open FullPlantedResampling FullRawBound

/-- Averaging retains a constant error without conditioning on any successful generation event. -/
theorem bind_probability {Context : Type} (prior : PMF Context) (first second : Context → PMF Bool)
    (error : ENNReal) (each : ∀ context,(first context) true ≤ (second context) true+error) :
    (prior.bind first) true ≤ (prior.bind second) true+error := by
  change moment prior (fun context => (first context) true) ≤
    moment prior (fun context => (second context) true)+error
  rw [← constant prior error,← MomentTools.add]
  exact mono prior _ _ each

variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- The attacker sees only the actual container and Omega(seed*); the score alone reads the two secrets and seed. -/
def original (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool) : PMF Bool :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    FullGenerationResampling.actual coordinates password crypto phrase target adversary (test password phrase)

/-- Actual generation, exact resampling, and programming removal are composed in the direction used by Theorem 5. -/
theorem transfer (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (original coordinates passwords phrases target adversary test) true ≤
      (FullRawInputs.rawGame coordinates passwords phrases adversary test) true+W2.delta kS qT := by
  unfold original FullRawInputs.rawGame
  apply bind_probability
  intro password
  apply bind_probability
  intro phrase
  apply bind_probability
  intro crypto
  have close := FullGenerationResampling.bound coordinates password crypto phrase target adversary (test password phrase)
    kS qT entropyWidth seedWidth checkWidth
    (fun wallet data container => budget.s wallet data (container,crypto))
    (fun wallet data container => budget.t wallet data (container,crypto))
  have first := (close id).1
  simp only [PMF.map_id] at first
  exact first.trans (add_le_add
    (FullPlantedTransfer.transfer coordinates password crypto phrase target adversary (test password phrase)) le_rfl)

end FullSourceTransfer

/-! Theorem 5 for the actual first-success source game, before the separately bounded creation-refusal step. -/
namespace Theorem5Base
open Gamma2Model FullRawBound FullSourceTransfer
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

/-- All explicit source-game errors other than the optional first creation refusal. -/
def error (p1 s1 : ENNReal) (kA kS qB qH qT qOmega : Nat) : ENNReal :=
  (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+
    (qT+qOmega)/(2^512:ENNReal)+W2.delta kS qT

/-- Actual rejection-generated source, actual cipher and full adaptive program: seed success has the advertised pair-search main term. -/
theorem seed_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (original coordinates passwords phrases target adversary
      (fun _ _ seed result => decide (output result=seed))) true ≤
      W1.top2 passwords phrases (kA/12) kS+error p1 s1 kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  have transfer := FullSourceTransfer.transfer coordinates passwords phrases target adversary
    (fun _ _ seed result => decide (output result=seed)) kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  have raw := FullRawBound.seed_bound coordinates passwords phrases sorted output adversary p1 s1 largestP largestQ
    kA kS qB qH qT qOmega seedWidth budget
  apply transfer.trans
  apply (add_le_add raw (le_refl (W2.delta kS qT))).trans
  exact le_of_eq (by unfold error; abel)

/-- The exact-pair game keeps both independently proved expressions inside the minimum, plus the same source error. -/
theorem pair_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Fin N × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (original coordinates passwords phrases target adversary
      (fun password phrase _ result => decide (output result=(password,phrase)))) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+error p1 s1 kA kS qB qH qT qOmega := by
  have transfer := FullSourceTransfer.transfer coordinates passwords phrases target adversary
    (fun password phrase _ result => decide (output result=(password,phrase)))
    kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  have raw := FullRawBound.pair_bound coordinates passwords phrases sorted output adversary p1 s1 largestP largestQ
    kA kS qB qH qT qOmega seedWidth budget
  apply transfer.trans
  apply (add_le_add raw (le_refl (W2.delta kS qT))).trans
  exact le_of_eq (by unfold error; abel)

end Theorem5Base

/-! Shared closed distribution terms avoid reducing enormous finite function enumerations. -/
namespace CryptoUniform
attribute [local instance] FiniteBits.fintype
noncomputable def h : PMF TableFactors.HTable := PMF.uniformOfFintype _
theorem h_eq : h = PMF.uniformOfFintype TableFactors.HTable := rfl
end CryptoUniform

/-! Restriction along an injection, including the independent complement of the full function. -/
namespace UniformInjection
variable {Domain Whole Answer : Type} [Fintype Domain] [Fintype Whole] [Fintype Answer] [Nonempty Answer]
  [DecidableEq Whole] [DecidableEq Domain]

def split (embedding : Domain → Whole) (injective : Function.Injective embedding) :
    (Whole → Answer) ≃ ((Domain → Answer) × ({point // point ∉ Set.range embedding} → Answer)) := by
  classical
  let domain : Domain ⊕ {point // point ∉ Set.range embedding} ≃ Whole :=
    (Equiv.sumCongr (Equiv.ofInjective embedding injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range embedding))
  exact (Equiv.arrowCongr domain.symm (Equiv.refl Answer)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- A uniform function restricted along an injection is itself fully uniform. -/
theorem restriction (embedding : Domain → Whole) (injective : Function.Injective embedding) :
    (PMF.uniformOfFintype (Whole → Answer)).map (fun table => fun point => table (embedding point)) =
      PMF.uniformOfFintype (Domain → Answer) := by
  classical
  let transport := split (Answer := Answer) embedding injective
  have moved := PMF.uniformOfFintype_map_of_bijective transport transport.bijective
  calc
    _ = ((PMF.uniformOfFintype (Whole → Answer)).map transport).map Prod.fst :=
      (PMF.map_comp transport _ Prod.fst).symm
    _ = _ := by rw [moved,ProbabilityTools.uniform_fst]

end UniformInjection

/-! Round-index and right-half separation make the actual composed H masks independent uniform functions. -/
namespace RoundFunctionLaw
open Gamma2Model Lemma1 ProbabilityTools
set_option maxRecDepth 2048
attribute [local instance] FiniteBits.fintype
abbrev Mask := Half → Half
abbrev Rounds := Fin 12 → Mask

def curry : (Fin 12 × Half → Half) ≃ Rounds where
  toFun table round right := table (round,right)
  invFun table point := table point.1 point.2
  left_inv := by intro table; rfl
  right_inv := by intro table; rfl

def input (keyAt : Fin 12 → Half → Key) (point : Fin 12 × Half) : Key × Fin 12 × Half :=
  (keyAt point.1 point.2,point.1,point.2)

/-- Even with colliding keys or salts, round and right half retain every round-function input. -/
theorem input_injective (keyAt : Fin 12 → Half → Key) : Function.Injective (input keyAt) := by
  intro first second equal
  exact congrArg Prod.snd equal

theorem masks_uniform (keyAt : Fin 12 → Half → Key) :
    (PMF.uniformOfFintype (Key × Fin 12 × Half → Half)).map
      (fun h round right => h (keyAt round right,round,right)) = PMF.uniformOfFintype Rounds := by
  calc
    _ = ((PMF.uniformOfFintype (Key × Fin 12 × Half → Half)).map
        (fun table point => table (input keyAt point))).map curry := (PMF.map_comp _ _ _).symm
    _ = (PMF.uniformOfFintype (Fin 12 × Half → Half)).map curry := by
      rw [UniformInjection.restriction _ (input_injective keyAt)]
    _ = _ := PMF.uniformOfFintype_map_of_bijective curry curry.bijective

/-- The independent round vector has a uniform output after its first two rounds. -/
theorem network_uniform (source : State) :
    (PMF.uniformOfFintype Rounds).map (fun masks => encrypt (List.ofFn masks) source) =
      PMF.uniformOfFintype State :=
  Lemma3.rounds_uniform 10 source

/-- Fixed P,A,B and X: the real MHFE ciphertext is uniform over the choice of H. -/
theorem cipher_uniform {Password : Type} (password : Password) (a : TableFactors.ATable Password)
    (b : TableFactors.BTable) (source : State) :
    (CryptoUniform.h).map
      (fun h => KnownPairModel.cipher password a b h source) = PMF.uniformOfFintype State := by
  have law := masks_uniform (fun round right => a (password,b (round,right)))
  calc
    _ = ((CryptoUniform.h).map
        (fun h round right => h (a (password,b (round,right)),round,right))).map
        (fun masks => encrypt (List.ofFn masks) source) := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [CryptoUniform.h_eq,law,network_uniform]

end RoundFunctionLaw

/-! Exact creation refusal probability, stated directly as the ciphertext point mass. -/
namespace G9
open Gamma2Model TableFactors GameExpectation MomentTools
attribute [local instance] FiniteBits.fintype

/-- No enumeration of the concrete state space is needed for its cardinality. -/
theorem state_mass : (Fintype.card State : ENNReal)⁻¹ = (2^256 : ENNReal)⁻¹ := by
  have halfCard : Fintype.card Half = 2^128 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Lemma3.bitEquivFin 128)
  have card : Fintype.card State = 2^256 := by
    rw [Fintype.card_prod Half Half,halfCard,← Nat.pow_add]
  rw [card,Nat.cast_pow,Nat.cast_ofNat]

/-- X,P,A,B fixed: Pr_H[Perm_P(X)=X] is exactly 2^-256 for the actual cipher. -/
theorem fixed {Password : Type} (password : Password) (a : ATable Password) (b : BTable)
    (source : State) :
    ((CryptoUniform.h).map (fun h => KnownPairModel.cipher password a b h source)) source =
      (2^256 : ENNReal)⁻¹ := by
  rw [RoundFunctionLaw.cipher_uniform,PMF.uniformOfFintype_apply]
  exact state_mass

/-- The source, password, A,B and arbitrary context may be dependent; only H is sampled independently. -/
theorem joint {Password Context : Type}
    (worlds : PMF (Password × ATable Password × BTable × State × Context)) :
    moment worlds (fun world =>
      ((CryptoUniform.h).map (fun h =>
        KnownPairModel.cipher world.1 world.2.1 world.2.2.1 h world.2.2.2.1)) world.2.2.2.1) =
      (2^256 : ENNReal)⁻¹ := by
  simp_rw [fixed]
  exact constant _ _

end G9

/-! A singleton equality event uses one point mass, without constructing a finite enumeration. -/
namespace PointMassEvent

/-- This identity needs no Fintype instance on the target domain. -/
theorem equality {Value : Type} [DecidableEq Value] (distribution : PMF Value) (target : Value) :
    (distribution.map (fun candidate => decide (candidate=target))) true = distribution target := by
  simp [PMF.map_apply,eq_comm]

end PointMassEvent

/-! G9's exact point mass expressed as the actual creation-refusal predicate. -/
namespace G9Event
open Gamma2Model TableFactors
attribute [local irreducible] KnownPairModel.cipher

/-- No finite state-space enumeration is introduced by the singleton-event bridge. -/
def fixed {Password : Type} (password : Password) (a : ATable Password) (b : BTable) (source : State) :=
  (PointMassEvent.equality
    ((CryptoUniform.h).map (fun h => KnownPairModel.cipher password a b h source)) source).trans
      (G9.fixed password a b source)

end G9Event

/-! Average an exact conditional refusal law without re-elaborating a concrete state-space enumeration. -/
namespace ExactRefusalLift
open GameExpectation MomentTools
variable {Context Input Value : Type} [DecidableEq Value]

def initial (contexts : PMF Context) (inputs : PMF Input) :=
  contexts.bind fun context => inputs.map fun input => (context,input)

def refused (function : Context → Input → Value) (target : Context → Value) (pair : Context × Input) :
    Bool :=
  decide (function pair.1 pair.2=target pair.1)

theorem conditional (inputs : PMF Input) (function : Context → Input → Value)
    (target : Context → Value) (context : Context) :
    ((inputs.map (fun input => (context,input))).map (refused function target)) true=
      (inputs.map (function context)) (target context) := by
  have bridge := PointMassEvent.equality (inputs.map (function context)) (target context)
  rw [PMF.map_comp] at bridge ⊢
  exact bridge

/-- Only the independent input law is averaged; no conditioning on successful creation is assumed. -/
theorem probability (contexts : PMF Context) (inputs : PMF Input)
    (function : Context → Input → Value) (target : Context → Value) (rate : ENNReal)
    (each : ∀ context,(inputs.map (function context)) (target context)=rate) :
    ((initial contexts inputs).map (refused function target)) true=rate := by
  rw [initial,PMF.map_bind,PMF.bind_apply]
  change moment contexts _=rate
  simp_rw [conditional,each]
  exact constant _ _

/-- Retry behavior may retain all environment data or report failure; only the first refusal costs probability. -/
theorem success_bound (contexts : PMF Context) (inputs : PMF Input)
    (function : Context → Input → Value) (target : Context → Value) (rate : ENNReal)
    (each : ∀ context,(inputs.map (function context)) (target context)=rate)
    (test : Context × Input → Bool) (later : Context × Input → PMF (Context × Input))
    (upper : ENNReal) (original : ((initial contexts inputs).map test) true ≤ upper) :
    ((RefusalCoupling.replace (initial contexts inputs) (refused function target) later).map test) true ≤
      upper+rate := by
  have estimate := RefusalCoupling.success_bound (initial contexts inputs) (refused function target) test later upper original
  rw [probability contexts inputs function target rate each] at estimate
  exact estimate

end ExactRefusalLift

/-! Exact refusal on complete environments. A checked opaque witness prevents reduction of the enormous H-table enumeration. -/
namespace G9Game
open Gamma2Model TableFactors GameExpectation MomentTools
variable {Context Password : Type} [stateEq : DecidableEq State]
attribute [local irreducible] KnownPairModel.cipher

private opaque hWitness : {law : PMF HTable // law=CryptoUniform.h} :=
  ⟨CryptoUniform.h,rfl⟩

omit stateEq in
private theorem fixed (password : Password) (a : ATable Password) (b : BTable) (source : State) :
    (hWitness.val.map (fun h => KnownPairModel.cipher password a b h source)) source=
      (2^256:ENNReal)⁻¹ := by
  have same := congrArg (fun law : PMF HTable =>
    (law.map (fun h => KnownPairModel.cipher password a b h source)) source) hWitness.property
  exact same.trans (G9.fixed password a b source)

/-- Exact complete-environment refusal probability, with the source sampler retained in the conclusion. -/
theorem probability (contexts : PMF Context) (password : Context → Password)
    (a : Context → ATable Password) (b : Context → BTable) (source : Context → State) :
    ((ExactRefusalLift.initial contexts CryptoUniform.h).map
      (ExactRefusalLift.refused (fun context h =>
        KnownPairModel.cipher (password context) (a context) (b context) h (source context)) source)) true=
      (2^256:ENNReal)⁻¹ := by
  let Claim := fun law : PMF HTable =>
    ((ExactRefusalLift.initial contexts law).map
      (ExactRefusalLift.refused (fun context h =>
        KnownPairModel.cipher (password context) (a context) (b context) h (source context)) source)) true=
      (2^256:ENNReal)⁻¹
  have opaqueResult : Claim hWitness.val :=
    ExactRefusalLift.probability contexts hWitness.val _ _ _
      (fun context => fixed (password context) (a context) (b context) (source context))
  exact Eq.mp (congrArg Claim hWitness.property) opaqueResult

/-- The whole success-bound implication is transported, so neither its hypothesis nor conclusion uses a substitute sampler. -/
theorem success_bound (contexts : PMF Context) (password : Context → Password)
    (a : Context → ATable Password) (b : Context → BTable) (source : Context → State)
    (test : Context × HTable → Bool) (later : Context × HTable → PMF (Context × HTable))
    (upper : ENNReal)
    (original : ((ExactRefusalLift.initial contexts CryptoUniform.h).map test) true ≤ upper) :
    ((RefusalCoupling.replace (ExactRefusalLift.initial contexts CryptoUniform.h)
      (ExactRefusalLift.refused (fun context h =>
        KnownPairModel.cipher (password context) (a context) (b context) h (source context)) source) later).map test) true ≤
      upper+(2^256:ENNReal)⁻¹ := by
  let Claim := fun law : PMF HTable =>
    ((ExactRefusalLift.initial contexts law).map test) true ≤ upper →
    ((RefusalCoupling.replace (ExactRefusalLift.initial contexts law)
      (ExactRefusalLift.refused (fun context h =>
        KnownPairModel.cipher (password context) (a context) (b context) h (source context)) source) later).map test) true ≤
      upper+(2^256:ENNReal)⁻¹
  have opaqueResult : Claim hWitness.val :=
    ExactRefusalLift.success_bound contexts hWitness.val _ _ _
      (fun context => fixed (password context) (a context) (b context) (source context)) test later upper
  have sourceResult : Claim CryptoUniform.h := Eq.mp (congrArg Claim hWitness.property) opaqueResult
  exact sourceResult original

end G9Game

/-! Retain the complete first-attempt environment and sample H last, after actual profile-source generation. -/
namespace FullSourceEnvironment
open Gamma2Model TableFactors FullRawBound FullPlantedResampling
open GameExpectation MomentTools
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}

abbrev GenerationTable := TranscriptErasure.Table
  (WalletGeneration.spec Entropy Passphrase Seed Check Tail)
abbrev Other := ATable (Fin N) × BTable × GTable Entropy

/-- Generation may correlate E with S/T/Q, but none of its inputs reads H. -/
structure Context (N : Nat) (Entropy Passphrase Seed Check Tail Data : Type) where
  password : Fin N
  phrase : Passphrase
  other : Other (N := N) (Entropy := Entropy)
  omega : Seed → Data
  table : GenerationTable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)
  chosen : WalletGeneration.Selected Entropy Seed Tail

def crypto (context : Context N Entropy Passphrase Seed Check Tail Data) (h : HTable) :
    Tables (Fin N) Entropy :=
  ⟨context.other.1,context.other.2.1,h,context.other.2.2⟩

def score (coordinates : Entropy ≃ State)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool)
    (sample : Context N Entropy Passphrase Seed Check Tail Data × HTable) : Bool :=
  let context := sample.1
  let tables := crypto context sample.2
  test context.password context.phrase context.chosen.seed
    (TranscriptErasure.execute context.table
      (FullGenerationCoupling.program tables context.omega
        (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates context.password tables entropy)) adversary
          context.chosen)).1.1

variable [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] FullGenerationCoupling.program TranscriptErasure.execute
  FullSourceCoordinates.cipher

def contexts (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check) :
    PMF (Context N Entropy Passphrase Seed Check Tail Data) :=
  passwords.bind fun password => phrases.bind fun phrase =>
    (PMF.uniformOfFintype (Other (N := N) (Entropy := Entropy))).bind fun other =>
      (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
        (PMF.uniformOfFintype (GenerationTable (Entropy := Entropy) (Passphrase := Passphrase)
          (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
          (WalletCompletion.real table phrase target).map fun chosen =>
            ⟨password,phrase,other,omega,table,chosen⟩

/-- This is an exact sampler reordering; it does not assert E is independent of its generation functions. -/
theorem original (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Seed → Result → Bool) :
    FullSourceTransfer.original coordinates passwords phrases target adversary test=
      (ExactRefusalLift.initial (contexts passwords phrases target) CryptoUniform.h).map
        (score coordinates adversary test) := by
  unfold FullSourceTransfer.original FullGenerationResampling.actual WalletUnbounded.real
  simp_rw [TableFactors.factor_h]
  unfold ExactRefusalLift.initial contexts
  simp only [PMF.map_bind,PMF.map_comp,PMF.bind_map,PMF.bind_bind,Function.comp_def,score,crypto]
  apply congrArg (fun next => passwords.bind next)
  funext password
  apply congrArg (fun next => phrases.bind next)
  funext phrase
  apply congrArg (fun next => (PMF.uniformOfFintype (Other (N := N) (Entropy := Entropy))).bind next)
  funext other
  unfold CryptoUniform.h
  rw [PMF.bind_comm]
  apply congrArg (fun next => (PMF.uniformOfFintype (Seed → Data)).bind next)
  funext omega
  rw [PMF.bind_comm]
  apply congrArg (fun next => (PMF.uniformOfFintype (GenerationTable (Entropy := Entropy)
    (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))).bind next)
  funext table
  simp only [PMF.map]
  rw [PMF.bind_comm]
  rfl

end FullSourceEnvironment

/-! Retrying, reporting failure, or returning any other response after the first refusal changes success only on that refusal. -/
namespace RefusalResponse
open GameExpectation MomentTools
variable {Environment : Type}

def game (prior : PMF Environment) (refused success : Environment → Bool)
    (later : Environment → PMF Bool) : PMF Bool :=
  prior.bind fun environment => if refused environment then later environment else PMF.pure (success environment)

/-- The later response need not return a successful creation, nor preserve or redraw any particular part of the environment. -/
theorem bound (prior : PMF Environment) (refused success : Environment → Bool)
    (later : Environment → PMF Bool) (upper : ENNReal) (original : (prior.map success) true ≤ upper) :
    (game prior refused success later) true ≤ upper+(prior.map refused) true := by
  have pointwise (environment : Environment) :
      (if refused environment then later environment else PMF.pure (success environment)) true ≤
        (if success environment then (1:ENNReal) else 0)+(if refused environment then 1 else 0) := by
    cases bad : refused environment with
    | false => cases success environment <;> simp
    | true =>
      simp only [if_true]
      exact ((later environment).coe_le_one true).trans (le_add_of_nonneg_left (zero_le))
  change moment prior (fun environment =>
    (if refused environment then later environment else PMF.pure (success environment)) true) ≤ _
  calc
    _ ≤ moment prior (fun environment =>
      (if success environment then 1 else 0)+(if refused environment then 1 else 0)) := mono _ _ _ pointwise
    _ = (prior.map success) true+(prior.map refused) true := by rw [MomentTools.add,← probability,← probability]
    _ ≤ _ := add_le_add original le_rfl

end RefusalResponse

/-! Actual first-attempt refusal for the profile source, with no independence assumption between E and S/T/Q. -/
namespace FullSourceRefusal
open Gamma2Model TableFactors FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data : Type}

def refused (coordinates : Entropy ≃ State)
    (sample : Context N Entropy Passphrase Seed Check Tail Data × HTable) : Bool :=
  ExactRefusalLift.refused (fun context h =>
    KnownPairModel.cipher context.password context.other.1 context.other.2.1 h
      (coordinates context.chosen.entropy)) (fun context => coordinates context.chosen.entropy) sample

/-- The State-coordinate test is exactly ciphertext=original entropy in the actual source coordinates. -/
theorem actual_refusal (coordinates : Entropy ≃ State) [DecidableEq Entropy]
    (sample : Context N Entropy Passphrase Seed Check Tail Data × HTable) :
    refused coordinates sample=decide
      (FullSourceCoordinates.cipher coordinates sample.1.password (crypto sample.1 sample.2)
        sample.1.chosen.entropy=sample.1.chosen.entropy) := by
  apply Bool.eq_iff_iff.mpr
  simp only [refused,ExactRefusalLift.refused,decide_eq_true_eq]
  change KnownPairModel.cipher sample.1.password sample.1.other.1 sample.1.other.2.1 sample.2
    (coordinates sample.1.chosen.entropy)=coordinates sample.1.chosen.entropy ↔
    coordinates.symm (KnownPairModel.cipher sample.1.password sample.1.other.1 sample.1.other.2.1 sample.2
      (coordinates sample.1.chosen.entropy))=sample.1.chosen.entropy
  constructor
  · intro equal
    rw [equal]
    exact coordinates.symm_apply_apply _
  · intro equal
    have same := congrArg coordinates equal
    simpa only [Equiv.apply_symm_apply] using same

variable [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

def initial (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check) :=
  ExactRefusalLift.initial
    (contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) (Data := Data) passwords phrases target)
    CryptoUniform.h

/-- Source selection reads no H, so G9 applies even though the entropy was selected using the passphrase and seed/check functions. -/
theorem probability (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (target : Check) : ((initial (Entropy := Entropy) (Seed := Seed) (Tail := Tail) (Data := Data) passwords phrases target).map
      (refused coordinates)) true=(2^256:ENNReal)⁻¹ :=
  G9Game.probability (contexts passwords phrases target)
    (fun context => context.password) (fun context => context.other.1) (fun context => context.other.2.1)
    (fun context => coordinates context.chosen.entropy)

/-- This response covers a reported failure or arbitrary retry behavior after the first refused attempt. -/
def game (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (target : Check) (success : Context N Entropy Passphrase Seed Check Tail Data × HTable → Bool)
    (later : Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool) : PMF Bool :=
  RefusalResponse.game (initial passwords phrases target) (refused coordinates) success later

/-- Every checked success bound for this actual first-attempt environment gains precisely the G9 refusal term. -/
theorem bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (target : Check) (success : Context N Entropy Passphrase Seed Check Tail Data × HTable → Bool)
    (later : Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (upper : ENNReal) (original : ((initial passwords phrases target).map success) true ≤ upper) :
    (game coordinates passwords phrases target success later) true ≤ upper+(2^256:ENNReal)⁻¹ := by
  have result := RefusalResponse.bound (initial passwords phrases target) (refused coordinates) success later upper original
  rw [probability] at result
  exact result

end FullSourceRefusal

/-! Full finite-domain Theorem 5: actual profile generation, actual cipher, adaptive attacker and creation-refusal response. -/
namespace Theorem5
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

/-- The complete epsilon_W, including the exact first creation-refusal allowance. -/
def error (p1 s1 : ENNReal) (kA kS qB qH qT qOmega : Nat) : ENNReal :=
  Theorem5Base.error p1 s1 kA kS qB qH qT qOmega+(2^256:ENNReal)⁻¹

/-- Theorem 5(a): recovery of the real seed, with independent secrets, actual source generation and all stated query budgets. -/
theorem seed_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullSourceRefusal.game coordinates passwords phrases target
      (score coordinates adversary (fun _ _ seed result => decide (output result=seed))) later) true ≤
      W1.top2 passwords phrases (kA/12) kS+error p1 s1 kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  have base := Theorem5Base.seed_bound coordinates passwords phrases sorted target output adversary p1 s1
    largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  rw [FullSourceEnvironment.original] at base
  have result := FullSourceRefusal.bound coordinates passwords phrases target
    (score coordinates adversary (fun _ _ seed result => decide (output result=seed))) later _ base
  exact result.trans (le_of_eq (by unfold error; abel))

/-- Theorem 5(b): output of the actual secret pair retains the minimum of the two pair-mass bounds. -/
theorem pair_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Fin N × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullSourceRefusal.game coordinates passwords phrases target
      (score coordinates adversary (fun password phrase _ result => decide (output result=(password,phrase)))) later) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+error p1 s1 kA kS qB qH qT qOmega := by
  have base := Theorem5Base.pair_bound coordinates passwords phrases sorted target output adversary p1 s1
    largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  rw [FullSourceEnvironment.original] at base
  have result := FullSourceRefusal.bound coordinates passwords phrases target
    (score coordinates adversary (fun password phrase _ result => decide (output result=(password,phrase)))) later _ base
  exact result.trans (le_of_eq (by unfold error; abel))

end Theorem5

/-! Independent private random coins preserve both hard-budget Theorem 5 bounds. -/
namespace Theorem5Randomized
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result Strategy : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

theorem seed_bound (coins : PMF Strategy) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (target : Check) (output : Result → Seed)
    (adversary : Strategy → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : ∀ strategy,Budgets (adversary strategy) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => FullSourceRefusal.game coordinates passwords phrases target
      (score coordinates (adversary strategy) (fun _ _ seed result => decide (output result=seed))) (later strategy)) true ≤
      W1.top2 passwords phrases (kA/12) kS+Theorem5.error p1 s1 kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact Theorem5.seed_bound coordinates passwords phrases sorted target output (adversary strategy) (later strategy)
    p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth (budget strategy)

theorem pair_bound (coins : PMF Strategy) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (target : Check) (output : Result → Fin N × Passphrase)
    (adversary : Strategy → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : ∀ strategy,Budgets (adversary strategy) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => FullSourceRefusal.game coordinates passwords phrases target
      (score coordinates (adversary strategy) (fun password phrase _ result => decide (output result=(password,phrase)))) (later strategy)) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+Theorem5.error p1 s1 kA kS qB qH qT qOmega := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact Theorem5.pair_bound coordinates passwords phrases sorted target output (adversary strategy) (later strategy)
    p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth (budget strategy)

end Theorem5Randomized

/-! The concrete 24-word entropy, 512-bit seed and 16+240-bit check-output specialization. -/
namespace Theorem5Bits
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
attribute [local instance] FiniteBits.fintype

private theorem card (width : Nat) : Fintype.card (BitVec width)=2^width := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (Lemma3.bitEquivFin width)

variable {N : Nat} {Passphrase Result : Type} [Fintype Passphrase] [DecidableEq Passphrase] [Inhabited (Fin N)]

/-- Concrete Theorem 5(a), with public wallet data of any finite bit width. -/
def seed_bound (lambda : Nat) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (output : Result → BitVec 512)
    (adversary : FullProgram (N := N) (Entropy := BitVec 256) (Passphrase := Passphrase)
      (Seed := BitVec 512) (Check := BitVec 16) (Tail := BitVec 240) (Data := BitVec lambda) (Result := Result))
    (later : Context N (BitVec 256) Passphrase (BitVec 512) (BitVec 16) (BitVec 240) (BitVec lambda) × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (budget : Budgets adversary kA kS qB qH qT qOmega) :=
  Theorem5.seed_bound FullSourceCoordinates.bits passwords phrases sorted (0:BitVec 16)
    output adversary later p1 s1 largestP largestQ kA kS qB qH qT qOmega (card 256) (card 512) (card 16) budget

/-- Concrete Theorem 5(b), using exactly the same source profile and attacker interface. -/
def pair_bound (lambda : Nat) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (output : Result → Fin N × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := BitVec 256) (Passphrase := Passphrase)
      (Seed := BitVec 512) (Check := BitVec 16) (Tail := BitVec 240) (Data := BitVec lambda) (Result := Result))
    (later : Context N (BitVec 256) Passphrase (BitVec 512) (BitVec 16) (BitVec 240) (BitVec lambda) × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (budget : Budgets adversary kA kS qB qH qT qOmega) :=
  Theorem5.pair_bound FullSourceCoordinates.bits passwords phrases sorted (0:BitVec 16)
    output adversary later p1 s1 largestP largestQ kA kS qB qH qT qOmega (card 256) (card 512) (card 16) budget

end Theorem5Bits

end
end MhfeLean
