import MhfeLean.Chapters.SeedPairs
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # Corollary W5: recovery of the source and passphrase
-/

/-! Three-point Bad bound without a free final seed guess, used for Corollary W5. -/
namespace Theta2BadBound
open Gamma2Model GameExpectation MomentTools ProbabilityTools
open SeedQueryRun SeedQueryBounds QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [Fintype Entropy] [DecidableEq Entropy] [DecidableEq Passphrase] [Inhabited (Fin N)]
  [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]

def event (source : State → Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (sample : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) : Bool :=
  decide (bad source wallet adversary sample.1=true ∨
    sample.2 ∈ SeedWalletModel.blindSeeds (full wallet adversary sample.1.2).2)

/-- No output is inserted into the independent blind-seed candidate set. -/
theorem bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isH ≤ qH)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS)
    (budgetT : ∀ input : Input (N := N) (Entropy := Entropy),(full wallet adversary input).2.countP SeedWalletModel.isT ≤ qT)
    (budgetOmega : ∀ input : Input (N := N) (Entropy := Entropy),(full wallet adversary input).2.countP SeedWalletModel.isOmega ≤ qOmega) :
    moment (independentPair (worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if event source wallet adversary sample then 1 else 0) ≤
      W1.top2 passwords phrases (kA/12) kS+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+(qT+qOmega)/(2^512:ENNReal) := by
  classical
  let chosen := fun world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) =>
    (SeedWalletModel.blindSeeds (full wallet adversary world.2).2).toFinset
  have seedQueries := SeedQueryAssembly.bound source injective firstHalf projects passwords phrases sorted
    wallet adversary p1 s1 largestP largestQ kA kS qB qH budgetA budgetB budgetH budgetS
  have result := IndependentSeedUnion.bound (worlds passwords phrases) (bad source wallet adversary) chosen
    (event source wallet adversary) (qT+qOmega)
    (fun world => SeedWalletModel.blind_bound _ qT qOmega (budgetT world.2) (budgetOmega world.2)) _ seedQueries
    (fun sample hit => by
      rcases of_decide_eq_true hit with badS | query
      · exact Or.inl badS
      · exact Or.inr (List.mem_toFinset.mpr query))
  simpa only [seedWidth,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add] using result

end Theta2BadBound

/-! The actual unprogrammed raw game with Bad alone, so no free final seed guess is charged. -/
namespace FullRawBadBound
open Gamma2Model FullRawBound FullPlantedResampling
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [Inhabited (Fin N)]
attribute [local irreducible] finalize FinalCut.prepare

omit [Inhabited (Fin N)] in
/-- The false success test leaves exactly the actual S-query or independent blind-seed events. -/
theorem event (coordinates : Entropy ≃ State)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (sample : SeedQueryRun.World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) :
    FullRawInputs.stateScore coordinates wallet data adversary (fun _ _ _ _ => false) sample=
      Theta2BadBound.event coordinates.symm wallet (adversary data) sample := by
  rcases sample with ⟨⟨⟨password,phrase⟩,⟨container,crypto⟩⟩,seed⟩
  apply Bool.eq_iff_iff.mpr
  unfold FullRawInputs.stateScore FullPlantedTransfer.rawScore
    WalletQueryEvent.winOrBad Theta2BadBound.event
  simp only [decide_eq_true_eq,Bool.false_eq_true,false_or,Equiv.apply_symm_apply]
  rw [FullSourceCoordinates.inverse]
  simp only [SeedQueryRun.bad,decide_eq_true_eq]
  simp only [SeedQueryRun.pairs,SeedQueryRun.full,Equiv.apply_symm_apply]

variable [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- Same exact nine-factor averaging as Theorem 5, but the event has no final-output singleton. -/
theorem bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullRawInputs.rawGame coordinates passwords phrases adversary (fun _ _ _ _ => false)) true ≤
      W1.top2 passwords phrases (kA/12) kS+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+(qT+qOmega)/(2^512:ENNReal) := by
  apply FullRawBound.shared coordinates passwords phrases adversary _ _
  intro wallet data
  simp_rw [event]
  exact Theta2BadBound.bound coordinates.symm coordinates.symm.injective
    (FullSourceCoordinates.firstHalf coordinates) (FullSourceCoordinates.projects coordinates)
    passwords phrases sorted wallet (adversary data) p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth
    (budget.a wallet data) (budget.b wallet data) (budget.h wallet data) (budget.s wallet data)
    (budget.t wallet data) (budget.omega wallet data)

end FullRawBadBound

/-! Corollary W5 instrumentation: append the output entropy/passphrase as one actual S query. -/
namespace WalletOutputQuery
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}

abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev FullSpec := combinedSpec (Password := Password) (Entropy := Entropy)
  (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))

local notation "AttackSpec" => FullSpec (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)

/-- The answer is discarded; the original result and all original queries are preserved. -/
def augment (output : Result → Entropy × Passphrase)
    (program : OracleComp (AttackSpec) Result) := do
  let result ← program
  let _seed ← TranscriptErasure.ask (spec := FullSpec) (Sum.inr (.s (output result).1 (output result).2))
  pure result

/-- This is an emitted S query, rather than a free direct guess of entropy. -/
theorem execution (crypto : Tables Password Entropy)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data)
    (output : Result → Entropy × Passphrase)
    (program : OracleComp (AttackSpec) Result) :
    TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet))
      (augment output program)=
      let first := TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program
      (first.1,first.2++[Sum.inr (.s (output first.1).1 (output first.1).2)]) := by
  simp only [augment,TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,
    TranscriptErasure.execute_pure,List.append_nil]

/-- Partial evaluation removes the appended wallet call, so the full crypto execution and log are identical. -/
theorem crypto_execution (crypto : Tables Password Entropy)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data)
    (output : Result → Entropy × Passphrase)
    (program : OracleComp (AttackSpec) Result) :
    execute crypto (compile WalletSpec (SeedWalletModel.answer wallet) (augment output program))=
      execute crypto (compile WalletSpec (SeedWalletModel.answer wallet) program) := by
  rw [WalletCryptoCompiler.execution,WalletCryptoCompiler.execution,execution]
  simp only [W4TraceProjection.crypto_append,W4TraceProjection.crypto,List.append_nil]

/-- Exactly one pair is appended, including when it repeats an earlier query. -/
theorem seed_pairs (crypto : Tables Password Entropy)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data)
    (output : Result → Entropy × Passphrase)
    (program : OracleComp (AttackSpec) Result) :
    SeedWalletModel.seedPairs (TranscriptErasure.execute
      (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) (augment output program)).2=
      let first := TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program
      SeedWalletModel.seedPairs first.2++[output first.1] := by
  rw [execution]
  simp only [SeedWalletModel.seedPairs,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
    SeedQueryMetadata.extract,SeedWalletModel.seedPair]

/-- The extra S call does not contribute a T or Omega query, or any blind-seed candidate. -/
theorem blind_seeds (crypto : Tables Password Entropy)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data)
    (output : Result → Entropy × Passphrase)
    (program : OracleComp (AttackSpec) Result) :
    SeedWalletModel.blindSeeds (TranscriptErasure.execute
      (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) (augment output program)).2=
      SeedWalletModel.blindSeeds (TranscriptErasure.execute
        (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2 := by
  rw [execution]
  simp only [SeedWalletModel.blindSeeds,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
    SeedWalletModel.blindSeed,List.append_nil]

/-- Neither cheap query budget changes when the output pair is queried at S. -/
theorem cheap_counts (crypto : Tables Password Entropy)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data)
    (output : Result → Entropy × Passphrase)
    (program : OracleComp (AttackSpec) Result) :
    let first := TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program
    let later := TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) (augment output program)
    later.2.countP SeedWalletModel.isT=first.2.countP SeedWalletModel.isT ∧
      later.2.countP SeedWalletModel.isOmega=first.2.countP SeedWalletModel.isOmega := by
  rw [execution]
  simp only [List.countP_append,List.countP_cons,List.countP_nil,SeedWalletModel.isT,
    SeedWalletModel.isOmega,Bool.false_eq_true,if_false,Nat.add_zero,and_self]

end WalletOutputQuery

/-! Exact hard-budget transport for treating a final phrase/passphrase output as one more S call. -/
namespace WalletOutputBudget
open Gamma2Model FullRawBound WalletCryptoCompiler
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}

def program (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) :=
  fun data container => WalletOutputQuery.augment output (adversary data container)

/-- Only kS increases, exactly by one; no crypto call, T call or Omega call is added. -/
theorem budgets (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (kA kS qB qH qT qOmega : Nat) (original : Budgets adversary kA kS qB qH qT qOmega) :
    Budgets (program output adversary) kA (kS+1) qB qH qT qOmega := by
  constructor
  · intro wallet data container crypto
    change (execute crypto (compile _ (SeedWalletModel.answer wallet)
      (WalletOutputQuery.augment output (adversary data container)))).2.countP _ ≤ kA
    rw [WalletOutputQuery.crypto_execution]
    exact original.a wallet data container crypto
  · intro wallet data container crypto
    change (execute crypto (compile _ (SeedWalletModel.answer wallet)
      (WalletOutputQuery.augment output (adversary data container)))).2.countP _ ≤ qB
    rw [WalletOutputQuery.crypto_execution]
    exact original.b wallet data container crypto
  · intro wallet data container crypto
    change (execute crypto (compile _ (SeedWalletModel.answer wallet)
      (WalletOutputQuery.augment output (adversary data container)))).2.countP _ ≤ qH
    rw [WalletOutputQuery.crypto_execution]
    exact original.h wallet data container crypto
  · intro wallet data input
    unfold SeedQueryRun.pairs SeedQueryRun.full program
    rw [WalletOutputQuery.seed_pairs,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (original.s wallet data input) 1
  · intro wallet data input
    change (TranscriptErasure.execute (combinedAnswer _ input.2 (SeedWalletModel.answer wallet))
      (WalletOutputQuery.augment output (adversary data input.1))).2.countP _ ≤ qT
    rw [(WalletOutputQuery.cheap_counts input.2 wallet output (adversary data input.1)).1]
    exact original.t wallet data input
  · intro wallet data input
    change (TranscriptErasure.execute (combinedAnswer _ input.2 (SeedWalletModel.answer wallet))
      (WalletOutputQuery.augment output (adversary data input.1))).2.countP _ ≤ qOmega
    rw [(WalletOutputQuery.cheap_counts input.2 wallet output (adversary data input.1)).2]
    exact original.omega wallet data input

end WalletOutputBudget

/-! A correct phrase/passphrase output is covered by the augmented S-query Bad event, without a blind seed guess. -/
namespace WalletOutputProgramming
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev WalletTables := SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data
abbrev Program := OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
  (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] in
theorem output_member (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (output : Result → Entropy × Passphrase)
    (program : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) :
    output (TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet))
      (WalletOutputQuery.augment output program)).1 ∈
      SeedWalletModel.seedPairs (TranscriptErasure.execute
        (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet))
          (WalletOutputQuery.augment output program)).2 := by
  rw [WalletOutputQuery.seed_pairs,WalletOutputQuery.execution]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The only transferred event is the union of all three programmed-point queries in the plain execution. -/
theorem pointwise (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (output : Result → Entropy × Passphrase)
    (program : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (target : Check) (data : Data) :
    (if output (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
        (SeedWalletModel.answer (WalletProgramming.updated wallet entropy phrase seed target data))) program).1=(entropy,phrase)
      then 1 else 0 : ENNReal) ≤
    if WalletQueryEvent.winOrBad crypto wallet (WalletOutputQuery.augment output program)
      entropy phrase seed (fun _ => false) then 1 else 0 := by
  classical
  let augmented := WalletOutputQuery.augment output program
  have result := WalletQueryEvent.pointwise crypto wallet augmented entropy phrase seed target data
    (fun result => decide (output result=(entropy,phrase)))
  have drop : WalletQueryEvent.winOrBad crypto wallet augmented entropy phrase seed
      (fun result => decide (output result=(entropy,phrase)))=
    WalletQueryEvent.winOrBad crypto wallet augmented entropy phrase seed (fun _ => false) := by
    apply Bool.eq_iff_iff.mpr
    unfold WalletQueryEvent.winOrBad
    simp only [decide_eq_true_eq,Bool.false_eq_true,false_or]
    have queried := output_member crypto wallet output program
    dsimp only [augmented]
    constructor
    · rintro (correct | bad)
      · exact Or.inl (correct ▸ queried)
      · exact bad
    · intro bad
      exact Or.inr bad
  rw [drop] at result
  dsimp only [augmented] at result
  rw [WalletOutputQuery.execution] at result
  simpa only [decide_eq_true_eq] using result

end WalletOutputProgramming

/-! W5 source-entropy scoring on W3's retained observation, and its Bad-only programming transfer. -/
namespace W5Planted
open Gamma2Model FullPlantedResampling FullPlantedTransfer
open GameExpectation MomentTools WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

def score (coordinates : Entropy ≃ State) (crypto : Tables Password Entropy) (phrase : Passphrase)
    (output : Result → Entropy × Passphrase)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (observation : Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) : Bool :=
  let ⟨entropy,container,_,s,t,omega,data⟩ := observation
  decide (output (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
    (SeedWalletModel.answer ⟨s,t,omega⟩)) (adversary data (coordinates container))).1=(entropy,phrase))

theorem planted_score (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check) (omega : Seed → Data) (output : Result → Entropy × Passphrase)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (chosen : WalletGeneration.Selected Entropy Seed Tail)
    (table : TranscriptErasure.Table (WalletGeneration.spec Entropy Passphrase Seed Check Tail)) :
    decide (output (TranscriptErasure.execute (WalletGeneration.restore phrase target (some chosen) table)
      (FullGenerationCoupling.program crypto omega
        (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates password crypto entropy)) adversary chosen)).1.1=
        (chosen.entropy,phrase))=
    score coordinates crypto phrase output adversary
      (W3Source.observation (FullSourceCoordinates.cipher coordinates password crypto) phrase target chosen table omega) := by
  rw [FullGenerationCoupling.program,WalletGenerationCompiler.execution]
  rfl

variable [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]

def original (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy)
    (phrase : Passphrase) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) : PMF Bool :=
  (W3Source.original (Tail := Tail) (Wallet := Data)
    (FullSourceCoordinates.cipher coordinates password crypto) phrase target).map
      (score coordinates crypto phrase output adversary)

/-- A correct source/passphrase output is charged to the appended S call, so no final seed guess is granted. -/
theorem transfer {N : Nat} (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy)
    (phrase : Passphrase) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : Program (Password := Fin N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) :
    (original coordinates password crypto phrase target output adversary) true ≤
      (raw coordinates password crypto phrase (WalletOutputBudget.program output adversary) (fun _ _ => false)) true := by
  unfold original
  rw [W3Source.resampling,← MomentTools.bool,← MomentTools.bool]
  unfold raw W3.programmed W3.payload W3.tagProgrammed W3.omegaProgrammed
  simp only [MomentTools.bind,moment_map,Function.comp_def,PMF.bind_map]
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
  have simpaTerm := WalletOutputProgramming.pointwise crypto ⟨s,t,omega⟩ output (adversary data (coordinates container)) ((FullSourceCoordinates.cipher coordinates password crypto).symm container) phrase seed target data
  (try simp only [score,rawScore,WalletProgramming.updated,WalletOutputBudget.program,decide_eq_true_eq] at simpaTerm ⊢)
  exact simpaTerm

end W5Planted

/-! Actual rejection-source generation transfer for the W5 source/passphrase output event. -/
namespace W5Generation
open Gamma2Model FullRawBound FullPlantedResampling WalletCryptoCompiler
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]

def planted (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy)
    (phrase : Passphrase) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) : PMF Bool :=
  (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
    (WalletCapped.planted phrase target (FullGenerationCoupling.program crypto omega
      (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates password crypto entropy)) adversary)).map
      (fun view => decide (output view.2.1.1=(view.1.entropy,phrase)))

theorem planted_equal (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy)
    (phrase : Passphrase) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) :
    planted coordinates password crypto phrase target output adversary=
      W5Planted.original coordinates password crypto phrase target output adversary := by
  unfold planted WalletCapped.planted W5Planted.original W3Source.original
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  rw [PMF.bind_comm]
  apply congrArg (fun next => (PMF.uniformOfFintype (WalletGeneration.Selected Entropy Seed Tail)).bind next)
  funext chosen
  simp only [PMF.map,Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext table
  congr 1
  funext omega
  exact congrArg PMF.pure (W5Planted.planted_score coordinates password crypto phrase target omega output adversary chosen table)

variable [DecidableEq Check]

def actual (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy)
    (phrase : Passphrase) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) : PMF Bool :=
  (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
    (WalletUnbounded.real phrase target (FullGenerationCoupling.program crypto omega
      (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates password crypto entropy)) adversary)).map
      (fun view => decide (output view.2.1.1=(view.1.entropy,phrase)))

/-- Lemma W2 concerns the adversary's view, so its own kS seed calls give delta_gen; the seed query for the output
follows that view. -/
theorem bound (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy)
    (phrase : Passphrase) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    StatisticalClose.Close (actual coordinates password crypto phrase target output adversary)
      (W5Planted.original coordinates password crypto phrase target output adversary) (W2.delta kS qT) := by
  rw [← planted_equal]
  have averaged := CloseComposition.bind (PMF.uniformOfFintype (Seed → Data)) _ _
    (fun _ => W2.delta kS qT) (fun omega => CloseComposition.map _ _ _
      (FullGenerationCoupling.bound crypto omega
        (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates password crypto entropy)) adversary
        phrase target kS qT entropyWidth seedWidth checkWidth
        (fun chosen table => budget.s (WalletGenerationCompiler.wallet table omega) (omega chosen.seed) (_,crypto))
        (fun chosen table => budget.t (WalletGenerationCompiler.wallet table omega) (omega chosen.seed) (_,crypto)))
      (fun view => decide (output view.2.1.1=(view.1.entropy,phrase))))
  simpa only [actual,planted,MomentTools.constant] using averaged

end W5Generation

/-! A whole retained-environment sampler identity reusable for source-dependent winning conditions. -/
namespace FullSourceOrdered
open Gamma2Model TableFactors FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

def ordered (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check) :
    PMF (Context N Entropy Passphrase Seed Check Tail Data × HTable) :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
      (PMF.uniformOfFintype (GenerationTable (Entropy := Entropy) (Passphrase := Passphrase)
        (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
          (WalletCompletion.real table phrase target).map fun chosen =>
            (⟨password,phrase,(crypto.a,crypto.b,crypto.g),omega,table,chosen⟩,crypto.h)

/-- This retains all source/table correlations, before choosing any particular success predicate. -/
theorem initial (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check) :
    ordered (Entropy := Entropy) (Seed := Seed) (Tail := Tail) (Data := Data) passwords phrases target=
      ExactRefusalLift.initial (contexts passwords phrases target) CryptoUniform.h := by
  unfold ordered
  simp_rw [TableFactors.factor_h]
  unfold ExactRefusalLift.initial contexts
  simp only [PMF.bind_bind,PMF.bind_map,Function.comp_def]
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

end FullSourceOrdered

/-! Actual profile-source entropy/passphrase recovery game and its charged-query upper bound. -/
namespace W5Source
open Gamma2Model FullRawBound FullSourceEnvironment FullSourceTransfer
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

def original (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check)
    (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) : PMF Bool :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    W5Generation.actual coordinates password crypto phrase target output adversary

def score (coordinates : Entropy ≃ State) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (sample : Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable) : Bool :=
  let context := sample.1
  let tables := crypto context sample.2
  decide (output (TranscriptErasure.execute context.table
    (FullGenerationCoupling.program tables context.omega
      (fun entropy => coordinates (FullSourceCoordinates.cipher coordinates context.password tables entropy)) adversary
        context.chosen)).1.1=(context.chosen.entropy,context.phrase))

/-- Unlike the seed game, the score explicitly retains and tests the actual selected entropy E. -/
theorem ordered (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check)
    (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) :
    original coordinates passwords phrases target output adversary=
      (FullSourceOrdered.ordered passwords phrases target).map (score coordinates output adversary) := by
  simp only [original,W5Generation.actual,WalletUnbounded.real,FullSourceOrdered.ordered,
    PMF.map_bind,PMF.map_comp,Function.comp_def,score,crypto]
  rfl

/-- The real generation is replaced once, then a correct output is covered by the actual augmented S-query Bad event. -/
theorem transfer (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check)
    (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (original coordinates passwords phrases target output adversary) true ≤
      (FullRawInputs.rawGame coordinates passwords phrases (WalletOutputBudget.program output adversary)
        (fun _ _ _ _ => false)) true+W2.delta kS qT := by
  unfold original FullRawInputs.rawGame
  apply bind_probability
  intro password
  apply bind_probability
  intro phrase
  apply bind_probability
  intro crypto
  have close := W5Generation.bound coordinates password crypto phrase target output adversary
    kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  have first := (close id).1
  simp only [PMF.map_id] at first
  exact first.trans (add_le_add
    (W5Planted.transfer coordinates password crypto phrase target output adversary) le_rfl)

variable [Inhabited (Fin N)]

/-- epsilon_W of Corollary W5 before refusal: kS+1 in place of kS except in delta_gen, which keeps the adversary's
own kS seed calls. -/
def error (p1 s1 : ENNReal) (kA kS qB qH qT qOmega : Nat) : ENNReal :=
  (s1*((kS+1:Nat):ENNReal)+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+
    (qT+qOmega)/(2^512:ENNReal)+W2.delta kS qT

/-- W5 before refusal: the budget uses kS+1 for the seed query of the output, with no free seed-output term. -/
theorem bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (original coordinates passwords phrases target output adversary) true ≤
      W1.top2 passwords phrases (kA/12) (kS+1)+error p1 s1 kA kS qB qH qT qOmega := by
  have source := transfer coordinates passwords phrases target output adversary kA kS qB qH qT qOmega
    entropyWidth seedWidth checkWidth budget
  have raw := FullRawBadBound.bound coordinates passwords phrases sorted
    (WalletOutputBudget.program output adversary) p1 s1 largestP largestQ kA (kS+1) qB qH qT qOmega
    seedWidth (WalletOutputBudget.budgets output adversary kA kS qB qH qT qOmega budget)
  apply source.trans
  apply (add_le_add raw (le_refl (W2.delta kS qT))).trans
  exact le_of_eq (by unfold error; abel)

end W5Source

/-! Corollary W5: actual phrase entropy and passphrase recovery with one extra S query charged throughout epsilon_W. -/
namespace W5
open Gamma2Model FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

/-- This score tests the selected E itself; it does not accept another pair giving the same seed. -/
def game (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (target : Check)
    (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool) : PMF Bool :=
  FullSourceRefusal.game coordinates passwords phrases target (W5Source.score coordinates output adversary) later

/-- The complete epsilon_W of Corollary W5, with the first creation-refusal allowance. -/
def error (p1 s1 : ENNReal) (kA kS qB qH qT qOmega : Nat) : ENNReal :=
  W5Source.error p1 s1 kA kS qB qH qT qOmega+(2^256:ENNReal)⁻¹

/-- Exact source formula: top2(floor(kA/12),kS+1)+epsilon_W with kS+1 except in delta_gen, without a free
seed-output term. -/
theorem bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (game coordinates passwords phrases target output adversary later) true ≤
      W1.top2 passwords phrases (kA/12) (kS+1)+error p1 s1 kA kS qB qH qT qOmega := by
  have base := W5Source.bound coordinates passwords phrases sorted target output adversary
    p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  rw [W5Source.ordered,FullSourceOrdered.initial] at base
  have result := FullSourceRefusal.bound coordinates passwords phrases target
    (W5Source.score coordinates output adversary) later _ base
  exact result.trans (le_of_eq (by unfold error; abel))

end W5

/-! Independent private coins preserve Corollary W5's exact actual-source bound. -/
namespace W5Randomized
open Gamma2Model FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result Strategy : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

theorem bound (coins : PMF Strategy) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (target : Check) (output : Result → Entropy × Passphrase)
    (adversary : Strategy → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : ∀ strategy,Budgets (adversary strategy) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => W5.game coordinates passwords phrases target output (adversary strategy) (later strategy)) true ≤
      W1.top2 passwords phrases (kA/12) (kS+1)+W5.error p1 s1 kA kS qB qH qT qOmega := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact W5.bound coordinates passwords phrases sorted target output (adversary strategy) (later strategy)
    p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth (budget strategy)

end W5Randomized

end
end MhfeLean
