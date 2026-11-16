import MhfeLean.Chapters.CreationRefusal
import MhfeLean.Chapters.MatchingAttack
import MhfeLean.Chapters.ShortSources
import MhfeLean.Chapters.WalletData
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # G10 matching attack and first-refusal lower bounds
-/

/-! Embed a crypto program in a combined wallet oracle without changing its execution or costs. -/
namespace CryptoEmbedding
open Gamma2Model WalletCryptoCompiler
variable {Password E Wallet Result : Type}

def embed (walletSpec : OracleSpec Wallet) (program : OracleComp (spec Password E) Result) :
    OracleComp (combinedSpec (Password := Password) (Entropy := E) walletSpec) Result :=
  OracleComp.construct (fun result => pure result) (fun point _ recurse => do
    let value ← TranscriptErasure.ask (spec := combinedSpec (Password := Password) (Entropy := E) walletSpec) (.inl point)
    recurse value) program

theorem embed_pure (walletSpec : OracleSpec Wallet) (result : Result) : embed (Password := Password) (E := E) walletSpec (pure result)=pure result := rfl

theorem embed_query (walletSpec : OracleSpec Wallet) (point : Point Password E)
    (next : spec Password E point → OracleComp (spec Password E) Result) :
    embed walletSpec (ask point >>= next)=
      (TranscriptErasure.ask (spec := combinedSpec (Password := Password) (Entropy := E) walletSpec) (.inl point) >>= fun value => embed walletSpec (next value)) := rfl

attribute [local irreducible] embed

variable (walletSpec : OracleSpec Wallet) (wallet : (point : Wallet) → walletSpec point)
  (tables : Tables Password E) (program : OracleComp (spec Password E) Result)

/-- The result and full mapped log agree for every adaptive input program and all oracle tables. -/
theorem execution :
    TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) (embed walletSpec program)=
      ((execute tables program).1,(execute tables program).2.map Sum.inl) := by
  induction program using OracleComp.inductionOn with
  | pure result => rw [embed_pure]; rfl
  | query_bind point next ih =>
    change TranscriptErasure.execute (combinedAnswer walletSpec tables wallet)
      (embed walletSpec (ask point >>= next))=_
    rw [embed_query]
    simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,
      combinedAnswer,execute_bind]
    rw [ih]
    rfl

/-- Every repeated crypto lookup is counted exactly once after embedding. -/
theorem crypto_count (test : Point Password E → Bool) :
    (TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) (embed walletSpec program)).2.countP
      (G10WalletCounts.crypto test)=(execute tables program).2.countP test := by
  rw [execution,List.countP_map]
  rfl

/-- The embedding issues no wallet queries. -/
theorem wallet_count :
    (TranscriptErasure.execute (combinedAnswer walletSpec tables wallet) (embed walletSpec program)).2.countP
      G10WalletCounts.isWallet=0 := by
  rw [execution,List.countP_map]
  simp [G10WalletCounts.isWallet]

end CryptoEmbedding

/-! Actual inverse candidates and their jointly programmed verifier/wallet-data tests. -/
namespace G10CandidateData
open Gamma2Model CryptoInputs CandidateData GameExpectation
variable {Password E V R Data : Type} [DecidableEq E] [DecidableEq V] [DecidableEq Data]

def jointHash (hash : Hash ≃ V × R) : (Hash × Data) ≃ ((V × Data) × R) :=
  G10Resampling.hashPlus hash

def programmed (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data) (real : Password)
    (other : ABH Password) (container : State) (joint : E → Hash × Data) : E → Hash × Data :=
  let source := fields coordinates real other container
  Function.update joint source.1 ((jointHash hash).symm ((source.2,data),(jointHash hash (joint source.1)).2))

def passes (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data)
    (real candidate : Password) (other : ABH Password) (container : State) (joint : E → Hash × Data) :
    Bool :=
  let test := fields coordinates candidate other container
  decide (((jointHash hash) (programmed coordinates hash data real other container joint test.1)).1=(test.2,data))

/-- The real password passes both programmed checks exactly. -/
theorem real_passes (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data)
    (real : Password) (other : ABH Password) (container : State) (joint : E → Hash × Data) :
    passes coordinates hash data real real other container joint=true := by
  simp only [passes,programmed,VerifierProbability.real_passes,decide_true]

variable [Fintype Password] [DecidableEq Password] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

omit [Fintype Password] [DecidableEq Password] in
/-- Distinct entropies give the joint, rather than serialized-field, false-match rate. -/
theorem distinct_probability (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data)
    (real candidate : Password) (other : ABH Password) (container : State)
    (different : (fields coordinates candidate other container).1 ≠ (fields coordinates real other container).1) :
    moment (PMF.uniformOfFintype (E → Hash × Data)) (fun joint =>
      if passes coordinates hash data real candidate other container joint then 1 else 0)=
        1/(Fintype.card (V × Data):ENNReal) :=
  VerifierProbability.off_point (jointHash hash) _ _ different _ _

/-- The only additional way to pass is the same pairwise entropy collision bounded in G8. -/
theorem probability (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (focus real : Password) (different : real ≠ focus) (container : State) :
    moment (PMF.uniformOfFintype (ABH Password)) (fun other =>
      moment (PMF.uniformOfFintype (E → Hash × Data)) (fun joint =>
        if passes coordinates hash data real focus other container joint then 1 else 0)) ≤
      1/(Fintype.card (V × Data):ENNReal)+1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal) := by
  have fixed_bound (other : ABH Password) :
      moment (PMF.uniformOfFintype (E → Hash × Data)) (fun joint =>
        if passes coordinates hash data real focus other container joint then 1 else 0) ≤
        (if FalsePass.entropyEvent coordinates focus real container other then 1 else 0)+
          1/(Fintype.card (V × Data):ENNReal) := by
    by_cases same : (fields coordinates focus other container).1=(fields coordinates real other container).1
    · have at_most_one : moment (PMF.uniformOfFintype (E → Hash × Data)) (fun joint =>
          if passes coordinates hash data real focus other container joint then 1 else 0) ≤ 1 := by
        apply MomentTools.bounded
        intro joint
        split_ifs <;> simp only [le_refl,zero_le]
      simp only [FalsePass.entropyEvent,same,decide_true,ite_true]
      exact at_most_one.trans (le_add_right le_rfl)
    · rw [distinct_probability coordinates hash data real focus other container same]
      simp only [FalsePass.entropyEvent,same,decide_false,Bool.false_eq_true,ite_false,zero_add,le_refl]
  calc
    _ ≤ moment (PMF.uniformOfFintype (ABH Password)) (fun other =>
      (if FalsePass.entropyEvent coordinates focus real container other then 1 else 0)+
        1/(Fintype.card (V × Data):ENNReal)) := MomentTools.mono _ _ _ fixed_bound
    _ = _ := MomentTools.add _ _ _
    _ ≤ (1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal))+1/(Fintype.card (V × Data):ENNReal) := by
      rw [MomentTools.constant]
      exact add_le_add (FalsePass.collision coordinates firstHalf projects focus real different container) le_rfl
    _ = _ := by simp only [add_assoc,add_comm]

end G10CandidateData

/-! Actual ordered candidate recovery with both the packed verifier and ideal wallet-data check. -/
namespace G10WalletAttack
open Gamma2Model WalletCryptoCompiler
variable {Password E V R Data : Type} [DecidableEq V] [DecidableEq Data]
attribute [local irreducible] finalize

abbrev wallet (E Data : Type) := G10Model.walletSpec E Data
abbrev fullSpec (Password E Data : Type) := combinedSpec (Password := Password) (Entropy := E) (wallet E Data)

def query (point : Point Password E) : OracleComp (fullSpec Password E Data) (spec Password E point) :=
  TranscriptErasure.ask (spec := fullSpec Password E Data) (.inl point)

def queryWallet (e : E) : OracleComp (fullSpec Password E Data) Data :=
  TranscriptErasure.ask (spec := fullSpec Password E Data) (.inr e)

omit [DecidableEq Data] in
@[simp] theorem execute_query (tables : Tables Password E) (omega : E → Data) (point : Point Password E) :
    TranscriptErasure.execute (combinedAnswer (wallet E Data) tables omega) (query point)=
      (answer tables point,[.inl point]) := by rw [query,TranscriptErasure.execute_ask]; rfl

/-! Port to Lean 4.35: a typed `do` binding instantiates `execute` at the reduced answer type, which
`execute_query` does not match; these two instances state the same law at those types. -/
omit [DecidableEq Data] in
@[simp] theorem execute_query_g (tables : Tables Password E) (omega : E → Data) (entropy : E) :
    TranscriptErasure.execute (Result := Hash) (combinedAnswer (wallet E Data) tables omega)
      (query (Data := Data) (.g entropy))=(tables.g entropy,[.inl (.g entropy)]) :=
  execute_query tables omega (.g entropy)

omit [DecidableEq Data] in
@[simp] theorem execute_query_b (tables : Tables Password E) (omega : E → Data) (round : Fin 12)
    (right : Half) :
    TranscriptErasure.execute (Result := Half) (combinedAnswer (wallet E Data) tables omega)
      (query (Data := Data) (.b round right))=(tables.b (round,right),[.inl (.b round right)]) :=
  execute_query tables omega (.b round right)

omit [DecidableEq Data] in
@[simp] theorem execute_wallet (tables : Tables Password E) (omega : E → Data) (e : E) :
    TranscriptErasure.execute (combinedAnswer (wallet E Data) tables omega) (queryWallet e)=
      (omega e,[.inr e]) := by rw [queryWallet,TranscriptErasure.execute_ask]; rfl

def test (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data) (container : State)
    (tables : Tables Password E) (omega : E → Data) (password : Password) : Bool :=
  let source := coordinates.symm (execute tables (finalize password 12 container (by omega))).1.1
  decide (((hash (tables.g source.1)).1,omega source.1)=(source.2,data))

def run (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data)
    (container : State) (firstSalt : Half) (fallback : Password) :
    List Password → OracleComp (fullSpec Password E Data) Password
  | [] => pure fallback
  | candidate :: rest => do
    let recovered ← CryptoEmbedding.embed (wallet E Data)
      (SharedInverse.recover candidate container firstSalt)
    let source := coordinates.symm recovered
    let digest : Hash ← query (.g source.1)
    let found : Data ← queryWallet source.1
    if decide (((hash digest).1,found)=(source.2,data)) then pure candidate
    else run coordinates hash data container firstSalt fallback rest

def attack (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (candidates : List Password)
    (fallback : Password) (container : State) (data : Data) :
    OracleComp (fullSpec Password E Data) Password := do
  let salt : Half ← query (.b 11 container.1)
  run coordinates hash data container salt fallback candidates

/-- Exact first-pass behavior of the executable query program, including early stopping. -/
theorem result (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data)
    (container : State) (tables : Tables Password E) (omega : E → Data) (fallback : Password)
    (candidates : List Password) :
    (TranscriptErasure.execute (combinedAnswer (wallet E Data) tables omega)
      (run coordinates hash data container (tables.b (11,container.1)) fallback candidates)).1=
      FirstPass.choose (test coordinates hash data container tables omega) fallback candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [run,TranscriptErasure.execute_bind,CryptoEmbedding.execution,
      SharedInverse.execution,execute_query,execute_query_g,execute_query_b,execute_wallet,answer,FirstPass.choose,test]
    split_ifs <;> simp_all

/-- Sharing the first B query leaves the same first-pass result. -/
theorem attack_result (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (tables : Tables Password E) (omega : E → Data) (fallback : Password)
    (candidates : List Password) (container : State) (data : Data) :
    (TranscriptErasure.execute (combinedAnswer (wallet E Data) tables omega)
      (attack coordinates hash candidates fallback container data)).1=
      FirstPass.choose (test coordinates hash data container tables omega) fallback candidates := by
  simp only [attack,TranscriptErasure.execute_bind,execute_query,execute_query_g,execute_query_b,answer]
  exact result coordinates hash data container tables omega fallback candidates

end G10WalletAttack

/-! G10's per-real-password joint-check lower bound, including the free fallback case. -/
namespace G10FirstPass
open Gamma2Model CryptoInputs G10CandidateData
open GameExpectation ProbabilityTools
variable {Password E V R Data : Type} [Fintype Password] [DecidableEq Password]
  [Fintype E] [Nonempty E] [DecidableEq E] [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype R] [Nonempty R] [Fintype Data] [Nonempty Data] [DecidableEq Data]
attribute [local instance] FiniteBits.fintype

abbrev World (Password E Data : Type) := ABH Password × (E → Hash × Data)

def law : PMF (World Password E Data) :=
  independentPair (PMF.uniformOfFintype (ABH Password)) (PMF.uniformOfFintype (E → Hash × Data))

def delta : ENNReal := 1/(Fintype.card (V × Data):ENNReal)+1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal)

/-- A fixed preceding list gives a finite union; its tests may be arbitrarily correlated. -/
theorem before_bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1) (real : Password)
    (container : State) (earlier : List Password) (no_real : real ∉ earlier)
    (win : World Password E Data → Bool)
    (rescued : ∀ world,(∀ candidate ∈ earlier, passes coordinates hash data real candidate world.1 container world.2=false) → win world=true) :
    1-(earlier.length:ENNReal)*delta (V := V) (Data := Data) ≤ moment law (fun world => if win world then 1 else 0) := by
  let bad (i : Fin earlier.length) (world : World Password E Data) :=
    passes coordinates hash data real (earlier.get i) world.1 container world.2
  apply FirstPass.probability law win earlier.length bad (delta (V := V) (Data := Data))
  · intro world
    by_cases failed : ∃ i,bad i world=true
    · exact Or.inr failed
    · apply Or.inl
      apply rescued world
      intro candidate member
      obtain ⟨i,equal⟩ := List.mem_iff_get.mp member
      cases hit : passes coordinates hash data real candidate world.1 container world.2 with
      | false => rfl
      | true =>
        exact False.elim (failed ⟨i,by simpa only [bad,equal] using hit⟩)
  · intro i
    have different : real ≠ earlier.get i := by
      intro equal
      exact no_real (equal.symm ▸ List.get_mem earlier i)
    have estimate := G10CandidateData.probability coordinates hash data firstHalf projects (earlier.get i) real different container
    simpa only [law,independentPair,MomentTools.bind,moment_map,Function.comp_def,bad,delta] using estimate

/-- A real tested candidate is returned unless an earlier candidate passes. -/
theorem tested (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (real fallback : Password) (container : State) (earlier later : List Password)
    (no_real : real ∉ earlier) : 1-(earlier.length:ENNReal)*delta (V := V) (Data := Data) ≤ moment law (fun world =>
      if decide (FirstPass.choose
        (fun candidate => passes coordinates hash data real candidate world.1 container world.2)
        fallback (earlier ++ real :: later)=real) then 1 else 0) := by
  apply before_bound coordinates hash data firstHalf projects real container earlier no_real
  intro world fail
  apply decide_eq_true
  exact FirstPass.selected _ fallback real earlier later fail
    (G10CandidateData.real_passes coordinates hash data real world.1 container world.2)

/-- The final untested candidate incurs only the false-pass losses of preceding tests. -/
theorem fallback (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1) (real : Password)
    (container : State) (earlier : List Password) (no_real : real ∉ earlier) :
    1-(earlier.length:ENNReal)*delta (V := V) (Data := Data) ≤ moment law (fun world =>
      if decide (FirstPass.choose
        (fun candidate => passes coordinates hash data real candidate world.1 container world.2)
        real earlier=real) then 1 else 0) := by
  apply before_bound coordinates hash data firstHalf projects real container earlier no_real
  intro world fail
  exact decide_eq_true (FirstPass.fallback _ real earlier fail)

end G10FirstPass

/-! Per-real-password success of the concrete oracle attack in the exact programmed experiment. -/
namespace G10Conditional
open Gamma2Model CryptoInputs CandidateData GameExpectation
variable {Password E V R Data : Type} [DecidableEq E] [DecidableEq V] [DecidableEq Data]
attribute [local irreducible] finalize

/-- Replacing G at the genuine source does not affect any candidate's ABH inverse. -/
theorem test (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (real candidate : Password) (other : ABH Password) (container : State) (g : E → Hash × Data) :
    G10WalletAttack.test coordinates hash data container
      (tables other (fun e => (G10CandidateData.programmed coordinates hash data real other container g e).1))
      (fun e => (G10CandidateData.programmed coordinates hash data real other container g e).2) candidate=
      G10CandidateData.passes coordinates hash data real candidate other container g := by
  unfold G10WalletAttack.test
  rw [CandidateData.actual]
  rfl

/-- The actual adaptive stopping attack has the same output as the pure first-pass search. -/
theorem result (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (real fallback : Password) (candidates : List Password) (other : ABH Password)
    (container : State) (g : E → Hash × Data) :
    (TranscriptErasure.execute
      (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec E Data)
        (tables other (fun e => (G10CandidateData.programmed coordinates hash data real other container g e).1))
        (fun e => (G10CandidateData.programmed coordinates hash data real other container g e).2))
      (G10WalletAttack.attack coordinates hash candidates fallback container data)).1=
      FirstPass.choose
        (fun candidate => G10CandidateData.passes coordinates hash data real candidate other container g) fallback candidates := by
  rw [G10WalletAttack.attack_result]
  have same : G10WalletAttack.test coordinates hash data container
      (tables other (fun e => (G10CandidateData.programmed coordinates hash data real other container g e).1))
      (fun e => (G10CandidateData.programmed coordinates hash data real other container g e).2)=
      fun candidate => G10CandidateData.passes coordinates hash data real candidate other container g := by
    funext candidate
    exact test coordinates hash data real candidate other container g
  rw [same]

variable [Fintype Password] [DecidableEq Password] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- Conditional on a fixed genuine tested candidate, only preceding false passes can spoil success. -/
theorem tested (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (real fallback : Password) (container : State) (earlier later : List Password)
    (no_real : real ∉ earlier) : 1-(earlier.length:ENNReal)*G10FirstPass.delta (V := V) (Data := Data) ≤
      moment G10FirstPass.law (fun world =>
        if decide ((TranscriptErasure.execute
          (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec E Data)
            (tables world.1 (fun e => (G10CandidateData.programmed coordinates hash data real world.1 container world.2 e).1))
            (fun e => (G10CandidateData.programmed coordinates hash data real world.1 container world.2 e).2))
          (G10WalletAttack.attack coordinates hash (earlier ++ real :: later) fallback container data)).1=real)
        then 1 else 0) := by
  simpa only [result] using G10FirstPass.tested coordinates hash data firstHalf projects
    real fallback container earlier later no_real

/-- The same bound covers the final free untested candidate. -/
theorem fallback (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1) (real : Password)
    (container : State) (earlier : List Password) (no_real : real ∉ earlier) :
    1-(earlier.length:ENNReal)*G10FirstPass.delta (V := V) (Data := Data) ≤
      moment G10FirstPass.law (fun world =>
        if decide ((TranscriptErasure.execute
          (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec E Data)
            (tables world.1 (fun e => (G10CandidateData.programmed coordinates hash data real world.1 container world.2 e).1))
            (fun e => (G10CandidateData.programmed coordinates hash data real world.1 container world.2 e).2))
          (G10WalletAttack.attack coordinates hash earlier real container data)).1=real)
        then 1 else 0) := by
  simpa only [result] using G10FirstPass.fallback coordinates hash data firstHalf projects
    real container earlier no_real

end G10Conditional

/-! Rank-by-rank and weighted success of the concrete G10 wallet oracle attack. -/
namespace G10RankedSearch
open Gamma2Model CryptoInputs CandidateData GameExpectation
variable {Password E V R Data : Type} {m : Nat} [DecidableEq E] [DecidableEq V] [DecidableEq Data]
  [Fintype Password] [DecidableEq Password] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

def conditional (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (order : Fin (m+1) → Password) (container : State) (real : Password) : ENNReal :=
  moment G10FirstPass.law (fun world =>
    if decide ((TranscriptErasure.execute
      (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec E Data)
        (tables world.1 (fun e => (G10CandidateData.programmed coordinates hash data real world.1 container world.2 e).1))
        (fun e => (G10CandidateData.programmed coordinates hash data real world.1 container world.2 e).2))
      (G10WalletAttack.attack coordinates hash (RankedCandidates.tested order)
        (RankedCandidates.fallback order) container data)).1=real) then 1 else 0)

/-- Each selected rank loses at most one delta per preceding tested candidate. -/
theorem ranked (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (order : Fin (m+1) → Password) (injective : Function.Injective order) (container : State)
    (rank : Fin (m+1)) : 1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data) ≤
      conditional coordinates hash data order container (order rank) := by
  by_cases tested_rank : rank.val < m
  · let i : Fin m := ⟨rank.val,tested_rank⟩
    have same_rank : i.castSucc=rank := Fin.ext rfl
    have split : RankedCandidates.tested order=
        (RankedCandidates.tested order).take rank.val ++ order rank ::
          (RankedCandidates.tested order).drop (rank.val+1) := by
      simpa only [same_rank] using RankedCandidates.split order i
    have estimate := G10Conditional.tested coordinates hash data firstHalf projects
      (order rank) (RankedCandidates.fallback order) container
      ((RankedCandidates.tested order).take rank.val)
      ((RankedCandidates.tested order).drop (rank.val+1))
      (RankedCandidates.absent order injective rank)
    rw [← split,RankedCandidates.earlier_length] at estimate
    exact estimate
  · have last : rank=Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst rank
    have estimate := G10Conditional.fallback coordinates hash data firstHalf projects
      (RankedCandidates.fallback order) container (RankedCandidates.tested order)
      (RankedCandidates.last_absent order injective)
    (try simp only [conditional,Fin.val_last,RankedCandidates.tested,List.length_ofFn, RankedCandidates.fallback] at estimate ⊢)
    exact estimate

/-- Sum over distinct selected ranks; unselected genuine passwords contribute a nonnegative mass. -/
theorem weighted (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF Password) (order : Fin (m+1) → Password) (injective : Function.Injective order)
    (container : State) :
    (∑ rank : Fin (m+1),passwords (order rank)*
      (1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))) ≤
      moment passwords (conditional coordinates hash data order container) := by
  exact RankedCandidates.weighted_lower passwords order injective _ _
    (ranked coordinates hash data firstHalf projects order injective container)

/-- The simpler multiplicative lower bound uses at most m preceding candidates at every selected rank. -/
theorem coarse (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (data : Data)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF Password) (order : Fin (m+1) → Password) (injective : Function.Injective order)
    (container : State) :
    (∑ rank : Fin (m+1),passwords (order rank))*(1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data)) ≤
      moment passwords (conditional coordinates hash data order container) := by
  exact RankedCandidates.coarse_lower passwords order _ _
    (weighted coordinates hash data firstHalf projects passwords order injective container)

end G10RankedSearch

/-! Exact joint source-game transport of the concrete verifier/wallet matching attack. -/
namespace G10WalletTransport
open Gamma2Model CryptoInputs GameExpectation ProbabilityTools
variable {N m : Nat} {E V R Data : Type} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R]
  [Fintype Data] [Nonempty Data] [DecidableEq Data]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] finalize

/-- Full resampling preserves the real attack; disclosed Y/u are averaged independently only in Gamma1. -/
theorem source (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (order : Fin (m+1) → Fin N) : (G10Model.original (Data := Data) coordinates hash passwords
      (G10WalletAttack.attack coordinates hash (RankedCandidates.tested order)
        (RankedCandidates.fallback order))) true=
      moment (PMF.uniformOfFintype (State × Data)) (fun disclosed =>
        moment passwords (G10RankedSearch.conditional coordinates hash disclosed.2 order disclosed.1)) := by
  rw [G10Model.resampling,← MomentTools.bool]
  unfold G10Model.programmed
  rw [MomentTools.bind]
  simp_rw [MomentTools.bind,moment_map,Function.comp_def]
  rw [uniform_product (α := State × Data) (β := E → Hash × Data)]
  simp_rw [independentPair,MomentTools.bind,moment_map,Function.comp_def]
  calc
    _ = moment passwords (fun real => moment (PMF.uniformOfFintype (State × Data))
        (fun disclosed => G10RankedSearch.conditional coordinates hash disclosed.2 order disclosed.1 real)) := by
      apply congrArg (moment passwords)
      funext real
      change moment (PMF.uniformOfFintype (ABH (Fin N))) (fun other =>
        moment (PMF.uniformOfFintype (State × Data)) (fun disclosed =>
          moment (PMF.uniformOfFintype (E → Hash × Data)) (fun joint =>
            if decide ((TranscriptErasure.execute
              (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec E Data)
                (tables other (fun e => (G10CandidateData.programmed coordinates hash disclosed.2 real other disclosed.1 joint e).1))
                (fun e => (G10CandidateData.programmed coordinates hash disclosed.2 real other disclosed.1 joint e).2))
              (G10WalletAttack.attack coordinates hash (RankedCandidates.tested order)
                (RankedCandidates.fallback order) disclosed.1 disclosed.2)).1=real) then 1 else 0)))=_
      rw [G8Transport.comm]
      simp only [G10RankedSearch.conditional,G10FirstPass.law,independentPair,
        MomentTools.bind,moment_map,Function.comp_def]
    _ = _ := G8Transport.comm _ _ _

end G10WalletTransport

/-! Exact hard budgets of the executable joint verifier/wallet-data guessing strategy. -/
namespace G10WalletAttackCounts
open Gamma2Model WalletCryptoCompiler G10WalletAttack
open G10WalletCounts
variable {Password E V R Data : Type} [DecidableEq V] [DecidableEq Data]

omit [DecidableEq Data] in
/-- The embedded inverse retains all repeated A/B/H calls and adds no G or wallet query. -/
theorem recover (tables : Tables Password E) (omega : E → Data) (candidate : Password) (container : State) (salt : Half) :
    let queries := (TranscriptErasure.execute (combinedAnswer (wallet E Data) tables omega)
      (CryptoEmbedding.embed (wallet E Data) (SharedInverse.recover candidate container salt))).2
    queries.countP (crypto QueryCounts.isA)=12 ∧ queries.countP (crypto QueryCounts.isB)=11 ∧
      queries.countP (crypto QueryCounts.isH)=12 ∧ queries.countP (crypto InverseCounts.isG)=0 ∧
      queries.countP isWallet=0 := by
  simp only [CryptoEmbedding.crypto_count,CryptoEmbedding.wallet_count]
  have paid := SharedInverse.counts candidate tables container salt
  exact ⟨paid.1,paid.2.1,paid.2.2.1,paid.2.2.2,trivial⟩

/-- Early stopping only decreases the five per-candidate resource counts. -/
theorem run_counts (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (data : Data)
    (container : State) (tables : Tables Password E) (omega : E → Data) (firstSalt : Half)
    (fallback : Password) (candidates : List Password) :
    let queries := (TranscriptErasure.execute (combinedAnswer (wallet E Data) tables omega)
      (run coordinates hash data container firstSalt fallback candidates)).2
    queries.countP (crypto QueryCounts.isA) ≤ 12*candidates.length ∧
      queries.countP (crypto QueryCounts.isB) ≤ 11*candidates.length ∧
      queries.countP (crypto QueryCounts.isH) ≤ 12*candidates.length ∧
      queries.countP (crypto InverseCounts.isG) ≤ candidates.length ∧
      queries.countP isWallet ≤ candidates.length := by
  induction candidates with
  | nil => simp only [run,TranscriptErasure.execute_pure,List.countP_nil,List.length_nil,Nat.mul_zero,le_refl,and_self]
  | cons candidate rest ih =>
    have paid := recover tables omega candidate container firstSalt
    simp only [run,TranscriptErasure.execute_bind,execute_query,execute_query_g,execute_query_b,execute_wallet,answer]
    split_ifs
    · simp only [TranscriptErasure.execute_pure,List.countP_append,List.countP_cons,List.countP_nil,
        crypto,isWallet,QueryCounts.isA,QueryCounts.isB,QueryCounts.isH,
        InverseCounts.isG,Bool.false_eq_true,ite_false,ite_true,add_zero,List.length_cons]
      omega
    · simp only [List.countP_append,List.countP_cons,List.countP_nil,
        crypto,isWallet,QueryCounts.isA,QueryCounts.isB,QueryCounts.isH,
        InverseCounts.isG,Bool.false_eq_true,ite_false,ite_true,add_zero,List.length_cons]
      omega

/-- One shared initial B call yields caps12m,11m+1,12m,m,m for A/B/H/G/Omega. -/
theorem counts (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (tables : Tables Password E) (omega : E → Data) (fallback : Password) (candidates : List Password)
    (container : State) (data : Data) :
    let queries := (TranscriptErasure.execute (combinedAnswer (wallet E Data) tables omega)
      (attack coordinates hash candidates fallback container data)).2
    queries.countP (crypto QueryCounts.isA) ≤ 12*candidates.length ∧
      queries.countP (crypto QueryCounts.isB) ≤ 11*candidates.length+1 ∧
      queries.countP (crypto QueryCounts.isH) ≤ 12*candidates.length ∧
      queries.countP (crypto InverseCounts.isG) ≤ candidates.length ∧
      queries.countP isWallet ≤ candidates.length := by
  have rest := run_counts coordinates hash data container tables omega (tables.b (11,container.1)) fallback candidates
  simp only [attack,TranscriptErasure.execute_bind,execute_query,execute_query_g,execute_query_b,answer,List.singleton_append]
  simp only [List.countP_cons,crypto,isWallet,QueryCounts.isA,QueryCounts.isB,QueryCounts.isH,
    InverseCounts.isG,Bool.false_eq_true,ite_false,ite_true,add_zero]
  omega

end G10WalletAttackCounts

/-! G10: the actual joint-check matching attack, source-game success and hard query budgets. -/
namespace G10Matching
open Gamma2Model GameExpectation
variable {N m : Nat} {E V R Data : Type} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R]
  [Fintype Data] [Nonempty Data] [DecidableEq Data]
attribute [local instance] FiniteBits.fintype

/-- The more precise weighted loss holds for any fixed injective candidate order. -/
theorem weighted (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (order : Fin (m+1) → Fin N) (injective : Function.Injective order) :
    (∑ rank : Fin (m+1),passwords (order rank)*
      (1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))) ≤
    (G10Model.original (Data := Data) coordinates hash passwords
      (G10WalletAttack.attack coordinates hash (RankedCandidates.tested order)
        (RankedCandidates.fallback order))) true := by
  rw [G10WalletTransport.source (Data := Data)]
  calc
    _ = moment (PMF.uniformOfFintype (State × Data)) (fun _ =>
      ∑ rank : Fin (m+1),passwords (order rank)*
        (1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))) :=
      (MomentTools.constant _ _).symm
    _ ≤ _ := MomentTools.mono _ _ _
      (fun disclosed => G10RankedSearch.weighted coordinates hash disclosed.2 firstHalf projects passwords order injective disclosed.1)

/-- The common multiplicative loss holds in the original source game, not only the programmed game. -/
theorem coarse (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (order : Fin (m+1) → Fin N) (injective : Function.Injective order) :
    (∑ rank : Fin (m+1),passwords (order rank))*
      (1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data)) ≤
    (G10Model.original (Data := Data) coordinates hash passwords
      (G10WalletAttack.attack coordinates hash (RankedCandidates.tested order)
        (RankedCandidates.fallback order))) true := by
  rw [G10WalletTransport.source (Data := Data)]
  calc
    _ = moment (PMF.uniformOfFintype (State × Data)) (fun _ =>
      (∑ rank : Fin (m+1),passwords (order rank))*
        (1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))) :=
      (MomentTools.constant _ _).symm
    _ ≤ _ := MomentTools.mono _ _ _
      (fun disclosed => G10RankedSearch.coarse coordinates hash disclosed.2 firstHalf projects passwords order injective disclosed.1)

def attack (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (m : Nat) (positive : 0 < N) :
    G10Model.Adversary N E Data :=
  let order := PasswordPrefix.order (PasswordPrefix.within (m := m) positive)
  G10WalletAttack.attack coordinates hash (RankedCandidates.tested order)
    (RankedCandidates.fallback order)

/-- Arbitrary requested budgets are covered, including empty testing and finite dictionary saturation. -/
theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top passwords (m+1)*(1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data)) ≤
      (G10Model.original (Data := Data) coordinates hash passwords (attack coordinates hash m positive)) true := by
  let k := PasswordPrefix.count m N
  have within : k+1 ≤ N := PasswordPrefix.within positive
  let order := PasswordPrefix.order within
  have estimate := coarse (Data := Data) coordinates hash firstHalf projects passwords order (PasswordPrefix.injective within)
  rw [PasswordPrefix.mass,PasswordPrefix.saturated passwords positive] at estimate
  have index_bound : (k:ENNReal) ≤ (m:ENNReal) := by exact_mod_cast (Nat.min_le_left m (N-1))
  have loss : (k:ENNReal)*G10FirstPass.delta (V := V) (Data := Data) ≤
      (m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data) := by
    simpa only [mul_comm] using mul_le_mul_right index_bound (G10FirstPass.delta (V := V) (Data := Data))
  exact (mul_le_mul_right (tsub_le_tsub_left loss 1) _).trans estimate

omit [Fintype E] [Nonempty E] [DecidableEq E] [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
  [Fintype Data] [Nonempty Data] in
/-- Every actual run has the same hard five-resource caps, including all repeats. -/
theorem budgets (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (m : Nat) (positive : 0 < N) (tables : Tables (Fin N) E) (omega : E → Data)
    (container : State) (data : Data) :
    let queries := (TranscriptErasure.execute
      (WalletCryptoCompiler.combinedAnswer (G10Model.walletSpec E Data) tables omega)
      (attack coordinates hash m positive container data)).2
    queries.countP (G10WalletCounts.crypto QueryCounts.isA) ≤ 12*m ∧
      queries.countP (G10WalletCounts.crypto QueryCounts.isB) ≤ 11*m+1 ∧
      queries.countP (G10WalletCounts.crypto QueryCounts.isH) ≤ 12*m ∧
      queries.countP (G10WalletCounts.crypto InverseCounts.isG) ≤ m ∧
      queries.countP G10WalletCounts.isWallet ≤ m := by
  let k := PasswordPrefix.count m N
  let order := PasswordPrefix.order (PasswordPrefix.within (m := m) positive)
  have estimate := G10WalletAttackCounts.counts coordinates hash tables omega
    (RankedCandidates.fallback order) (RankedCandidates.tested order) container data
  have length : (RankedCandidates.tested order).length=k := List.length_ofFn
  rw [length] at estimate
  have limit : k ≤ m := Nat.min_le_left m (N-1)
  exact ⟨estimate.1.trans (Nat.mul_le_mul_left 12 limit),
    estimate.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 11 limit) 1),
    estimate.2.2.1.trans (Nat.mul_le_mul_left 12 limit),
    estimate.2.2.2.1.trans limit,estimate.2.2.2.2.trans limit⟩

end G10Matching

/-! The precise rank-weighted G10 lower bound, including finite dictionary saturation. -/
namespace G10MatchingWeighted
open Gamma2Model
variable {N : Nat} {E V R Data : Type} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R] [Fintype Data] [Nonempty Data] [DecidableEq Data]
attribute [local instance] FiniteBits.fintype

/-- Prefix notation denotes exactly the source's sum of per-rank false-pass losses. -/
theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ (V × R)) (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top (fun rank => passwords rank*
      (1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))) (m+1) ≤
      (G10Model.original (Data := Data) coordinates hash passwords (G10Matching.attack coordinates hash m positive)) true := by
  let k := PasswordPrefix.count m N
  have within : k+1 ≤ N := PasswordPrefix.within positive
  let order := PasswordPrefix.order within
  have estimate := G10Matching.weighted (Data := Data) coordinates hash firstHalf projects passwords order
    (PasswordPrefix.injective within)
  have sum_equal : (∑ rank : Fin (k+1),passwords (order rank)*
      (1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data)))=
      RankedMass.top (fun rank => passwords rank*
        (1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))) (k+1) :=
    PasswordPrefix.mass (fun rank : Fin N => passwords rank*
      (1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))) within
  rw [sum_equal,PasswordPrefix.saturated _ positive] at estimate
  exact estimate

end G10MatchingWeighted

/-! The joint false-match term is2^-(r+lambda) for ideal uniform bit outputs. -/
namespace G10MatchingBits
open Gamma2Model
variable {N : Nat}
attribute [local instance] FiniteBits.fintype

/-- Joint output width is justified by the product law of the ideal verifier and wallet data. -/
theorem delta (verifier width : Nat) : G10FirstPass.delta (V := BitVec verifier) (Data := BitVec width)=
      1/(2^(verifier+width):ENNReal)+1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal) := by
  simp only [G10FirstPass.delta,Fintype.card_prod,G3Probability.card_bits,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]

/-- The full source-game lower bound uses the actual bit coordinates for every source width. -/
theorem bound (tail verifier suffix width : Nat) (state_length : tail+verifier=128)
    (hash_length : verifier+suffix=256) (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top passwords (m+1)*
      (1-(m:ENNReal)*(1/(2^(verifier+width):ENNReal)+1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal))) ≤
      (G10Model.original (Data := BitVec width)
        (ShortSourceCoordinates.state tail verifier state_length)
        (BitPacking.hash verifier suffix hash_length) passwords
        (G10Matching.attack (ShortSourceCoordinates.state tail verifier state_length)
          (BitPacking.hash verifier suffix hash_length) m positive)) true := by
  have estimate := G10Matching.bound (Data := BitVec width)
    (ShortSourceCoordinates.state tail verifier state_length)
    (BitPacking.hash verifier suffix hash_length) (ShortSourceCoordinates.firstHalf tail)
    (ShortSourceCoordinates.projects tail verifier state_length) passwords m positive
  simpa only [delta] using estimate

end G10MatchingBits

/-! Lower success bounds lose at most the first-refusal probability, for arbitrary later responses. -/
namespace RefusalResponseLower
open GameExpectation MomentTools
variable {Environment : Type}

/-- The original success is covered by the response success or the first refusal. -/
theorem comparison (prior : PMF Environment) (refused success : Environment → Bool)
    (later : Environment → PMF Bool) :
    (prior.map success) true ≤ (RefusalResponse.game prior refused success later) true+
      (prior.map refused) true := by
  have pointwise (environment : Environment) :
      (if success environment then 1 else 0 : ENNReal) ≤
        (if refused environment then later environment else PMF.pure (success environment)) true+
          (if refused environment then 1 else 0) := by
    cases bad : refused environment with
    | false => cases success environment <;> simp
    | true =>
      simp only [if_true]
      cases won : success environment with
      | false => simp only [Bool.false_eq_true,ite_false,zero_le]
      | true => exact le_add_of_nonneg_left (zero_le)
  rw [probability,probability]
  change moment prior (fun environment => if success environment then 1 else 0) ≤
    moment prior (fun environment => (if refused environment then later environment else PMF.pure (success environment)) true)+
      moment prior (fun environment => if refused environment then 1 else 0)
  rw [← MomentTools.add]
  exact MomentTools.mono _ _ _ pointwise

/-- The same subtraction is meaningful even when the lower expression saturates at zero. -/
theorem bound (prior : PMF Environment) (refused success : Environment → Bool)
    (later : Environment → PMF Bool) (lower : ENNReal) (original : lower ≤ (prior.map success) true) :
    lower-(prior.map refused) true ≤ (RefusalResponse.game prior refused success later) true :=
  tsub_le_iff_right.mpr (original.trans (comparison prior refused success later))

end RefusalResponseLower

/-! The concrete G10 matching strategy loses at most one first-refusal probability. -/
namespace G10MatchingRefusal
open Gamma2Model
variable {N : Nat} {E V R Data : Type} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R]
  [Fintype Data] [Nonempty Data] [DecidableEq Data]
attribute [local instance] FiniteBits.fintype

/-- Later retries or a reported failure are allowed; only the first refused event changes the comparison. -/
theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N)
    (later : G10DirectEnvironment.Context (N := N) (E := E) (Phrase := E) (Data := Data)
      × TableFactors.HTable → PMF Bool) :
    RankedMass.top passwords (m+1)*
      (1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))-(2^256:ENNReal)⁻¹ ≤
      (G10DirectRefusal.game coordinates hash (fun _ e => e) passwords
        (G10Matching.attack coordinates hash m positive) later) true := by
  let attack := G10Matching.attack (Data := Data) coordinates hash m positive
  let lower := RankedMass.top passwords (m+1)*
    (1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))
  have source : lower ≤ (G10Model.original coordinates hash passwords attack) true :=
    G10Matching.bound coordinates hash firstHalf projects passwords m positive
  rw [G10AsDirect.original,G10DirectEnvironment.original] at source
  have result := RefusalResponseLower.bound (G10DirectEnvironment.initial passwords)
    (G10DirectRefusal.refused coordinates hash)
    (G10DirectEnvironment.score coordinates hash (fun _ e => e) attack) later lower source
  rw [G10DirectRefusal.probability] at result
  exact result

end G10MatchingRefusal

/-! The actual G8 matching-attack lower bound also survives the specification's first-refusal response. -/
namespace G8Refusal
open Gamma2Model
variable {N : Nat} {E V R : Type} [Fintype E] [Nonempty E] [DecidableEq E]
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

/-- Couple the actual packed source and functions, with arbitrary behavior after the first refusal. -/
theorem bound (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N)
    (later : ShortSourceEnvironment.Context (N := N) (E := E)
      × TableFactors.HTable → PMF Bool) :
    RankedMass.top passwords (m+1)*
      (1-(m:ENNReal)*FirstPassSource.delta (V := V))-(2^256:ENNReal)⁻¹ ≤
      (ShortSourceRefusal.game coordinates hash passwords
        (G8.attack coordinates hash m positive) (fun real _ result => decide (result=real)) later) true := by
  let attack := G8.attack coordinates hash m positive
  let lower := RankedMass.top passwords (m+1)*(1-(m:ENNReal)*FirstPassSource.delta (V := V))
  have source : lower ≤ (Theorem3.original coordinates hash passwords attack) true :=
    G8.bound coordinates hash firstHalf projects passwords m positive
  rw [ShortSourceEnvironment.password_original] at source
  have result := RefusalResponseLower.bound (ShortSourceEnvironment.initial passwords)
    (ShortSourceRefusal.refused coordinates hash)
    (ShortSourceEnvironment.score coordinates hash attack (fun real _ result => decide (result=real))) later lower source
  rw [ShortSourceRefusal.probability] at result
  exact result

end G8Refusal

end
end MhfeLean
