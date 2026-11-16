/- long: uniform-source specialization and its source/seed/pair consequences stay together. -/
-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import MhfeLean.Chapters.GenerationSurvival
import MhfeLean.Chapters.SeedPairs
import MhfeLean.Chapters.WalletRecovery
import MhfeLean.Chapters.WalletResampling
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # Corollary W6: ordinary sources and an unknown passphrase
-/

/-! Ordinary-source exact seed-table law, without a wallet-check selection or generation error. -/
namespace OrdinarySeedLaw
variable {Entropy Passphrase Seed Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Nonempty Entropy] [Nonempty Seed]

omit [Nonempty Entropy] in
/-- Conditional on a fixed entropy/passphrase, reading S equals planting its uniform output while retaining all of S. -/
theorem fixed (entropy : Entropy) (phrase : Passphrase) :
    (PMF.uniformOfFintype (Entropy × Passphrase → Seed)).map (fun table => (table,table (entropy,phrase)))=
      (PMF.uniformOfFintype Seed).bind fun seed =>
        (PMF.uniformOfFintype (Entropy × Passphrase → Seed)).map
          (fun table => (Function.update table (entropy,phrase) seed,seed)) :=
  PointProgramming.value (entropy,phrase)

/-- Uniform E stays jointly linked to its actual seed and complete S table; no rejection sampling is used. -/
theorem source (phrase : Passphrase)
    (test : Entropy → (Entropy × Passphrase → Seed) → Seed → Result) :
    (PMF.uniformOfFintype (Entropy × Passphrase → Seed)).bind (fun table =>
      (PMF.uniformOfFintype Entropy).map (fun entropy => test entropy table (table (entropy,phrase))))=
    (PMF.uniformOfFintype Entropy).bind (fun entropy =>
      (PMF.uniformOfFintype Seed).bind (fun seed =>
        (PMF.uniformOfFintype (Entropy × Passphrase → Seed)).map
          (fun table => test entropy (Function.update table (entropy,phrase) seed) seed))) := by
  have swapped := PMF.bind_comm (PMF.uniformOfFintype (Entropy × Passphrase → Seed))
    (PMF.uniformOfFintype Entropy) (fun table entropy => PMF.pure (test entropy table (table (entropy,phrase))))
  simp only [PMF.map,Function.comp_def] at swapped ⊢
  rw [swapped]
  apply congrArg (fun next => (PMF.uniformOfFintype Entropy).bind next)
  funext entropy
  have law := congrArg (fun distribution : PMF ((Entropy × Passphrase → Seed) × Seed) =>
    distribution.map (fun pair => test entropy pair.1 pair.2)) (fixed entropy phrase)
  simpa only [PMF.map,PMF.bind_bind,PMF.pure_bind,Function.comp_def] using law

end OrdinarySeedLaw

/-! W6 exact complete-table re-sampling with no wallet-check selection and no T programming. -/
namespace OrdinaryResampling
open ProbabilityTools
variable {Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
abbrev STable := Entropy × Passphrase → Seed
abbrev TTable := Seed → Check × Tail
abbrev Observation := W3.Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
  (Check := Check) (Tail := Tail) (Wallet := Data)

def payload (cipher : Equiv.Perm Entropy) (entropy : Entropy)
    (s : STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)) (seed : Seed) :
    PMF (Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) :=
  (PMF.uniformOfFintype (TTable (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun t =>
    (W3.omegaOriginal (Wallet := Data) seed).map fun pair =>
      (entropy,cipher entropy,seed,s,t,pair.1,pair.2)

def original (cipher : Equiv.Perm Entropy) (phrase : Passphrase) : PMF (Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) :=
  (PMF.uniformOfFintype (STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind fun s =>
    (PMF.uniformOfFintype Entropy).bind fun entropy => payload cipher entropy s (s (entropy,phrase))

def planted (cipher : Equiv.Perm Entropy) (phrase : Passphrase) : PMF (Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) :=
  (PMF.uniformOfFintype Entropy).bind fun entropy =>
    (PMF.uniformOfFintype Seed).bind fun seed =>
      (PMF.uniformOfFintype (STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind fun s =>
        payload cipher entropy (Function.update s (entropy,phrase) seed) seed

/-- Reading S at the independently uniform source can be replaced exactly, retaining E, seed and all functions. -/
theorem plant (cipher : Equiv.Perm Entropy) (phrase : Passphrase) : original (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) cipher phrase=
      planted (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) cipher phrase := by
  have law := congrArg (fun distribution : PMF (PMF (Observation (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) => distribution.bind id)
    (OrdinarySeedLaw.source phrase (payload (Check := Check) (Tail := Tail) (Data := Data) cipher))
  simpa only [PMF.bind_bind,PMF.bind_map,Function.comp_def,id_eq,original,planted] using law

def programmed (cipher : Equiv.Perm Entropy) (phrase : Passphrase) : PMF (Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) :=
  (PMF.uniformOfFintype (STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind fun s =>
    (PMF.uniformOfFintype Entropy).bind fun container =>
      (PMF.uniformOfFintype Seed).bind fun seed =>
        (PMF.uniformOfFintype (TTable (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun t =>
          (W3.omegaProgrammed (Wallet := Data) seed).map fun pair =>
            (cipher.symm container,container,seed,Function.update s (cipher.symm container,phrase) seed,t,pair.1,pair.2)

/-- Only S and Omega are programmed. The entire T table is the same independent uniform function. -/
theorem resampling (cipher : Equiv.Perm Entropy) (phrase : Passphrase) : original (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) cipher phrase=
      programmed (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) cipher phrase := by
  rw [plant]
  unfold planted programmed
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype Seed)
    (PMF.uniformOfFintype (STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)))]
  rw [PMF.bind_comm (PMF.uniformOfFintype Entropy)
    (PMF.uniformOfFintype (STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)))]
  have uniform := Lemma2.uniform_permutation cipher
  conv_rhs => rw [← uniform]
  simp only [PMF.bind_map,Function.comp_def,Equiv.symm_apply_apply]
  apply congrArg (fun next => (PMF.uniformOfFintype (STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind next)
  funext s
  apply congrArg (fun next => (PMF.uniformOfFintype Entropy).bind next)
  funext entropy
  apply congrArg (fun next => (PMF.uniformOfFintype Seed).bind next)
  funext seed
  unfold payload W3.omegaOriginal W3.omegaProgrammed
  rw [PointProgramming.value]

end OrdinaryResampling

/-! Reuse the checked nine-factor sampler for arbitrary raw events, including ordinary-source games with T unprogrammed. -/
namespace RawKernel
open Gamma2Model GameExpectation MomentTools ProbabilityTools
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype
abbrev Input := FullRawInputs.RawInput (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)

def stateScore (coordinates : Entropy ≃ State) (test : Input (N := N) (Entropy := Entropy)
    (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) → Bool)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (sample : SeedQueryRun.World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) : Bool :=
  test (sample.1.1.1,sample.1.1.2,sample.1.2.2,wallet.s,coordinates.symm sample.1.2.1,sample.2,wallet.t,data,wallet.omega)

/-- Only independent input coordinates are permuted; the event itself is arbitrary. -/
theorem reorder (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (test : Input (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) → Bool) :
    moment (FullRawInputs.inputLaw passwords phrases) (fun input => if test input then 1 else 0)=
      moment (FullRawInputs.normalLaw passwords phrases)
        (fun input => if test (IndependentReorder.reorder input) then 1 else 0) :=
  IndependentReorder.moments passwords phrases sampleTables
    (PMF.uniformOfFintype (Entropy × Passphrase → Seed)) (PMF.uniformOfFintype Entropy) (PMF.uniformOfFintype Seed)
    (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype Data) (PMF.uniformOfFintype (Seed → Data))
    (fun input => if test input then 1 else 0)

omit [DecidableEq Passphrase] [DecidableEq Seed] [Fintype Passphrase] [Fintype Check]
  [Fintype Tail] [Fintype Data] [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
theorem fixed (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (test : Input (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) → Bool)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data) :
    moment (independentPair (independentPair passwords phrases)
      (independentPair (PMF.uniformOfFintype Entropy) (independentPair sampleTables (PMF.uniformOfFintype Seed))))
      (fun input => if test (IndependentReorder.reorder ((wallet.s,wallet.t,data,wallet.omega),input)) then 1 else 0)=
    moment (independentPair (SeedQueryBounds.worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if stateScore coordinates test wallet data sample then 1 else 0) := by
  simp only [SeedQueryBounds.worlds,SeedQueryBounds.views,independentPair,
    MomentTools.bind,moment_map,Function.comp_def,IndependentReorder.reorder,stateScore]
  apply congrArg (moment passwords)
  funext password
  apply congrArg (moment phrases)
  funext phrase
  have transport := FullSourceUniform.expectation coordinates
    (fun container => moment (sampleTables (Password := Fin N) (Entropy := Entropy)) (fun crypto =>
      moment (PMF.uniformOfFintype Seed) (fun seed =>
        if test (password,phrase,crypto,wallet.s,coordinates.symm container,seed,wallet.t,data,wallet.omega) then 1 else 0)))
  (try simp only [Equiv.symm_apply_apply] at transport ⊢)
  exact transport

/-- Any checked fixed-wallet Theta2 bound lifts to the exact raw sampler. -/
theorem bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (test : Input (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) → Bool)
    (upper : ENNReal) (each : ∀ wallet data,
      moment (independentPair (SeedQueryBounds.worlds passwords phrases) (PMF.uniformOfFintype Seed))
        (fun sample => if stateScore coordinates test wallet data sample then 1 else 0) ≤ upper) :
    ((FullRawInputs.inputLaw passwords phrases).map test) true ≤ upper := by
  rw [probability,reorder]
  unfold FullRawInputs.normalLaw IndependentReorder.normal
  rw [independentPair,MomentTools.bind]
  apply bounded
  rintro ⟨s,t,data,omega⟩
  rw [moment_map]
  change moment (independentPair (independentPair passwords phrases)
    (independentPair (PMF.uniformOfFintype Entropy) (independentPair sampleTables (PMF.uniformOfFintype Seed))))
    (fun input => if test (IndependentReorder.reorder ((s,t,data,omega),input)) then 1 else 0) ≤ upper
  rw [fixed coordinates passwords phrases test ⟨s,t,omega⟩ data]
  exact each ⟨s,t,omega⟩ data

end RawKernel

/-! Only Omega queries target the independently hidden seed when the check function T is unprogrammed. -/
namespace WalletOmegaQueries
variable {Password Entropy Passphrase Seed : Type}
abbrev Point := Gamma2Model.Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed

def seed : Point (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) → Option Seed
  | .inr (.omega value) => some value
  | _ => none

def targets (queries : List (Point (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))) :=
  queries.filterMap seed

/-- Repeated wallet-data tests count repeatedly; T calls contribute nothing here. -/
theorem count (queries : List (Point (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))) :
    (targets queries).length=queries.countP SeedWalletModel.isOmega := by
  induction queries with
  | nil => rfl
  | cons point rest ih =>
    simp only [targets] at ih ⊢
    cases point with
    | inl point => simpa [seed,SeedWalletModel.isOmega,List.filterMap_cons,List.countP_cons] using ih
    | inr point => cases point <;> simp [seed,SeedWalletModel.isOmega,List.filterMap_cons,List.countP_cons] <;> omega

/-- The actual unprogrammed Omega-query target set has the stated qOmega cap. -/
theorem bound [DecidableEq Seed]
    (queries : List (Point (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)))
    (qOmega : Nat) (budget : queries.countP SeedWalletModel.isOmega ≤ qOmega) :
    (targets queries).toFinset.card ≤ qOmega :=
  (List.toFinset_card_le _).trans ((count queries).trans_le budget)

/-- Membership is precisely a submitted Omega call, rather than a check-function call. -/
theorem member (queries : List (Point (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))) (value : Seed) :
    value ∈ targets queries ↔ Sum.inr (.omega value) ∈ queries := by
  induction queries with
  | nil => simp [targets]
  | cons point rest ih =>
    simp only [targets] at ih ⊢
    cases point with
    | inl point => simpa [seed,List.filterMap_cons] using ih
    | inr point => cases point <;> simp [seed,ih,List.filterMap_cons]

end WalletOmegaQueries

/-! Ordinary-source programming changes only S and Omega. The complete check function T is unchanged. -/
namespace SeedDataProgramming
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
abbrev WalletSpec := SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev WalletTables := SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data
abbrev Program := OracleComp (combinedSpec (Password := Password) (Entropy := Entropy)
  (WalletSpec (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))) Result

def updated (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (data : Data) :
    WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) :=
  ⟨Function.update wallet.s (entropy,phrase) seed,wallet.t,Function.update wallet.omega seed data⟩

/-- No T-query exclusion is needed: T has exactly the same complete table in both executions. -/
theorem execution (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (data : Data)
    (missingS : Sum.inr (.s entropy phrase) ∉ (TranscriptErasure.execute
      (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2)
    (missingOmega : Sum.inr (.omega seed) ∉ (TranscriptErasure.execute
      (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2) :
    TranscriptErasure.execute (combinedAnswer WalletSpec crypto
      (SeedWalletModel.answer (updated wallet entropy phrase seed data))) program=
    TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program := by
  apply TranscriptErasure.execute_agree program
    (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet))
    (combinedAnswer WalletSpec crypto (SeedWalletModel.answer (updated wallet entropy phrase seed data)))
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
    | t candidate => rfl
    | omega candidate =>
      have different : candidate ≠ seed := by intro equal; subst candidate; exact missingOmega member
      exact Function.update_of_ne different _ _

def bad (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) : Bool := by
  classical
  let queries := (TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).2
  exact decide (Sum.inr (.s entropy phrase) ∈ queries ∨ Sum.inr (.omega seed) ∈ queries)

/-- Arbitrary success tests transfer through the union of only the two genuinely changed points. -/
theorem pointwise (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (data : Data) (test : Result → Bool) :
    (if test (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
      (SeedWalletModel.answer (updated wallet entropy phrase seed data))) program).1 then 1 else 0 : ENNReal) ≤
    if test (TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program).1 ||
      bad crypto wallet program entropy phrase seed then 1 else 0 := by
  classical
  by_cases changed : bad crypto wallet program entropy phrase seed=true
  · simp only [changed,Bool.or_true]
    split_ifs <;> simp only [le_refl,zero_le]
  · have missing := of_decide_eq_false (Bool.eq_false_iff.mpr changed)
    have same := execution crypto wallet program entropy phrase seed data
      (fun member => missing (Or.inl member)) (fun member => missing (Or.inr member))
    rw [same]
    simp only [Bool.eq_false_iff.mpr changed,Bool.or_false,le_refl]

end SeedDataProgramming

/-! Express two-point ordinary-source programming in actual S-pair and Omega-query events. -/
namespace SeedDataQueryEvent
open Gamma2Model WalletCryptoCompiler SeedDataProgramming
variable {Password Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

def winOrBad (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (test : Result → Bool) : Bool := by
  classical
  let run := TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program
  exact decide (test run.1=true ∨ (entropy,phrase) ∈ SeedWalletModel.seedPairs run.2 ∨
    seed ∈ WalletOmegaQueries.targets run.2)

/-- Queries to T do not set Bad, because no T output was changed. -/
theorem pointwise (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (program : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (data : Data) (test : Result → Bool) :
    (if test (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
      (SeedWalletModel.answer (updated wallet entropy phrase seed data))) program).1 then 1 else 0 : ENNReal) ≤
    if winOrBad crypto wallet program entropy phrase seed test then 1 else 0 := by
  classical
  apply (SeedDataProgramming.pointwise crypto wallet program entropy phrase seed data test).trans
  let run := TranscriptErasure.execute (combinedAnswer WalletSpec crypto (SeedWalletModel.answer wallet)) program
  by_cases enabled : (test run.1 || bad crypto wallet program entropy phrase seed)=true
  · have good : winOrBad crypto wallet program entropy phrase seed test=true := by
      unfold winOrBad
      simp only [decide_eq_true_eq]
      rcases Bool.or_eq_true_iff.mp enabled with wins | badHit
      · exact Or.inl wins
      · have details : Sum.inr (.s entropy phrase) ∈ run.2 ∨ Sum.inr (.omega seed) ∈ run.2 := of_decide_eq_true badHit
        rcases details with s | omega
        · exact Or.inr (Or.inl ((WalletQueryMembership.seed_pair run.2 entropy phrase).mpr s))
        · exact Or.inr (Or.inr ((WalletOmegaQueries.member run.2 seed).mpr omega))
    change (if test run.1 || bad crypto wallet program entropy phrase seed then 1 else 0 : ENNReal) ≤ _
    rw [enabled,good]
  · change (if test run.1 || bad crypto wallet program entropy phrase seed then 1 else 0 : ENNReal) ≤ _
    simp only [Bool.eq_false_iff.mpr enabled,Bool.false_eq_true,if_false,zero_le]

/-- A source/passphrase output, charged as one extra S call, is covered by Bad alone. -/
theorem output_pointwise (crypto : Tables Password Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (output : Result → Entropy × Passphrase)
    (program : Program (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (entropy : Entropy) (phrase : Passphrase) (seed : Seed) (data : Data) :
    (if output (TranscriptErasure.execute (combinedAnswer WalletSpec crypto
        (SeedWalletModel.answer (updated wallet entropy phrase seed data))) program).1=(entropy,phrase)
      then 1 else 0 : ENNReal) ≤
    if winOrBad crypto wallet (WalletOutputQuery.augment output program) entropy phrase seed (fun _ => false)
      then 1 else 0 := by
  classical
  let augmented := WalletOutputQuery.augment output program
  have result := pointwise crypto wallet augmented entropy phrase seed data (fun result => decide (output result=(entropy,phrase)))
  have drop : winOrBad crypto wallet augmented entropy phrase seed (fun result => decide (output result=(entropy,phrase)))=
      winOrBad crypto wallet augmented entropy phrase seed (fun _ => false) := by
    apply Bool.eq_iff_iff.mpr
    unfold winOrBad
    simp only [decide_eq_true_eq,Bool.false_eq_true,false_or]
    have queried := WalletOutputProgramming.output_member crypto wallet output program
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

end SeedDataQueryEvent

/-! Ordinary-source Theta2 bounds: T is independent and unprogrammed, so only Omega queries enter the hidden-seed union. -/
namespace OrdinaryTheta2
open Gamma2Model GameExpectation MomentTools ProbabilityTools
open SeedQueryRun SeedQueryBounds FullRawBound
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [Fintype Entropy] [DecidableEq Entropy] [DecidableEq Passphrase] [Inhabited (Fin N)]
  [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]

def seedEvent (source : State → Entropy) (output : Result → Seed)
    (wallet : SeedQueryRun.WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (sample : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) : Bool :=
  decide (output (full wallet adversary sample.1.2).1=sample.2 ∨ bad source wallet adversary sample.1=true ∨
    sample.2 ∈ WalletOmegaQueries.targets (full wallet adversary sample.1.2).2)

def badEvent (source : State → Entropy)
    (wallet : SeedQueryRun.WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (sample : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) : Bool :=
  decide (bad source wallet adversary sample.1=true ∨
    sample.2 ∈ WalletOmegaQueries.targets (full wallet adversary sample.1.2).2)

/-- Seed-output allowance adds just one guess to qOmega, with no qT term. -/
theorem seed_bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords) (output : Result → Seed)
    (wallet : SeedQueryRun.WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) (data : Data)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    moment (independentPair (worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if seedEvent source output wallet (adversary data) sample then 1 else 0) ≤
      W1.top2 passwords phrases (kA/12) kS+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+qOmega/(2^512:ENNReal)+(2^512:ENNReal)⁻¹ := by
  classical
  let chosen := fun world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) =>
    insert (output (full wallet (adversary data) world.2).1)
      (WalletOmegaQueries.targets (full wallet (adversary data) world.2).2).toFinset
  have main := SeedQueryAssembly.bound source injective firstHalf projects passwords phrases sorted wallet (adversary data)
    p1 s1 largestP largestQ kA kS qB qH (budget.a wallet data) (budget.b wallet data) (budget.h wallet data) (budget.s wallet data)
  have result := IndependentSeedUnion.bound (worlds passwords phrases) (bad source wallet (adversary data)) chosen
    (seedEvent source output wallet (adversary data)) (qOmega+1)
    (fun world => (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
      (WalletOmegaQueries.bound _ qOmega (budget.omega wallet data world.2)) 1)) _ main
    (fun sample hit => by
      rcases of_decide_eq_true hit with wins | badS | query
      · exact Or.inr (Finset.mem_insert.mpr (Or.inl wins.symm))
      · exact Or.inl badS
      · exact Or.inr (Finset.mem_insert_of_mem (List.mem_toFinset.mpr query)))
  apply result.trans_eq
  rw [seedWidth]
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,ENNReal.add_div,one_div]
  abel

/-- No final output guess is charged for an augmented source/passphrase query. -/
theorem bad_bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords)
    (wallet : SeedQueryRun.WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) (data : Data)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    moment (independentPair (worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if badEvent source wallet (adversary data) sample then 1 else 0) ≤
      W1.top2 passwords phrases (kA/12) kS+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+qOmega/(2^512:ENNReal) := by
  classical
  let chosen := fun world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) =>
    (WalletOmegaQueries.targets (full wallet (adversary data) world.2).2).toFinset
  have main := SeedQueryAssembly.bound source injective firstHalf projects passwords phrases sorted wallet (adversary data)
    p1 s1 largestP largestQ kA kS qB qH (budget.a wallet data) (budget.b wallet data) (budget.h wallet data) (budget.s wallet data)
  have result := IndependentSeedUnion.bound (worlds passwords phrases) (bad source wallet (adversary data)) chosen
    (badEvent source wallet (adversary data)) qOmega
    (fun world => WalletOmegaQueries.bound _ qOmega (budget.omega wallet data world.2)) _ main
    (fun sample hit => by
      rcases of_decide_eq_true hit with badS | query
      · exact Or.inl badS
      · exact Or.inr (List.mem_toFinset.mpr query))
  simpa only [seedWidth,Nat.cast_pow,Nat.cast_ofNat] using result

def pairEvent (source : State → Entropy) (output : Result → Fin N × Passphrase)
    (wallet : SeedQueryRun.WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (sample : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) : Bool :=
  decide (PairQueryBound.event source output wallet adversary sample.1=true ∨
    sample.2 ∈ WalletOmegaQueries.targets (full wallet adversary sample.1.2).2)

/-- Both pair-mass allowances remain valid while only qOmega enters the hidden-seed union. -/
theorem pair_bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords) (output : Result → Fin N × Passphrase)
    (wallet : SeedQueryRun.WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) (data : Data)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    moment (independentPair (worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if pairEvent source output wallet (adversary data) sample then 1 else 0) ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+
      (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+qOmega/(2^512:ENNReal) := by
  classical
  let chosen := fun world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) =>
    (WalletOmegaQueries.targets (full wallet (adversary data) world.2).2).toFinset
  have main := PairQueryBound.bound source injective firstHalf projects passwords phrases sorted output wallet (adversary data)
    p1 s1 largestP largestQ kA kS qB qH (budget.a wallet data) (budget.b wallet data) (budget.h wallet data) (budget.s wallet data)
  have result := IndependentSeedUnion.bound (worlds passwords phrases)
    (PairQueryBound.event source output wallet (adversary data)) chosen
    (pairEvent source output wallet (adversary data)) qOmega
    (fun world => WalletOmegaQueries.bound _ qOmega (budget.omega wallet data world.2)) _ main
    (fun sample hit => by
      rcases of_decide_eq_true hit with mainEvent | query
      · exact Or.inl mainEvent
      · exact Or.inr (List.mem_toFinset.mpr query))
  simpa only [seedWidth,Nat.cast_pow,Nat.cast_ofNat] using result

end OrdinaryTheta2

/-! Ordinary-source raw events on the exact independently sampled environment, with T unchanged. -/
namespace OrdinaryRaw
open Gamma2Model FullPlantedResampling FullRawBound
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
abbrev Input := FullRawInputs.RawInput (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)

def score (coordinates : Entropy ≃ State)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool)
    (input : Input (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) : Bool :=
  let ⟨password,phrase,crypto,s,container,seed,t,data,omega⟩ := input
  let entropy := (FullSourceCoordinates.cipher coordinates password crypto).symm container
  SeedDataQueryEvent.winOrBad crypto ⟨s,t,omega⟩ (adversary data (coordinates container)) entropy phrase seed
    (test password phrase entropy seed)

section Sampler
variable [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

def game (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool) : PMF Bool :=
  (FullRawInputs.inputLaw passwords phrases).map (score coordinates adversary test)

end Sampler

/-- No T-query event remains after identifying the exact source coordinate. -/
theorem seed_event (coordinates : Entropy ≃ State)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (output : Result → Seed)
    (sample : SeedQueryRun.World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) :
    RawKernel.stateScore coordinates (score coordinates adversary (fun _ _ _ seed result => decide (output result=seed))) wallet data sample=
      OrdinaryTheta2.seedEvent coordinates.symm output wallet (adversary data) sample := by
  rcases sample with ⟨⟨⟨password,phrase⟩,⟨container,crypto⟩⟩,seed⟩
  apply Bool.eq_iff_iff.mpr
  unfold RawKernel.stateScore score SeedDataQueryEvent.winOrBad OrdinaryTheta2.seedEvent
  simp only [decide_eq_true_eq,Equiv.apply_symm_apply]
  rw [FullSourceCoordinates.inverse]
  simp only [SeedQueryRun.bad,decide_eq_true_eq]
  simp only [SeedQueryRun.pairs,SeedQueryRun.full,Equiv.apply_symm_apply]

theorem bad_event (coordinates : Entropy ≃ State)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (sample : SeedQueryRun.World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) :
    RawKernel.stateScore coordinates (score coordinates adversary (fun _ _ _ _ _ => false)) wallet data sample=
      OrdinaryTheta2.badEvent coordinates.symm wallet (adversary data) sample := by
  rcases sample with ⟨⟨⟨password,phrase⟩,⟨container,crypto⟩⟩,seed⟩
  apply Bool.eq_iff_iff.mpr
  unfold RawKernel.stateScore score SeedDataQueryEvent.winOrBad OrdinaryTheta2.badEvent
  simp only [decide_eq_true_eq,Bool.false_eq_true,false_or,Equiv.apply_symm_apply]
  rw [FullSourceCoordinates.inverse]
  simp only [SeedQueryRun.bad,decide_eq_true_eq]
  simp only [SeedQueryRun.pairs,SeedQueryRun.full,Equiv.apply_symm_apply]

theorem pair_event (coordinates : Entropy ≃ State)
    (wallet : SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data) (data : Data)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (output : Result → Fin N × Passphrase)
    (sample : SeedQueryRun.World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) × Seed) :
    RawKernel.stateScore coordinates (score coordinates adversary
      (fun password phrase _ _ result => decide (output result=(password,phrase)))) wallet data sample=
      OrdinaryTheta2.pairEvent coordinates.symm output wallet (adversary data) sample := by
  rcases sample with ⟨⟨⟨password,phrase⟩,⟨container,crypto⟩⟩,seed⟩
  apply Bool.eq_iff_iff.mpr
  unfold RawKernel.stateScore score SeedDataQueryEvent.winOrBad OrdinaryTheta2.pairEvent
    PairQueryBound.event
  simp only [decide_eq_true_eq,Bool.or_eq_true_iff,Equiv.apply_symm_apply]
  rw [FullSourceCoordinates.inverse]
  simp only [SeedQueryRun.bad,decide_eq_true_eq]
  simp only [SeedQueryRun.pairs,SeedQueryRun.full,Equiv.apply_symm_apply]
  tauto

end OrdinaryRaw

/-! W6 raw seed, pair and charged-source bounds with neither generation distance nor qT term. -/
namespace OrdinaryRawBounds
open Gamma2Model FullRawBound OrdinaryRaw
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

def error (p1 s1 : ENNReal) (kA kS qB qH qOmega : Nat) : ENNReal :=
  (s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+qOmega/(2^512:ENNReal)

theorem seed_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (game coordinates passwords phrases adversary (fun _ _ _ seed result => decide (output result=seed))) true ≤
      W1.top2 passwords phrases (kA/12) kS+error p1 s1 kA kS qB qH qOmega+(2^512:ENNReal)⁻¹ := by
  apply RawKernel.bound coordinates passwords phrases _ _
  intro wallet data
  simp_rw [seed_event]
  simpa only [error,add_assoc] using
    OrdinaryTheta2.seed_bound coordinates.symm coordinates.symm.injective
    (FullSourceCoordinates.firstHalf coordinates) (FullSourceCoordinates.projects coordinates)
    passwords phrases sorted output wallet data adversary p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth budget

theorem bad_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (game coordinates passwords phrases adversary (fun _ _ _ _ _ => false)) true ≤
      W1.top2 passwords phrases (kA/12) kS+error p1 s1 kA kS qB qH qOmega := by
  apply RawKernel.bound coordinates passwords phrases _ _
  intro wallet data
  simp_rw [bad_event]
  simpa only [error,add_assoc] using
    OrdinaryTheta2.bad_bound coordinates.symm coordinates.symm.injective
    (FullSourceCoordinates.firstHalf coordinates) (FullSourceCoordinates.projects coordinates)
    passwords phrases sorted wallet data adversary p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth budget

theorem pair_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Fin N × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (game coordinates passwords phrases adversary (fun password phrase _ _ result => decide (output result=(password,phrase)))) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+error p1 s1 kA kS qB qH qOmega := by
  apply RawKernel.bound coordinates passwords phrases _ _
  intro wallet data
  simp_rw [pair_event]
  simpa only [error,add_assoc] using
    OrdinaryTheta2.pair_bound coordinates.symm coordinates.symm.injective
    (FullSourceCoordinates.firstHalf coordinates) (FullSourceCoordinates.projects coordinates)
    passwords phrases sorted output wallet data adversary p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth budget

end OrdinaryRawBounds

/-! Exact ordinary-source observation scored on the actual adaptive program, before and after removing S/Omega programming. -/
namespace OrdinaryPlanted
open Gamma2Model FullRawBound WalletCryptoCompiler
open GameExpectation MomentTools
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
abbrev Observation := OrdinaryResampling.Observation (Entropy := Entropy) (Passphrase := Passphrase)
  (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)

def score (coordinates : Entropy ≃ State) (crypto : Tables (Fin N) Entropy)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Entropy → Seed → Result → Bool)
    (observation : Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) : Bool :=
  let ⟨entropy,container,seed,s,t,omega,data⟩ := observation
  test entropy seed (TranscriptErasure.execute (combinedAnswer FullPlantedResampling.WalletSpec crypto
    (SeedWalletModel.answer ⟨s,t,omega⟩)) (adversary data (coordinates container))).1

variable (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy)
  (phrase : Passphrase)

def original
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Entropy → Seed → Result → Bool) : PMF Bool :=
  (OrdinaryResampling.original (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)
    (FullSourceCoordinates.cipher coordinates password crypto) phrase).map (score coordinates crypto adversary test)

def rawScore
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Entropy → Seed → Result → Bool)
    (container : Entropy) (seed : Seed) (s : Entropy × Passphrase → Seed) (t : Seed → Check × Tail) (omega : Seed → Data) (data : Data) : Bool :=
  let entropy := (FullSourceCoordinates.cipher coordinates password crypto).symm container
  SeedDataQueryEvent.winOrBad crypto ⟨s,t,omega⟩ (adversary data (coordinates container)) entropy phrase seed (test entropy seed)

def raw
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Entropy → Seed → Result → Bool) : PMF Bool :=
  (PMF.uniformOfFintype (Entropy × Passphrase → Seed)).bind fun s => (PMF.uniformOfFintype Entropy).bind fun container =>
    (PMF.uniformOfFintype Seed).bind fun seed => (PMF.uniformOfFintype (Seed → Check × Tail)).bind fun t =>
      (PMF.uniformOfFintype Data).bind fun data => (PMF.uniformOfFintype (Seed → Data)).map fun omega =>
        rawScore coordinates password crypto phrase adversary test container seed s t omega data

/-- The exact re-sampling law can be followed by any proved pointwise operational transfer. -/
theorem transfer_of (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy) (phrase : Passphrase)
    (before after : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (testBefore testAfter : Entropy → Seed → Result → Bool)
    (pointwise : ∀ container seed s t omega data,
      (if score coordinates crypto before testBefore
        ((FullSourceCoordinates.cipher coordinates password crypto).symm container,container,seed,
          Function.update s ((FullSourceCoordinates.cipher coordinates password crypto).symm container,phrase) seed,t,
          Function.update omega seed data,data) then 1 else 0 : ENNReal) ≤
      if rawScore coordinates password crypto phrase after testAfter container seed s t omega data then 1 else 0) :
    (original coordinates password crypto phrase before testBefore) true ≤
      (raw coordinates password crypto phrase after testAfter) true := by
  unfold original
  rw [OrdinaryResampling.resampling,← MomentTools.bool,← MomentTools.bool]
  unfold raw OrdinaryResampling.programmed W3.omegaProgrammed
  simp only [MomentTools.bind,moment_map,Function.comp_def]
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
  exact pointwise container seed s t omega data

theorem transfer (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy) (phrase : Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) (test : Entropy → Seed → Result → Bool) :
    (original coordinates password crypto phrase adversary test) true ≤
      (raw coordinates password crypto phrase adversary test) true := by
  apply transfer_of
  intro container seed s t omega data
  exact SeedDataQueryEvent.pointwise crypto ⟨s,t,omega⟩ (adversary data (coordinates container))
    ((FullSourceCoordinates.cipher coordinates password crypto).symm container) phrase seed data
    (test ((FullSourceCoordinates.cipher coordinates password crypto).symm container) seed)

theorem source_transfer (coordinates : Entropy ≃ State) (password : Fin N) (crypto : Tables (Fin N) Entropy) (phrase : Passphrase)
    (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) :
    (original coordinates password crypto phrase adversary (fun entropy _ result => decide (output result=(entropy,phrase)))) true ≤
      (raw coordinates password crypto phrase (WalletOutputBudget.program output adversary) (fun _ _ _ => false)) true := by
  apply transfer_of
  intro container seed s t omega data
  have simpaTerm := SeedDataQueryEvent.output_pointwise crypto ⟨s,t,omega⟩ output (adversary data (coordinates container)) ((FullSourceCoordinates.cipher coordinates password crypto).symm container) phrase seed data
  (try simp only [score,rawScore,SeedDataProgramming.updated,WalletOutputBudget.program,decide_eq_true_eq] at simpaTerm ⊢)
  exact simpaTerm

end OrdinaryPlanted

/-! Complete ordinary-source base games: actual S(E,Q) and Omega(seed), before first creation refusal. -/
namespace OrdinarySource
open Gamma2Model FullRawBound MomentTools
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

def original (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool) : PMF Bool :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    OrdinaryPlanted.original coordinates password crypto phrase adversary (test password phrase)

def raw (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool) : PMF Bool :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    OrdinaryPlanted.raw coordinates password crypto phrase adversary (test password phrase)

/-- The raw sampler is exactly the nine independent factors used by the numerical bounds. -/
theorem raw_equal (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool) :
    raw coordinates passwords phrases adversary test=OrdinaryRaw.game coordinates passwords phrases adversary test := by
  simp only [raw,OrdinaryPlanted.raw,OrdinaryRaw.game,FullRawInputs.inputLaw,
    IndependentReorder.raw,ProbabilityTools.independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def,
    OrdinaryRaw.score,OrdinaryPlanted.rawScore]

theorem transfer (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool) :
    (original coordinates passwords phrases adversary test) true ≤
      (OrdinaryRaw.game coordinates passwords phrases adversary test) true := by
  rw [← raw_equal]
  unfold original raw
  simp only [PMF.bind_apply]
  apply mono
  intro password
  apply mono
  intro phrase
  apply mono
  intro crypto
  exact OrdinaryPlanted.transfer coordinates password crypto phrase adversary (test password phrase)

theorem source_transfer (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)) :
    (original coordinates passwords phrases adversary (fun _ phrase entropy _ result => decide (output result=(entropy,phrase)))) true ≤
      (OrdinaryRaw.game coordinates passwords phrases (WalletOutputBudget.program output adversary)
        (fun _ _ _ _ _ => false)) true := by
  rw [← raw_equal]
  unfold original raw
  simp only [PMF.bind_apply]
  apply mono
  intro password
  apply mono
  intro phrase
  apply mono
  intro crypto
  exact OrdinaryPlanted.source_transfer coordinates password crypto phrase output adversary

variable [Inhabited (Fin N)]

theorem seed_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (original coordinates passwords phrases adversary (fun _ _ _ seed result => decide (output result=seed))) true ≤
      W1.top2 passwords phrases (kA/12) kS+OrdinaryRawBounds.error p1 s1 kA kS qB qH qOmega+(2^512:ENNReal)⁻¹ :=
  (transfer coordinates passwords phrases adversary _).trans
    (OrdinaryRawBounds.seed_bound coordinates passwords phrases sorted output adversary
      p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth budget)

theorem pair_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Fin N × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (original coordinates passwords phrases adversary (fun password phrase _ _ result => decide (output result=(password,phrase)))) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+OrdinaryRawBounds.error p1 s1 kA kS qB qH qOmega :=
  (transfer coordinates passwords phrases adversary _).trans
    (OrdinaryRawBounds.pair_bound coordinates passwords phrases sorted output adversary
      p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth budget)

theorem source_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (original coordinates passwords phrases adversary (fun _ phrase entropy _ result => decide (output result=(entropy,phrase)))) true ≤
      W1.top2 passwords phrases (kA/12) (kS+1)+OrdinaryRawBounds.error p1 s1 kA (kS+1) qB qH qOmega :=
  (source_transfer coordinates passwords phrases output adversary).trans
    (OrdinaryRawBounds.bad_bound coordinates passwords phrases sorted (WalletOutputBudget.program output adversary)
      p1 s1 largestP largestQ kA (kS+1) qB qH qT qOmega seedWidth
      (WalletOutputBudget.budgets output adversary kA kS qB qH qT qOmega budget))

end OrdinarySource

/-! Ordinary-source retained environments and exact first creation refusal. -/
namespace OrdinaryContext
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
open WalletCryptoCompiler
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

def pack (password : Fin N) (phrase : Passphrase) (other : Other (N := N) (Entropy := Entropy))
    (s : Entropy × Passphrase → Seed) (entropy : Entropy) (t : Seed → Check × Tail) (omega : Seed → Data) :
    Context N Entropy Passphrase Seed Check Tail Data :=
  ⟨password,phrase,other,omega,WalletTableFactors.split.symm (s,t),⟨entropy,s (entropy,phrase),(t (s (entropy,phrase))).2⟩⟩

def contexts (passwords : PMF (Fin N)) (phrases : PMF Passphrase) :
    PMF (Context N Entropy Passphrase Seed Check Tail Data) :=
  passwords.bind fun password => phrases.bind fun phrase =>
    (PMF.uniformOfFintype (Other (N := N) (Entropy := Entropy))).bind fun other =>
      (PMF.uniformOfFintype (Entropy × Passphrase → Seed)).bind fun s =>
        (PMF.uniformOfFintype Entropy).bind fun entropy =>
          (PMF.uniformOfFintype (Seed → Check × Tail)).bind fun t =>
            (PMF.uniformOfFintype (Seed → Data)).map fun omega => pack password phrase other s entropy t omega

def initial (passwords : PMF (Fin N)) (phrases : PMF Passphrase) :=
  ExactRefusalLift.initial (contexts (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) passwords phrases)
    CryptoUniform.h

def ordered (passwords : PMF (Fin N)) (phrases : PMF Passphrase) :
    PMF (Context N Entropy Passphrase Seed Check Tail Data × HTable) :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    (PMF.uniformOfFintype (Entropy × Passphrase → Seed)).bind fun s =>
      (PMF.uniformOfFintype Entropy).bind fun entropy =>
        (PMF.uniformOfFintype (Seed → Check × Tail)).bind fun t =>
          (PMF.uniformOfFintype (Seed → Data)).map fun omega =>
            (pack password phrase (crypto.a,crypto.b,crypto.g) s entropy t omega,crypto.h)

/-- E, S, T and Omega are sampled without H; the actual source/table correlations are retained. -/
theorem ordered_initial (passwords : PMF (Fin N)) (phrases : PMF Passphrase) : ordered (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) passwords phrases=initial passwords phrases := by
  unfold ordered
  simp_rw [TableFactors.factor_h]
  unfold initial ExactRefusalLift.initial contexts
  simp only [PMF.bind_bind,PMF.bind_map,Function.comp_def]
  apply congrArg (fun next => passwords.bind next)
  funext password
  apply congrArg (fun next => phrases.bind next)
  funext phrase
  apply congrArg (fun next => (PMF.uniformOfFintype (Other (N := N) (Entropy := Entropy))).bind next)
  funext other
  unfold CryptoUniform.h
  rw [PMF.bind_comm]
  apply congrArg (fun next => (PMF.uniformOfFintype (Entropy × Passphrase → Seed)).bind next)
  funext s
  rw [PMF.bind_comm]
  apply congrArg (fun next => (PMF.uniformOfFintype Entropy).bind next)
  funext entropy
  rw [PMF.bind_comm]
  apply congrArg (fun next => (PMF.uniformOfFintype (Seed → Check × Tail)).bind next)
  funext t
  simp only [PMF.map]
  rw [PMF.bind_comm]
  rfl

def score (coordinates : Entropy ≃ State)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool)
    (sample : Context N Entropy Passphrase Seed Check Tail Data × HTable) : Bool :=
  let context := sample.1
  let crypto := FullSourceEnvironment.crypto context sample.2
  let wallet := WalletGenerationCompiler.wallet context.table context.omega
  test context.password context.phrase context.chosen.entropy context.chosen.seed
    (TranscriptErasure.execute (combinedAnswer FullPlantedResampling.WalletSpec crypto
      (SeedWalletModel.answer wallet)) (adversary (context.omega context.chosen.seed)
        (coordinates (FullSourceCoordinates.cipher coordinates context.password crypto context.chosen.entropy)))).1

/-- The ordinary-source success law is the actual S(E,Q)/Omega(seed) experiment, including the sampled E. -/
theorem original (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool) :
    OrdinarySource.original coordinates passwords phrases adversary test=
      ((initial passwords phrases).map (score coordinates adversary test)) := by
  rw [← ordered_initial]
  simp only [OrdinarySource.original,OrdinaryPlanted.original,OrdinaryResampling.original,
    OrdinaryResampling.payload,W3.omegaOriginal,ordered,PMF.map_bind,PMF.map_comp,Function.comp_def,
    score,pack,OrdinaryPlanted.score,FullSourceEnvironment.crypto,
    WalletGenerationCompiler.wallet,WalletTableFactors.split,Equiv.coe_fn_symm_mk]

/-- Even with arbitrary seed and source correlations in context, only H independence is needed for exact refusal. -/
theorem refusal_probability (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) : ((initial (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) passwords phrases).map
      (FullSourceRefusal.refused coordinates)) true=(2^256:ENNReal)⁻¹ :=
  G9Game.probability (contexts (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) passwords phrases) (fun context => context.password)
    (fun context => context.other.1) (fun context => context.other.2.1) (fun context => coordinates context.chosen.entropy)

def game (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool)
    (later : Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool) : PMF Bool :=
  RefusalResponse.game (initial passwords phrases) (FullSourceRefusal.refused coordinates)
    (score coordinates adversary test) later

theorem bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (test : Fin N → Passphrase → Entropy → Seed → Result → Bool)
    (later : Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool) (upper : ENNReal)
    (base : (OrdinarySource.original coordinates passwords phrases adversary test) true ≤ upper) :
    (game coordinates passwords phrases adversary test later) true ≤ upper+(2^256:ENNReal)⁻¹ := by
  rw [original] at base
  have result := RefusalResponse.bound (initial passwords phrases) (FullSourceRefusal.refused coordinates)
    (score coordinates adversary test) later upper base
  rw [refusal_probability] at result
  exact result

end OrdinaryContext

/-! Corollary W6: ordinary uniform 24-word source, exact recovery events, no generation distance and no programmed T query term. -/
namespace W6
open Gamma2Model FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

def error (p1 s1 : ENNReal) (kA kS qB qH qOmega : Nat) : ENNReal :=
  OrdinaryRawBounds.error p1 s1 kA kS qB qH qOmega+(2^256:ENNReal)⁻¹

theorem seed_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (OrdinaryContext.game coordinates passwords phrases adversary
      (fun _ _ _ seed result => decide (output result=seed)) later) true ≤
      W1.top2 passwords phrases (kA/12) kS+error p1 s1 kA kS qB qH qOmega+(2^512:ENNReal)⁻¹ := by
  have base := OrdinarySource.seed_bound coordinates passwords phrases sorted output adversary
    p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth budget
  have result := OrdinaryContext.bound coordinates passwords phrases adversary _ later _ base
  exact result.trans (le_of_eq (by unfold error; abel))

theorem pair_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Fin N × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (OrdinaryContext.game coordinates passwords phrases adversary
      (fun password phrase _ _ result => decide (output result=(password,phrase))) later) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+error p1 s1 kA kS qB qH qOmega := by
  have base := OrdinarySource.pair_bound coordinates passwords phrases sorted output adversary
    p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth budget
  have result := OrdinaryContext.bound coordinates passwords phrases adversary _ later _ base
  exact result.trans (le_of_eq (by unfold error; abel))

theorem source_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (sorted : Antitone passwords) (output : Result → Entropy × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (OrdinaryContext.game coordinates passwords phrases adversary
      (fun _ phrase entropy _ result => decide (output result=(entropy,phrase))) later) true ≤
      W1.top2 passwords phrases (kA/12) (kS+1)+error p1 s1 kA (kS+1) qB qH qOmega := by
  have base := OrdinarySource.source_bound coordinates passwords phrases sorted output adversary
    p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth budget
  have result := OrdinaryContext.bound coordinates passwords phrases adversary _ later _ base
  exact result.trans (le_of_eq (by unfold error; abel))

end W6

/-! Independent private coins preserve all three ordinary-source W6 recovery bounds. -/
namespace W6Randomized
open Gamma2Model FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result Strategy : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

/-- Independent coins preserve the same actual seed-recovery success bound for every hard-budget strategy. -/
theorem seed_bound (coins : PMF Strategy) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords) (output : Result → Seed)
    (adversary : Strategy → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : ∀ strategy,Budgets (adversary strategy) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => OrdinaryContext.game coordinates passwords phrases (adversary strategy)
      (fun _ _ _ seed result => decide (output result=seed)) (later strategy)) true ≤
      W1.top2 passwords phrases (kA/12) kS+W6.error p1 s1 kA kS qB qH qOmega+(2^512:ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact W6.seed_bound coordinates passwords phrases sorted output (adversary strategy) (later strategy)
    p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth (budget strategy)

/-- Independent coins preserve the same actual pair-recovery success bound for every hard-budget strategy. -/
theorem pair_bound (coins : PMF Strategy) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords) (output : Result → Fin N × Passphrase)
    (adversary : Strategy → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : ∀ strategy,Budgets (adversary strategy) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => OrdinaryContext.game coordinates passwords phrases (adversary strategy)
      (fun password phrase _ _ result => decide (output result=(password,phrase))) (later strategy)) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+W6.error p1 s1 kA kS qB qH qOmega := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact W6.pair_bound coordinates passwords phrases sorted output (adversary strategy) (later strategy)
    p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth (budget strategy)

/-- Independent coins preserve the same actual source-recovery success bound for every hard-budget strategy. -/
theorem source_bound (coins : PMF Strategy) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (sorted : Antitone passwords) (output : Result → Entropy × Passphrase)
    (adversary : Strategy → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : ∀ strategy,Budgets (adversary strategy) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => OrdinaryContext.game coordinates passwords phrases (adversary strategy)
      (fun _ phrase entropy _ result => decide (output result=(entropy,phrase))) (later strategy)) true ≤
      W1.top2 passwords phrases (kA/12) (kS+1)+W6.error p1 s1 kA (kS+1) qB qH qOmega := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact W6.source_bound coordinates passwords phrases sorted output (adversary strategy) (later strategy)
    p1 s1 largestP largestQ kA kS qB qH qT qOmega seedWidth (budget strategy)

end W6Randomized

end
end MhfeLean
