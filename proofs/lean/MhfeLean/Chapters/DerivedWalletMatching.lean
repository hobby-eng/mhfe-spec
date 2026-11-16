import MhfeLean.Chapters.WalletData
import MhfeLean.Chapters.WalletMatching
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # Checksum-aware realization of the wallet-data matching attack
-/

/-! Realize an entropy-domain wallet oracle by actual G and phrase-domain D queries. -/
namespace G10DerivedCompiler
open Gamma2Model WalletCryptoCompiler
variable {Password E Phrase Data Result : Type}

abbrev baseSpec (Password E Data : Type) := combinedSpec (Password := Password) (Entropy := E) (G10Model.walletSpec E Data)
abbrev directSpec (Password E Phrase Data : Type) := combinedSpec (Password := Password) (Entropy := E) (G10Model.walletSpec Phrase Data)

def realize (shape : E → Hash → Phrase) (program : OracleComp (baseSpec Password E Data) Result) :
    OracleComp (directSpec Password E Phrase Data) Result :=
  OracleComp.construct (fun result => pure result) (fun point _ recurse => match point with
    | .inl point => do
      let value ← TranscriptErasure.ask (spec := directSpec Password E Phrase Data) (.inl point)
      recurse value
    | .inr e => do
      let digest : Hash ← TranscriptErasure.ask (spec := directSpec Password E Phrase Data) (.inl (.g e))
      let data : Data ← TranscriptErasure.ask (spec := directSpec Password E Phrase Data) (.inr (shape e digest))
      recurse data) program

def point (shape : E → Hash → Phrase) (g : E → Hash) : Point Password E ⊕ E → List (Point Password E ⊕ Phrase)
  | .inl query => [.inl query]
  | .inr e => [.inl (.g e),.inr (shape e (g e))]

theorem realize_pure (shape : E → Hash → Phrase) (result : Result) : realize (Password := Password) (Data := Data) shape (pure result)=pure result := rfl

theorem realize_query (shape : E → Hash → Phrase) (query : Point Password E ⊕ E)
    (next : baseSpec Password E Data query → OracleComp (baseSpec Password E Data) Result) :
    realize shape (TranscriptErasure.ask query >>= next)=
      (match query with
      | .inl query => do
        let value ← TranscriptErasure.ask (spec := directSpec Password E Phrase Data) (.inl query)
        realize shape (next value)
      | .inr e => do
        let digest : Hash ← TranscriptErasure.ask (spec := directSpec Password E Phrase Data) (.inl (.g e))
        let data : Data ← TranscriptErasure.ask (spec := directSpec Password E Phrase Data) (.inr (shape e digest))
        realize shape (next data)) := by cases query <;> rfl

attribute [local irreducible] realize

/-- Only valid shape-produced D points are read; full output and every actual repeated query are preserved. -/
theorem execution (shape : E → Hash → Phrase) (tables : Tables Password E) (d : Phrase → Data)
    (program : OracleComp (baseSpec Password E Data) Result) :
    TranscriptErasure.execute (combinedAnswer (G10Model.walletSpec Phrase Data) tables d) (realize shape program)=
      let base := TranscriptErasure.execute
        (combinedAnswer (G10Model.walletSpec E Data) tables (fun e => d (shape e (tables.g e)))) program
      (base.1,base.2.flatMap (point shape tables.g)) := by
  induction program using OracleComp.inductionOn with
  | pure result => rw [realize_pure]; rfl
  | query_bind query next ih =>
    change TranscriptErasure.execute _ (realize shape (TranscriptErasure.ask query >>= next))=_
    rw [realize_query]
    cases query with
    | inl query =>
      simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,combinedAnswer]
      rw [ih]
      rfl
    | inr e =>
      simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,combinedAnswer,answer]
      rw [ih]
      rfl

end G10DerivedCompiler

/-! A G-dependent injective phrase map gives independent uniform Omega only after projecting away unobserved D values. -/
namespace G10CompositionLaw
open ProbabilityTools
variable {E H Phrase Data : Type} [DecidableEq E] [DecidableEq Phrase]
  [Fintype E] [Fintype H] [Nonempty H] [Fintype Phrase] [Fintype Data] [Nonempty Data]

def compose (shape : E → H → Phrase) (g : E → H) (d : Phrase → Data) : E → Data :=
  fun e => d (shape e (g e))

omit [Fintype H] [Nonempty H] in
/-- Conditional on the full G, the restriction of D along this injective map is fully uniform. -/
theorem fixed (shape : E → H → Phrase) (decode : Phrase → E) (decodes : ∀ e h,decode (shape e h)=e)
    (g : E → H) :
    (PMF.uniformOfFintype (Phrase → Data)).map (compose shape g)=PMF.uniformOfFintype (E → Data) := by
  apply UniformInjection.restriction
  intro first second equal
  have same := congrArg decode equal
  simpa only [decodes] using same

/-- This retains G and the whole derived Omega function, but not arbitrary D-query access. -/
theorem joint (shape : E → H → Phrase) (decode : Phrase → E) (decodes : ∀ e h,decode (shape e h)=e) :
    (PMF.uniformOfFintype ((E → H) × (Phrase → Data))).map
      (fun tables => (tables.1,compose shape tables.1 tables.2))=
        independentPair (PMF.uniformOfFintype (E → H)) (PMF.uniformOfFintype (E → Data)) := by
  rw [uniform_product]
  simp only [independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def]
  apply congrArg (fun f => (PMF.uniformOfFintype (E → H)).bind f)
  funext g
  calc
    _ = ((PMF.uniformOfFintype (Phrase → Data)).map (compose shape g)).map (fun omega => (g,omega)) :=
      (PMF.map_comp _ _ _).symm
    _ = _ := by rw [fixed shape decode decodes]

end G10CompositionLaw

/-! Exact source-game equivalence only for an explicitly realized entropy-oracle adversary. -/
namespace G10DerivedModel
open Gamma2Model CryptoInputs ProbabilityTools
variable {N : Nat} {E V R Phrase Data : Type}

def adversary (shape : E → Hash → Phrase) (base : G10Model.Adversary N E Data) :
    G10DirectModel.Adversary N E Phrase Data := fun container data =>
  G10DerivedCompiler.realize shape (base container data)

def project (shape : E → Hash → Phrase) (input : E × G10DirectModel.Table E Phrase Data) :
    E × G10DirectModel.Table E E Data :=
  (input.1,(input.2.1,G10CompositionLaw.compose shape input.2.1 input.2.2))

/-- The real direct-D program reads only shape-valid points and has exactly the projected base result. -/
theorem fixed (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (shape : E → Hash → Phrase)
    (real : Fin N) (other : ABH (Fin N)) (base : G10Model.Adversary N E Data)
    (input : E × G10DirectModel.Table E Phrase Data) :
    G10DirectModel.score real other (adversary shape base)
      (G10DirectLaw.original coordinates hash (Theorem3.cipher real other)
        (fun g e => shape e (g e)) input)=
      G10DirectModel.score real other base
        (G10DirectLaw.original coordinates hash (Theorem3.cipher real other)
          (fun _ e => e) (project shape input)) := by
  simp only [G10DirectModel.score,G10DirectModel.combined,
    G10DirectLaw.original,adversary,project,G10CompositionLaw.compose]
  let chosen := base ((Theorem3.cipher real other)
    (coordinates (input.1,(hash (input.2.1 input.1)).1)))
      (input.2.2 (shape input.1 (input.2.1 input.1)))
  have performed := G10DerivedCompiler.execution shape (tables other input.2.1) input.2.2 chosen
  exact congrArg (fun output : Fin N × List (Point (Fin N) E ⊕ Phrase) => decide (output.1=real)) performed

variable [DecidableEq E] [DecidableEq Phrase] [Fintype E] [Nonempty E]
  [Fintype Phrase] [Fintype Data] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- The full original G is retained; only the unobserved complement of D is projected away. -/
theorem law (shape : E → Hash → Phrase) (decode : Phrase → E) (decodes : ∀ e h,decode (shape e h)=e) :
    (PMF.uniformOfFintype (E × G10DirectModel.Table E Phrase Data)).map (project shape)=
      PMF.uniformOfFintype (E × G10DirectModel.Table E E Data) := by
  rw [uniform_product (α := E) (β := G10DirectModel.Table E Phrase Data)]
  simp only [independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def]
  rw [uniform_product (α := E) (β := G10DirectModel.Table E E Data)]
  apply congrArg (fun f => (PMF.uniformOfFintype E).bind f)
  funext e
  calc
    _ = ((PMF.uniformOfFintype (G10DirectModel.Table E Phrase Data)).map
        (fun tables => (tables.1,G10CompositionLaw.compose shape tables.1 tables.2))).map (fun tables => (e,tables)) :=
      (PMF.map_comp _ _ _).symm
    _ = _ := by rw [G10CompositionLaw.joint shape decode decodes,← uniform_product]

/-- This theorem does not restrict arbitrary direct-D attackers: it compares this actual realization with its base program. -/
theorem original (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R) (shape : E → Hash → Phrase)
    (decode : Phrase → E) (decodes : ∀ e h,decode (shape e h)=e) (passwords : PMF (Fin N))
    (base : G10Model.Adversary N E Data) :
    G10DirectModel.original coordinates hash (fun g e => shape e (g e)) passwords (adversary shape base)=
      G10Model.original coordinates hash passwords base := by
  rw [G10AsDirect.original]
  unfold G10DirectModel.original
  apply congrArg (fun f => passwords.bind f)
  funext real
  apply congrArg (fun f => (PMF.uniformOfFintype (ABH (Fin N))).bind f)
  funext other
  rw [← law shape decode decodes]
  simp only [PMF.map_comp,Function.comp_def]
  congr 1
  funext input
  exact fixed coordinates hash shape real other base input

end G10DerivedModel

/-! The direct realization pays for its checksum G reads instead of treating them as free. -/
namespace G10DerivedCounts
open Gamma2Model WalletCryptoCompiler G10DerivedCompiler G10WalletCounts
variable {Password E Phrase Data Result : Type}

/-- A/B/H counts are preserved; every extra point is a G or D call. -/
theorem crypto_count (shape : E → Hash → Phrase) (g : E → Hash)
    (queries : List (Point Password E ⊕ E)) (test : Point Password E → Bool)
    (ignores : ∀ e,test (.g e)=false) :
    (queries.flatMap (point shape g)).countP (crypto test)=queries.countP (crypto test) := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
    cases query <;> simp only [List.flatMap_cons,List.countP_append,List.countP_cons,List.countP_nil,
      point,crypto,ignores,Bool.false_eq_true,ite_false,add_zero,zero_add,ih,Nat.add_comm] <;> rfl

/-- Each base Omega call adds one genuine G call, with repeats retained. -/
theorem g_count (shape : E → Hash → Phrase) (g : E → Hash) (queries : List (Point Password E ⊕ E)) :
    (queries.flatMap (point shape g)).countP (crypto InverseCounts.isG)=
      queries.countP (crypto InverseCounts.isG)+queries.countP isWallet := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
    rcases query with ((_ | _ | _ | _) | e) <;>
      simp only [List.flatMap_cons,List.countP_append,List.countP_cons,List.countP_nil,
        point,crypto,isWallet,InverseCounts.isG,Bool.false_eq_true,ite_false,ite_true,add_zero,zero_add,ih] <;>
      omega

/-- The number of phrase-domain D calls equals the number of base Omega calls. -/
theorem wallet_count (shape : E → Hash → Phrase) (g : E → Hash)
    (queries : List (Point Password E ⊕ E)) :
    (queries.flatMap (point shape g)).countP isWallet=queries.countP isWallet := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
    cases query <;> simp only [List.flatMap_cons,List.countP_append,List.countP_cons,List.countP_nil,
      point,isWallet,Bool.false_eq_true,ite_false,ite_true,add_zero,zero_add,ih,Nat.add_comm]

/-- All five exact counter identities hold for the actual adaptive query execution. -/
theorem counts (shape : E → Hash → Phrase) (tables : Tables Password E) (d : Phrase → Data)
    (program : OracleComp (baseSpec Password E Data) Result) :
    let source := (TranscriptErasure.execute
      (combinedAnswer (G10Model.walletSpec E Data) tables (fun e => d (shape e (tables.g e)))) program).2
    let actual := (TranscriptErasure.execute
      (combinedAnswer (G10Model.walletSpec Phrase Data) tables d) (realize shape program)).2
    actual.countP (crypto QueryCounts.isA)=source.countP (crypto QueryCounts.isA) ∧
      actual.countP (crypto QueryCounts.isB)=source.countP (crypto QueryCounts.isB) ∧
      actual.countP (crypto QueryCounts.isH)=source.countP (crypto QueryCounts.isH) ∧
      actual.countP (crypto InverseCounts.isG)=source.countP (crypto InverseCounts.isG)+source.countP isWallet ∧
      actual.countP isWallet=source.countP isWallet := by
  rw [G10DerivedCompiler.execution]
  exact ⟨crypto_count _ _ _ _ (by intro e; rfl),crypto_count _ _ _ _ (by intro e; rfl),
    crypto_count _ _ _ _ (by intro e; rfl),g_count _ _ _,wallet_count _ _ _⟩

end G10DerivedCounts

/-! A concrete12-Argon2-per-candidate matching strategy for checksum-aware phrase-domain D. -/
namespace G10DerivedMatching
open Gamma2Model WalletCryptoCompiler G10WalletCounts
variable {N m : Nat} {E V R Phrase Data : Type} [DecidableEq E] [DecidableEq Phrase]
  [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype R] [Nonempty R] [Fintype Phrase] [Fintype Data] [Nonempty Data] [DecidableEq Data]
attribute [local instance] FiniteBits.fintype

def attack (shape : E → Hash → Phrase) (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (m : Nat) (positive : 0 < N) : G10DirectModel.Adversary N E Phrase Data :=
  G10DerivedModel.adversary shape (G10Matching.attack coordinates hash m positive)

/-- The original direct-D source game inherits the same joint false-match loss from the exact realized-program identity. -/
theorem bound (shape : E → Hash → Phrase) (decode : Phrase → E)
    (decodes : ∀ e h,decode (shape e h)=e) (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top passwords (m+1)*
      (1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data)) ≤
      (G10DirectModel.original (Data := Data) coordinates hash (fun g e => shape e (g e)) passwords
        (attack shape coordinates hash m positive)) true := by
  unfold attack
  rw [G10DerivedModel.original coordinates hash shape decode decodes]
  exact G10Matching.bound coordinates hash firstHalf projects passwords m positive

/-- Every injective candidate order has the corresponding more precise rank-weighted bound. -/
theorem weighted (shape : E → Hash → Phrase) (decode : Phrase → E)
    (decodes : ∀ e h,decode (shape e h)=e) (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half)
    (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (order : Fin (m+1) → Fin N) (injective : Function.Injective order) :
    (∑ rank : Fin (m+1),passwords (order rank)*
      (1-(rank.val:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))) ≤
      (G10DirectModel.original (Data := Data) coordinates hash (fun g e => shape e (g e)) passwords
        (G10DerivedModel.adversary shape
          (G10WalletAttack.attack coordinates hash (RankedCandidates.tested order)
            (RankedCandidates.fallback order)))) true := by
  rw [G10DerivedModel.original coordinates hash shape decode decodes]
  exact G10Matching.weighted coordinates hash firstHalf projects passwords order injective

omit [DecidableEq E] [DecidableEq Phrase] [Fintype E] [Nonempty E] [Fintype V] [Nonempty V]
  [Fintype R] [Nonempty R] [Fintype Phrase] [Fintype Data] [Nonempty Data] in
/-- Real checksum reads are paid: A≤12m,B≤11m+1,H≤12m,G≤2m,D≤m, even on inconsistent public data. -/
theorem budgets (shape : E → Hash → Phrase) (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (m : Nat) (positive : 0 < N) (tables : Tables (Fin N) E) (d : Phrase → Data) (container : State) (data : Data) :
    let queries := (TranscriptErasure.execute
      (combinedAnswer (G10Model.walletSpec Phrase Data) tables d)
      (attack shape coordinates hash m positive container data)).2
    queries.countP (crypto QueryCounts.isA) ≤ 12*m ∧
      queries.countP (crypto QueryCounts.isB) ≤ 11*m+1 ∧
      queries.countP (crypto QueryCounts.isH) ≤ 12*m ∧
      queries.countP (crypto InverseCounts.isG) ≤ 2*m ∧ queries.countP isWallet ≤ m := by
  let program := G10Matching.attack coordinates hash m positive container data
  have identities := G10DerivedCounts.counts shape tables d program
  have source := G10Matching.budgets coordinates hash m positive tables
    (fun e => d (shape e (tables.g e))) container data
  dsimp only [program] at identities
  dsimp only [attack,G10DerivedModel.adversary]
  rw [identities.1,identities.2.1,identities.2.2.1,identities.2.2.2.1,identities.2.2.2.2]
  exact ⟨source.1,source.2.1,source.2.2.1,by omega,source.2.2.2.2⟩

end G10DerivedMatching

/-! The direct-D matching construction at actual checksum and entropy bit coordinates. -/
namespace G10DerivedChecksum
open Gamma2Model
variable {N : Nat} {E : Type}
attribute [local instance] FiniteBits.fintype

/-- Adapt the existing checksum encoder to the digest returned by a real G call. -/
def shape (checksum : Nat) (e : E) (digest : Hash) : G10Phrase.Phrase E checksum :=
  G10Phrase.encode checksum (fun _ => digest) e

theorem decodes (checksum : Nat) (e : E) (digest : Hash) :
    G10Phrase.decode checksum (shape checksum e digest)=e := rfl

/-- The actual source success has the same2^-(r+lambda) false-match term, including ENT256. -/
theorem bound (tail verifier suffix checksum width : Nat) (state_length : tail+verifier=128)
    (hash_length : verifier+suffix=256) (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N) :
    RankedMass.top passwords (m+1)*
      (1-(m:ENNReal)*(1/(2^(verifier+width):ENNReal)+1/(2^128:ENNReal)+(12:ENNReal)/(2^256:ENNReal))) ≤
      (G10DirectModel.original (Data := BitVec width)
        (ShortSourceCoordinates.state tail verifier state_length)
        (BitPacking.hash verifier suffix hash_length) (G10Phrase.encode checksum) passwords
        (G10DerivedMatching.attack (shape checksum)
          (ShortSourceCoordinates.state tail verifier state_length)
          (BitPacking.hash verifier suffix hash_length) m positive)) true := by
  have result := G10DerivedMatching.bound (Data := BitVec width) (shape checksum)
    (G10Phrase.decode checksum) (decodes checksum)
    (ShortSourceCoordinates.state tail verifier state_length)
    (BitPacking.hash verifier suffix hash_length) (ShortSourceCoordinates.firstHalf tail)
    (ShortSourceCoordinates.projects tail verifier state_length) passwords m positive
  (try simp only [shape,G10Phrase.encode,G10MatchingBits.delta] at result ⊢)
  exact result

end G10DerivedChecksum

/-! First-refusal loss for the actual checksum-aware direct-D matching strategy. -/
namespace G10DerivedMatchingRefusal
open Gamma2Model
variable {N : Nat} {E V R Phrase Data : Type} [DecidableEq E] [DecidableEq Phrase]
  [Fintype E] [Nonempty E] [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype R] [Nonempty R] [Fintype Phrase] [Fintype Data] [Nonempty Data] [DecidableEq Data]
attribute [local instance] FiniteBits.fintype

theorem bound (shape : E → Hash → Phrase) (decode : Phrase → E) (decodes : ∀ e h,decode (shape e h)=e)
    (coordinates : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy coordinates input)=input.1)
    (passwords : PMF (Fin N)) (m : Nat) (positive : 0 < N)
    (later : G10DirectEnvironment.Context (N := N) (E := E) (Phrase := Phrase) (Data := Data)
      × TableFactors.HTable → PMF Bool) :
    RankedMass.top passwords (m+1)*
      (1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))-(2^256:ENNReal)⁻¹ ≤
      (G10DirectRefusal.game coordinates hash (fun g e => shape e (g e)) passwords
        (G10DerivedMatching.attack shape coordinates hash m positive) later) true := by
  let attack := G10DerivedMatching.attack (Data := Data) shape coordinates hash m positive
  let lower := RankedMass.top passwords (m+1)*
    (1-(m:ENNReal)*G10FirstPass.delta (V := V) (Data := Data))
  have source : lower ≤ (G10DirectModel.original coordinates hash
      (fun g e => shape e (g e)) passwords attack) true :=
    G10DerivedMatching.bound shape decode decodes coordinates hash firstHalf projects passwords m positive
  rw [G10DirectEnvironment.original] at source
  have result := RefusalResponseLower.bound (G10DirectEnvironment.initial passwords)
    (G10DirectRefusal.refused coordinates hash)
    (G10DirectEnvironment.score coordinates hash (fun g e => shape e (g e)) attack) later lower source
  rw [G10DirectRefusal.probability] at result
  exact result

end G10DerivedMatchingRefusal

end
end MhfeLean
