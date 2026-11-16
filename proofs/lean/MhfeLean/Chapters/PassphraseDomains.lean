/- long: finite query windows and their native-source limit form one transport proof. -/
-- long: Finite observable query alphabets and the finite-window passphrase reduction belong to one domain-transport argument.
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # Arbitrary passphrase priors through finite observable windows

A fixed adaptive query program with finite answer types has finitely many possible
query labels and output values, even if its query alphabet is infinite. The finite
window reduction must retain the true source row in addition to the queried rows.
No discrete uniform distribution on an infinite full function space is assumed.
-/

namespace FiniteOracleViews
-- Port to Lean 4.35: VCVio removed the `OracleSpec.Fintype` class; finite answer types are now
-- an ordinary hypothesis quantified over the queries.
variable {Domain Result : Type} {spec : OracleSpec Domain} [∀ t, Fintype (spec.Range t)] [DecidableEq Domain]

variable [DecidableEq Result]

/-- Finite outputs follow from finite branching; the result type itself need not be finite. -/
-- Deliberate copy of VCVio's finite-support fold: importing EvalDist would also
-- bring its unused probabilistic simulation stack into this deterministic transcript bridge.
def results (program : OracleComp spec Result) : Finset Result :=
  OracleComp.construct (fun result => {result}) (fun _ _ rest => Finset.univ.biUnion rest) program

omit [DecidableEq Domain] in
theorem result_mem (table : (point : Domain) → spec point) (program : OracleComp spec Result) :
    (TranscriptErasure.execute table program).1 ∈ results program := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [TranscriptErasure.execute_pure,results,OracleComp.construct_pure,Finset.mem_singleton]
  | query_bind point next ih =>
    change (TranscriptErasure.execute table (TranscriptErasure.ask point >>= next)).1 ∈
      results (TranscriptErasure.ask point >>= next)
    simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_ask,
      results]
    exact Finset.mem_biUnion.mpr ⟨table point,Finset.mem_univ _,ih (table point)⟩

end FiniteOracleViews

namespace PassphraseWindow
variable {Passphrase : Type} [DecidableEq Passphrase]

abbrev Category (window : Finset Passphrase) := Option {phrase // phrase ∈ window}

/-- The one Other category is never a queried or emitted passphrase of the covered program. -/
def encode (window : Finset Passphrase) (phrase : Passphrase) : Category window :=
  if member : phrase ∈ window then some ⟨phrase,member⟩ else none

variable (window : Finset Passphrase) (phrases : PMF Passphrase)

/-- Outside mass is retained, rather than conditioning it away or renormalizing the prior. -/
def prior : PMF (Category window) :=
  phrases.map (encode window)

def tail : ENNReal :=
  ∑' phrase, if phrase ∈ window then 0 else phrases phrase

theorem encode_some (window : Finset Passphrase) (chosen : {phrase // phrase ∈ window})
    (phrase : Passphrase) : some chosen=encode window phrase ↔ phrase=chosen.val := by
  unfold encode
  by_cases member : phrase ∈ window
  · simp only [dif_pos member,Option.some.injEq,Subtype.ext_iff,eq_comm]
  · simp only [dif_neg member,Option.some_ne_none,false_iff]
    intro same
    exact member (same.symm ▸ chosen.2)

/-- Every retained point keeps exactly its original probability. -/
theorem some_mass (chosen : {phrase // phrase ∈ window}) :
    prior window phrases (some chosen)=phrases chosen.val := by
  rw [prior,PMF.map_apply]
  simp_rw [encode_some]
  exact tsum_ite_eq chosen.val phrases

/-- No outside probability is lost: its full mass is assigned to Other. -/
theorem none_mass : prior window phrases none=tail window phrases := by
  rw [prior,PMF.map_apply]
  apply tsum_congr
  intro phrase
  by_cases member : phrase ∈ window <;> simp [encode,member]

/-- A sufficiently large finite window preserves a global largest-point bound. -/
theorem largest (s1 : ENNReal) (points : ∀ phrase,phrases phrase ≤ s1)
    (outside : tail window phrases ≤ s1) : ∀ category,prior window phrases category ≤ s1 := by
  intro category
  cases category with
  | none => simpa only [none_mass] using outside
  | some phrase => simpa only [some_mass] using points phrase.val

/-- This is the ordinary probability tail over the complement, expressed without a conditional prior. -/
theorem tail_complement :
    tail window phrases=∑' phrase : {phrase // phrase ∉ window}, phrases phrase.val := by
  symm
  calc
    _ = ∑' phrase, ({phrase | phrase ∉ window} : Set Passphrase).indicator (fun phrase => phrases phrase) phrase :=
      tsum_subtype ({phrase | phrase ∉ window} : Set Passphrase) (fun phrase => phrases phrase)
    _ = tail window phrases := by
      unfold tail
      apply tsum_congr
      intro phrase
      by_cases member : phrase ∈ window <;> simp [Set.indicator,member]

/-- Every probability prior has arbitrarily small finite tails, even on an infinite alphabet. -/
theorem finite_window (base : Finset Passphrase) (phrases : PMF Passphrase) (epsilon : ENNReal)
    (positive : 0<epsilon) :
    ∃ window : Finset Passphrase, base ⊆ window ∧ tail window phrases ≤ epsilon := by
  have converges := ENNReal.tendsto_tsum_compl_atTop_zero phrases.tsum_coe_ne_top
  have eventually := converges.eventually_lt_const positive
  obtain ⟨window,bound⟩ := Filter.eventually_atTop.mp eventually
  refine ⟨base∪window,Finset.subset_union_left,?_⟩
  rw [tail_complement]
  exact (bound (base∪window) Finset.subset_union_right).le

/-- Larger hidden windows can only reduce the unobserved prior mass. -/
theorem tail_antitone (phrases : PMF Passphrase) :
    Antitone (fun window : Finset Passphrase => tail window phrases) := by
  intro smaller larger contained
  refine ENNReal.tsum_le_tsum fun phrase => ?_
  by_cases inLarger : phrase ∈ larger
  · simp [inLarger]
  · simp [inLarger, show phrase ∉ smaller from fun inSmaller => inLarger (contained inSmaller)]

variable {N : Nat}

/-- Retained products use only actual passphrases in the finite window. -/
def retained (window : Finset Passphrase) (pairs : Finset (Fin N × Category window)) :
    Finset (Fin N × {phrase // phrase ∈ window}) :=
  Finset.univ.filter (fun pair => (pair.1,some pair.2) ∈ pairs)

def originalPairs (window : Finset Passphrase) (pairs : Finset (Fin N × Category window)) :
    Finset (Fin N × Passphrase) :=
  (retained window pairs).image (fun pair => (pair.1,pair.2.val))

omit [DecidableEq Passphrase] in
private theorem some_injective (window : Finset Passphrase) :
    Function.Injective (fun pair : Fin N × {phrase // phrase ∈ window} => (pair.1,some pair.2)) := by
  intro first second equal
  apply Prod.ext
  · exact congrArg (fun pair : Fin N × Category window => pair.1) equal
  · exact Option.some.inj (congrArg (fun pair : Fin N × Category window => pair.2) equal)

omit [DecidableEq Passphrase] in
private theorem original_injective (window : Finset Passphrase) :
    Function.Injective (fun pair : Fin N × {phrase // phrase ∈ window} => (pair.1,pair.2.val)) := by
  intro first second equal
  apply Prod.ext
  · exact congrArg (fun pair : Fin N × Passphrase => pair.1) equal
  · exact Subtype.ext (congrArg (fun pair : Fin N × Passphrase => pair.2) equal)

theorem original_card (window : Finset Passphrase) (pairs : Finset (Fin N × Category window)) :
    (originalPairs window pairs).card ≤ pairs.card := by
  rw [originalPairs,Finset.card_image_of_injective _ (original_injective window)]
  have contained : (retained window pairs).image (fun pair => (pair.1,some pair.2)) ⊆ pairs := by
    intro pair member
    obtain ⟨candidate,within,rfl⟩ := Finset.mem_image.mp member
    exact (Finset.mem_filter.mp within).2
  calc
    _ = ((retained window pairs).image (fun pair => (pair.1,some pair.2))).card :=
      (Finset.card_image_of_injective _ (some_injective window)).symm
    _ ≤ _ := Finset.card_le_card contained

/-- Split the mass into observable products and the possible overcount assigned to Other. -/
theorem mass_split (window : Finset Passphrase) (p : Fin N → ENNReal) (phrases : PMF Passphrase)
    (pairs : Finset (Fin N × Category window)) :
    W1.mass p (prior window phrases) pairs=
      (∑ password : Fin N, if (password,none) ∈ pairs then p password*tail window phrases else 0)+
      ∑ pair ∈ retained window pairs, p pair.1*phrases pair.2.val := by
  have all (f : Fin N × Category window → ENNReal) :
      (∑ pair ∈ pairs, f pair)=∑ password : Fin N,∑ category : Category window,
        if (password,category) ∈ pairs then f (password,category) else 0 := by
    calc
      _ = ∑ pair : Fin N × Category window, if pair ∈ pairs then f pair else 0 := by simp
      _ = _ := Fintype.sum_prod_type (fun pair : Fin N × Category window => if pair ∈ pairs then f pair else 0)
  unfold W1.mass
  rw [all]
  simp_rw [Fintype.sum_option,none_mass,some_mass]
  rw [Finset.sum_add_distrib]
  simp only [retained,Finset.sum_filter,Fintype.sum_prod_type]

/-- The remaining mass is exactly that of the injectively embedded original product set. -/
theorem retained_mass (window : Finset Passphrase) (p : Fin N → ENNReal) (phrases : PMF Passphrase)
    (pairs : Finset (Fin N × Category window)) :
    (∑ pair ∈ retained window pairs,p pair.1*phrases pair.2.val)=
      W1.mass p phrases (originalPairs window pairs) := by
  unfold W1.mass originalPairs
  rw [Finset.sum_image]
  intro first _ second _ equal
  exact original_injective window equal

/-- Even if Other were tested in every row, it can contribute no more than its full prior mass. -/
theorem other_mass (window : Finset Passphrase) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (pairs : Finset (Fin N × Category window)) :
    (∑ password : Fin N,if (password,none) ∈ pairs then passwords password*tail window phrases else 0) ≤
      tail window phrases := by
  calc
    _ ≤ ∑ password : Fin N,passwords password*tail window phrases := by
      apply Finset.sum_le_sum
      intro password _
      split_ifs
      · rfl
      · exact zero_le
    _ = (∑ password : Fin N,passwords password)*tail window phrases := (Finset.sum_mul _ _ _).symm
    _ = _ := by
      have total : (∑ password : Fin N,passwords password)=1 := by
        simpa only [tsum_fintype] using passwords.tsum_coe
      rw [total,one_mul]

/-- The finite category model's main term exceeds the original one by at most the vanishing tail mass. -/
theorem mass_le_top2 (window : Finset Passphrase) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (pairs : Finset (Fin N × Category window)) (m n : Nat)
    (count : pairs.card≤n) (rows : ∀ pair ∈ pairs,pair.1.val<m) :
    W1.mass passwords (prior window phrases) pairs ≤
      W1.top2 passwords phrases m n+tail window phrases := by
  have bound_count : (originalPairs window pairs).card ≤ n := (original_card window pairs).trans count
  have bound_rows : ∀ pair ∈ originalPairs window pairs,pair.1.val<m := by
    intro pair member
    obtain ⟨candidate,within,rfl⟩ := Finset.mem_image.mp member
    exact rows (candidate.1,some candidate.2) (Finset.mem_filter.mp within).2
  have tested : W1.mass passwords phrases (originalPairs window pairs) ≤
      W1.top2 passwords phrases m n :=
    le_iSup_of_le (originalPairs window pairs) (le_iSup_of_le bound_count (le_iSup_of_le bound_rows le_rfl))
  rw [mass_split,retained_mass]
  exact (add_le_add (other_mass window passwords phrases pairs) tested).trans (le_of_eq (add_comm _ _))

theorem top2_le (window : Finset Passphrase) (passwords : PMF (Fin N)) (phrases : PMF Passphrase)
    (m n : Nat) :
    W1.top2 passwords (prior window phrases) m n ≤
      W1.top2 passwords phrases m n+tail window phrases := by
  apply iSup_le
  intro pairs
  apply iSup_le
  intro count
  apply iSup_le
  intro rows
  exact mass_le_top2 window passwords phrases pairs m n count rows

variable (smaller larger : Finset Passphrase) (contained : smaller ⊆ larger)

/-- Retained labels embed without changing their value. -/
def baseEmbedding : Category smaller ↪ Category larger where
  toFun category := category.map (fun phrase => ⟨phrase.val,contained phrase.2⟩)
  inj' := by
    intro first second equal
    cases first with
    | none => cases second with
      | none => rfl
      | some value => cases equal
    | some value => cases second with
      | none => cases equal
      | some other =>
        simp only [Option.map_some,Option.some.injEq] at equal
        exact congrArg some (Subtype.ext (congrArg (fun phrase : {phrase // phrase ∈ larger} => phrase.val) equal))


/-- Port to Lean 4.35: `Function.Embedding.coeFn_mk` no longer matches this structure, whose
injectivity proof is stated in unfolded form; this is the same application law. -/
theorem baseEmbedding_apply (category : Category smaller) :
    baseEmbedding smaller larger contained category =
      category.map (fun phrase => ⟨phrase.val,contained phrase.2⟩) := rfl

/-- Couple the unobserved Other row to the true source row when it is newly present in the larger window. -/
def embedding (real : Passphrase) : Category smaller ↪ Category larger :=
  if real ∈ smaller then baseEmbedding smaller larger contained
  else (baseEmbedding smaller larger contained).trans (Equiv.swap none (encode larger real)).toEmbedding

/-- The challenge row is preserved whether or not the real passphrase was queried. -/
theorem embedding_target (real : Passphrase) :
    embedding smaller larger contained real (encode smaller real)=encode larger real := by
  by_cases member : real ∈ smaller
  · simp only [embedding,if_pos member,encode,dif_pos member,dif_pos (contained member),baseEmbedding_apply,Option.map_some]
  · simp only [embedding,if_neg member,encode,dif_neg member,Function.Embedding.trans_apply,
      baseEmbedding_apply,Option.map_none,Equiv.toEmbedding_apply,Equiv.swap_apply_left]

/-- Every query-window row stays itself; the challenge-dependent coupling is invisible to the program. -/
theorem embedding_mem (real phrase : Passphrase) (member : phrase ∈ smaller) :
    embedding smaller larger contained real (encode smaller phrase)=encode larger phrase := by
  by_cases known : real ∈ smaller
  · simp only [embedding,if_pos known,encode,dif_pos member,dif_pos (contained member),baseEmbedding_apply,Option.map_some]
  · have away : some (⟨phrase,contained member⟩ : {phrase // phrase ∈ larger}) ≠ encode larger real := by
      intro equal
      have same := (encode_some larger ⟨phrase,contained member⟩ real).mp equal
      exact known (same.symm ▸ member)
    simp only [embedding,if_neg known,encode,dif_pos member,dif_pos (contained member),
      Function.Embedding.trans_apply,baseEmbedding_apply,Option.map_some,Equiv.toEmbedding_apply]
    exact Equiv.swap_apply_of_ne_of_ne (by simp) away

/-- The entire required S table, not just individual answers, has the same law under row restriction. -/
theorem seed_table_law {Entropy Seed : Type} [Fintype Entropy] [DecidableEq Entropy] [Fintype Seed]
    [Nonempty Seed] (smaller larger : Finset Passphrase) (contained : smaller ⊆ larger)
    (real : Passphrase) :
    (PMF.uniformOfFintype (Entropy × Category larger → Seed)).map
      (fun table input => table (input.1,embedding smaller larger contained real input.2))=
      PMF.uniformOfFintype (Entropy × Category smaller → Seed) := by
  apply UniformInjection.restriction
  intro first second equal
  apply Prod.ext
  · exact congrArg (fun pair : Entropy × Category larger => pair.1) equal
  · exact (embedding smaller larger contained real).injective
      (congrArg (fun pair : Entropy × Category larger => pair.2) equal)

/-- The source view adds at most the single hidden row outside the public query window. -/
def sourceEmbedding (window : Finset Passphrase) (real : Passphrase) :
    {phrase // phrase ∈ insert real window} ↪ Category window where
  toFun phrase := encode window phrase.val
  inj' := by
    intro first second equal
    dsimp only at equal
    apply Subtype.ext
    by_cases knownFirst : first.val ∈ window
    · have firstEncoded : encode window first.val=some ⟨first.val,knownFirst⟩ := dif_pos knownFirst
      rw [firstEncoded] at equal
      exact ((encode_some window ⟨first.val,knownFirst⟩ second.val).mp equal).symm
    · by_cases knownSecond : second.val ∈ window
      · have absent : encode window first.val=none := dif_neg knownFirst
        have present : encode window second.val=some ⟨second.val,knownSecond⟩ := dif_pos knownSecond
        rw [absent,present] at equal
        cases equal
      · have firstReal : first.val=real := (Finset.mem_insert.mp first.2).resolve_right knownFirst
        have secondReal : second.val=real := (Finset.mem_insert.mp second.2).resolve_right knownSecond
        exact firstReal.trans secondReal.symm

end PassphraseWindow

namespace PassphraseRecoding
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Native Small Seed Check Tail Data Result : Type}

abbrev FullSpec (Phrase : Type) := combinedSpec (Password := Password) (Entropy := Entropy)
  (SeedWalletModel.spec Entropy Phrase Seed Check Tail Data)

local notation "AttackSpec" => FullSpec (Password := Password) (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)

/-- Every answer type is finite even when passphrase labels are not. -/
instance answers [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
    (input : Gamma2Model.Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed) :
    Fintype ((AttackSpec Native).Range input) := by
  letI := FiniteBits.fintype
  cases input with
  | inl input => cases input <;> dsimp only [OracleSpec.Range,FullSpec,combinedSpec,Gamma2Model.spec] <;> infer_instance
  | inr input => cases input <;> dsimp only [OracleSpec.Range,FullSpec,combinedSpec,SeedWalletModel.spec] <;> infer_instance

abbrev Wallet (Phrase : Type) := SeedWalletModel.Tables Entropy Phrase Seed Check Tail Data

/-- Unobserved labels may be merged; only explicit row restrictions will be used as probability laws. -/
def pull (labels : Native → Small) (wallet : Wallet (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) Small) :
    Wallet (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) Native :=
  ⟨fun input => wallet.s (input.1,labels input.2),wallet.t,wallet.omega⟩

def point (labels : Native → Small) :
    Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed →
    Point Password Entropy ⊕ SeedWalletModel.Point Entropy Small Seed
  | .inl input => .inl input
  | .inr (.s e q) => .inr (.s e (labels q))
  | .inr (.t seed) => .inr (.t seed)
  | .inr (.omega seed) => .inr (.omega seed)

/-- The compiler sees query labels and oracle answers, never the true secrets or sampled functions. -/
def query (labels : Native → Small) :
    (input : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed) →
    OracleComp (AttackSpec Small)
      (AttackSpec Native input)
  | .inl (.a p salt) => TranscriptErasure.ask (spec := AttackSpec Small) (.inl (.a p salt))
  | .inl (.b i right) => TranscriptErasure.ask (spec := AttackSpec Small) (.inl (.b i right))
  | .inl (.h key i right) => TranscriptErasure.ask (spec := AttackSpec Small) (.inl (.h key i right))
  | .inl (.g e) => TranscriptErasure.ask (spec := AttackSpec Small) (.inl (.g e))
  | .inr (.s e q) => TranscriptErasure.ask (spec := AttackSpec Small) (.inr (.s e (labels q)))
  | .inr (.t seed) => TranscriptErasure.ask (spec := AttackSpec Small) (.inr (.t seed))
  | .inr (.omega seed) => TranscriptErasure.ask (spec := AttackSpec Small) (.inr (.omega seed))

def program (labels : Native → Small)
    (adversary : OracleComp (AttackSpec Native) Result) :
    OracleComp (AttackSpec Small) Result :=
  OracleComp.construct pure (fun input _ recurse => query labels input >>= recurse) adversary

theorem query_execution (labels : Native → Small) (crypto : Tables Password Entropy)
    (wallet : Wallet (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) Small)
    (input : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed) :
    TranscriptErasure.execute
      (combinedAnswer (SeedWalletModel.spec Entropy Small Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (query labels input)=
      (combinedAnswer (SeedWalletModel.spec Entropy Native Seed Check Tail Data) crypto
        (SeedWalletModel.answer (pull labels wallet)) input,[point labels input]) := by
  cases input with
  | inl input => cases input <;> simp only [query,TranscriptErasure.execute_ask,combinedAnswer,point]
  | inr input => cases input <;> simp only [query,TranscriptErasure.execute_ask,combinedAnswer,SeedWalletModel.answer,pull,point]

/-- Actual output and complete query order, including repeats, are transported exactly. -/
theorem execution (labels : Native → Small) (crypto : Tables Password Entropy)
    (wallet : Wallet (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) Small)
    (adversary : OracleComp (AttackSpec Native) Result) :
    TranscriptErasure.execute
      (combinedAnswer (SeedWalletModel.spec Entropy Small Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (program labels adversary)=
      let actual := TranscriptErasure.execute
        (combinedAnswer (SeedWalletModel.spec Entropy Native Seed Check Tail Data) crypto
          (SeedWalletModel.answer (pull labels wallet))) adversary
      (actual.1,actual.2.map (point labels)) := by
  induction adversary using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind input next ih =>
    change TranscriptErasure.execute _ (query labels input >>= fun answer => program labels (next answer))=
      ((TranscriptErasure.execute _ (TranscriptErasure.ask input >>= next)).1,
        (TranscriptErasure.execute _ (TranscriptErasure.ask input >>= next)).2.map (point labels))
    simp only [TranscriptErasure.execute_bind,query_execution,ih,
      TranscriptErasure.execute_ask,List.singleton_append,List.map_cons]

end PassphraseRecoding

namespace PassphraseRows
open WalletGeneration WalletFinite TranscriptErasure ProbabilityTools
variable {Entropy Small Large Seed Check Tail : Type}

def restrict (labels : Small → Large)
    (table : Table (spec Entropy Large Seed Check Tail)) : Table (spec Entropy Small Seed Check Tail)
  | .s e q => table (.s e (labels q))
  | .t seed => table (.t seed)

variable [DecidableEq Entropy] [DecidableEq Small] [DecidableEq Large] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Small] [Fintype Large] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Seed] [Nonempty Check] [Nonempty Tail]

/-- Restriction preserves the whole joint S/T function law, with T shared across every row. -/
theorem sampling (labels : Small ↪ Large) :
    (PMF.uniformOfFintype (Table (spec Entropy Large Seed Check Tail))).map (restrict labels)=
      PMF.uniformOfFintype (Table (spec Entropy Small Seed Check Tail)) := by
  have seedLaw : (PMF.uniformOfFintype (Entropy × Large → Seed)).map
      (fun table => fun input : Entropy × Small => table (input.1,labels input.2))=
      PMF.uniformOfFintype (Entropy × Small → Seed) := by
    apply UniformInjection.restriction
    intro first second equal
    apply Prod.ext
    · exact congrArg (fun pair : Entropy × Large => pair.1) equal
    · exact labels.injective (congrArg (fun pair : Entropy × Large => pair.2) equal)
  rw [WalletTableFactors.sampling,WalletTableFactors.sampling,
    uniform_product,uniform_product]
  simp only [independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def]
  have transported := congrArg (fun distribution : PMF (Entropy × Small → Seed) => distribution.bind
    (fun s => (PMF.uniformOfFintype (Seed → Check × Tail)).map
      (fun t => WalletTableFactors.split.symm (s,t)))) seedLaw
  (try simp only [PMF.bind_map] at transported ⊢)
  exact transported

variable [Nonempty Entropy] [DecidableEq Check]

omit [DecidableEq Entropy] [DecidableEq Small] [DecidableEq Large] [DecidableEq Seed]
  [Fintype Small] [Fintype Large] [Fintype Check] [Nonempty Check] in
/-- Fixed-function passing sets, selected entropy, seed and suffix agree exactly; so do empty-set fallbacks. -/
theorem real (labels : Small → Large) (table : Table (spec Entropy Large Seed Check Tail))
    (phrase : Small) (target : Check) :
    WalletCompletion.real (restrict labels table) phrase target=
      WalletCompletion.real table (labels phrase) target := rfl

end PassphraseRows

namespace PassphraseRecoding
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Native Small Seed Check Tail Data Result : Type}

/-- Relabeling S leaves the complete crypto-only subsequence unchanged. -/
theorem crypto_log (labels : Native → Small)
    (queries : List (Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed)) :
    W4TraceProjection.crypto (queries.map (point labels))=W4TraceProjection.crypto queries := by
  induction queries with
  | nil => rfl
  | cons input rest ih => cases input with
    | inl input => simpa only [List.map_cons,point,W4TraceProjection.crypto] using congrArg (List.cons input) ih
    | inr input => cases input <;> simpa only [List.map_cons,point,W4TraceProjection.crypto] using ih

/-- Seed calls retain their multiplicity; label merging never gives the attacker free calls. -/
theorem seed_length (labels : Native → Small)
    (queries : List (Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed)) :
    (SeedWalletModel.seedPairs (queries.map (point labels))).length=
      (SeedWalletModel.seedPairs queries).length := by
  induction queries with
  | nil => rfl
  | cons input rest ih =>
    cases input with
    | inl input => simpa [List.map_cons,point,SeedWalletModel.seedPairs,SeedQueryMetadata.extract,
        List.filterMap_cons] using ih
    | inr input => cases input <;> simp [List.map_cons,point,SeedWalletModel.seedPairs,
        SeedQueryMetadata.extract,SeedWalletModel.seedPair,List.filterMap_cons] at ih ⊢ <;> exact ih

/-- T and Omega are separate counters, both preserved without deduplication. -/
theorem tags (labels : Native → Small)
    (input : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed) :
    SeedWalletModel.isT (point labels input)=SeedWalletModel.isT input ∧
    SeedWalletModel.isOmega (point labels input)=SeedWalletModel.isOmega input := by
  cases input with
  | inl input => exact ⟨rfl,rfl⟩
  | inr input => cases input <;> exact ⟨rfl,rfl⟩

/-- Freezing wallet functions commutes with the recoder for both output and actual crypto calls. -/
theorem crypto_execution (labels : Native → Small) (crypto : Tables Password Entropy)
    (wallet : Wallet (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) Small)
    (adversary : OracleComp (FullSpec (Password := Password) (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) Native) Result) :
    execute crypto (compile (SeedWalletModel.spec Entropy Small Seed Check Tail Data)
      (SeedWalletModel.answer wallet) (program labels adversary))=
    execute crypto (compile (SeedWalletModel.spec Entropy Native Seed Check Tail Data)
      (SeedWalletModel.answer (pull labels wallet)) adversary) := by
  rw [WalletCryptoCompiler.execution,WalletCryptoCompiler.execution,execution]
  simp only [crypto_log]

variable {N : Nat} [DecidableEq Entropy] [DecidableEq Native] [DecidableEq Small] [DecidableEq Seed]

omit [DecidableEq Entropy] [DecidableEq Native] [DecidableEq Small] [DecidableEq Seed] in
/-- All six existing hard budgets follow from the original program's budgets for arbitrary tables. -/
theorem budgets (labels : Native → Small)
    (adversary : FullRawBound.FullProgram (N := N) (Entropy := Entropy) (Passphrase := Native)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (kA kS qB qH qT qOmega : Nat)
    (budget : FullRawBound.Budgets adversary kA kS qB qH qT qOmega) :
    FullRawBound.Budgets (fun data state => program labels (adversary data state)) kA kS qB qH qT qOmega := by
  constructor
  · intro wallet data state crypto
    simpa only [SeedQueryRun.compiled,crypto_execution] using budget.a (pull labels wallet) data state crypto
  · intro wallet data state crypto
    simpa only [SeedQueryRun.compiled,crypto_execution] using budget.b (pull labels wallet) data state crypto
  · intro wallet data state crypto
    simpa only [SeedQueryRun.compiled,crypto_execution] using budget.h (pull labels wallet) data state crypto
  · intro wallet data input
    simpa only [SeedQueryRun.pairs,SeedQueryRun.full,execution,seed_length] using budget.s (pull labels wallet) data input
  · intro wallet data input
    simpa only [SeedQueryRun.full,execution,List.countP_map,Function.comp_def,(tags labels _).1]
      using budget.t (pull labels wallet) data input
  · intro wallet data input
    simpa only [SeedQueryRun.full,execution,List.countP_map,Function.comp_def,(tags labels _).2]
      using budget.omega (pull labels wallet) data input

end PassphraseRecoding

namespace PassphraseSource
open Gamma2Model WalletCryptoCompiler PassphraseWindow
variable {Password Entropy Native Seed Check Tail Data Result : Type}
  [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Native] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

abbrev Adversary := Data → State → OracleComp (PassphraseRecoding.FullSpec
  (Password := Password) (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) Native) Result
abbrev ST (window : Finset Native) := TranscriptErasure.Table
  (WalletGeneration.spec Entropy (Category window) Seed Check Tail)

local notation "WalletAdversary" => Adversary (Password := Password) (Entropy := Entropy) (Native := Native) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)

/-- A syntactic support condition is independent of the secrets and all sampled functions. -/
def Supported (window : Finset Native) (adversary : WalletAdversary) : Prop :=
  ∀ data state e q, Sum.inr (SeedWalletModel.Point.s e q) ∈
    FiniteQuerySpace.space (adversary data state) → q ∈ window

/-- All S labels on every possible public-input and oracle-answer branch. -/
def queryWindow (adversary : WalletAdversary) : Finset Native :=
  Finset.univ.biUnion fun input : Data × State =>
    (FiniteQuerySpace.space (adversary input.1 input.2)).biUnion fun point =>
      match point with | .inr (.s _ q) => {q} | _ => ∅

omit [DecidableEq Check] [Fintype Entropy] [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
theorem queryWindow_supported (adversary : WalletAdversary) :
    Supported (queryWindow adversary) adversary := by
  intro data state e q member
  exact Finset.mem_biUnion.mpr ⟨(data,state),Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨Sum.inr (.s e q),member,Finset.mem_singleton_self _⟩⟩

omit [DecidableEq Check] [Fintype Entropy] [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
/-- A larger window remains sufficient without examining the actual execution. -/
theorem supported_mono (adversary : WalletAdversary)
    (smaller larger : Finset Native) (included : smaller ⊆ larger) (supported : Supported smaller adversary) :
    Supported larger adversary := fun data state e q member => included (supported data state e q member)

/-- The joint observable source law retains the selected triple and the real adversary's output. -/
def conditional (window : Finset Native) (real : Native) (coordinates : Entropy ≃ State)
    (password : Password) (crypto : Tables Password Entropy) (target : Check)
    (adversary : WalletAdversary) :
    PMF (WalletGeneration.Selected Entropy Seed Tail × Result) :=
  (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
    (PMF.uniformOfFintype (ST (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)).bind fun table =>
      (WalletCompletion.real table (encode window real) target).map fun chosen =>
        (chosen,(TranscriptErasure.execute
          (combinedAnswer (SeedWalletModel.spec Entropy (Category window) Seed Check Tail Data) crypto
            (SeedWalletModel.answer (WalletGenerationCompiler.wallet table omega)))
          (PassphraseRecoding.program (encode window)
            (adversary (omega chosen.seed)
              (coordinates (FullSourceCoordinates.cipher coordinates password crypto chosen.entropy))))).1)

omit [DecidableEq Password] in
/-- This is the existing actual source sampler, after discarding its internal query logs. -/
theorem finite_law (window : Finset Native) (real : Native) (coordinates : Entropy ≃ State)
    (password : Password) (crypto : Tables Password Entropy) (target : Check)
    (adversary : WalletAdversary) (test : Seed → Result → Bool) :
    (conditional window real coordinates password crypto target adversary).map (fun view => test view.1.seed view.2)=
    FullGenerationResampling.actual coordinates password crypto (encode window real) target
      (fun data state => PassphraseRecoding.program (encode window) (adversary data state)) test := by
  simp only [conditional,FullGenerationResampling.actual,WalletUnbounded.real,
    PMF.map_bind,PMF.map_comp,Function.comp_def,FullGenerationCoupling.program,
    WalletGenerationCompiler.execution]

omit [DecidableEq Check] [Fintype Entropy] [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
/-- Newly sampled hidden rows cannot change any native query the program can make. -/
theorem result_between (smaller larger : Finset Native) (contained : smaller ⊆ larger) (real : Native)
    (supported : Supported smaller (Password := Password) (Entropy := Entropy) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result) adversary)
    (crypto : Tables Password Entropy) (omega : Seed → Data)
    (table : ST (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) larger)
    (data : Data) (state : State) :
    (TranscriptErasure.execute
      (combinedAnswer (SeedWalletModel.spec Entropy (Category smaller) Seed Check Tail Data) crypto
        (SeedWalletModel.answer (WalletGenerationCompiler.wallet
          (PassphraseRows.restrict (embedding smaller larger contained real) table) omega)))
      (PassphraseRecoding.program (encode smaller) (adversary data state))).1=
    (TranscriptErasure.execute
      (combinedAnswer (SeedWalletModel.spec Entropy (Category larger) Seed Check Tail Data) crypto
        (SeedWalletModel.answer (WalletGenerationCompiler.wallet table omega)))
      (PassphraseRecoding.program (encode larger) (adversary data state))).1 := by
  rw [PassphraseRecoding.execution,PassphraseRecoding.execution]
  dsimp only
  apply congrArg (fun run : Result × List (Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed) => run.1)
  apply TranscriptErasure.execute_agree
  intro input member
  cases input with
  | inl input => rfl
  | inr input =>
    cases input with
    | s e q =>
      have inside := supported data state e q (FiniteQuerySpace.coverage _ _ _ member)
      change table (.s e (embedding smaller larger contained real (encode smaller q)))=table (.s e (encode larger q))
      rw [embedding_mem smaller larger contained real q inside]
    | t seed => rfl
    | omega seed => rfl

/-- The whole selected-output law is consistent under enlarging the hidden finite view. -/
theorem conditional_between (smaller larger : Finset Native) (contained : smaller ⊆ larger) (real : Native)
    (coordinates : Entropy ≃ State) (password : Password) (crypto : Tables Password Entropy) (target : Check)
    (adversary : WalletAdversary)
    (supported : Supported smaller adversary) :
    conditional smaller real coordinates password crypto target adversary=
      conditional larger real coordinates password crypto target adversary := by
  unfold conditional
  congr 1
  funext omega
  rw [← PassphraseRows.sampling (embedding smaller larger contained real),PMF.bind_map]
  congr 1
  funext table
  dsimp only [Function.comp_def]
  rw [PassphraseRows.real,embedding_target]
  congr 1
  funext chosen
  refine Prod.ext (by rfl) ?_
  exact result_between smaller larger contained real supported crypto omega table _ _

/-- Native finite-cylinder generation uses the existing WalletAt sampler, with the one true row retained. -/
def native (window : Finset Native) (real : Native) (coordinates : Entropy ≃ State)
    (password : Password) (crypto : Tables Password Entropy) (target : Check)
    (adversary : WalletAdversary) :
    PMF (WalletGeneration.Selected Entropy Seed Tail × Result) :=
  (PMF.uniformOfFintype (Seed → Data)).bind fun omega =>
    (WalletAt.actual (insert real window) ⟨real,Finset.mem_insert_self _ _⟩ target
      (FullGenerationCoupling.program crypto omega
        (fun e => coordinates (FullSourceCoordinates.cipher coordinates password crypto e)) adversary)).map
      (fun view => (view.1,view.2.1.1))

omit [DecidableEq Check] [Fintype Entropy] [Nonempty Entropy] [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
/-- Category execution preserves the native program, not just a success-probability expression. -/
theorem native_result (window : Finset Native) (real : Native)
    (adversary : WalletAdversary)
    (supported : Supported window adversary) (crypto : Tables Password Entropy) (omega : Seed → Data)
    (table : ST (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)
    (data : Data) (state : State) :
    (TranscriptErasure.execute
      (combinedAnswer (SeedWalletModel.spec Entropy Native Seed Check Tail Data) crypto
        (SeedWalletModel.answer (WalletGenerationCompiler.wallet
          (WalletWindowBudgets.extendTable (insert real window)
            (PassphraseRows.restrict (sourceEmbedding window real) table)) omega)))
      (adversary data state)).1=
    (TranscriptErasure.execute
      (combinedAnswer (SeedWalletModel.spec Entropy (Category window) Seed Check Tail Data) crypto
        (SeedWalletModel.answer (WalletGenerationCompiler.wallet table omega)))
      (PassphraseRecoding.program (encode window) (adversary data state))).1 := by
  rw [PassphraseRecoding.execution]
  dsimp only
  apply congrArg (fun run : Result × List (Point Password Entropy ⊕ SeedWalletModel.Point Entropy Native Seed) => run.1)
  apply TranscriptErasure.execute_agree
  intro input member
  cases input with
  | inl input => rfl
  | inr input => cases input with
    | s e q =>
      have inside := supported data state e q (FiniteQuerySpace.coverage _ _ _ member)
      have present : q ∈ insert real window := Finset.mem_insert_of_mem inside
      change (if member : q ∈ insert real window then _ else _)=_
      rw [dif_pos present]
      rfl
    | t seed => rfl
    | omega seed => rfl

/-- Exact bridge from the pre-existing native source semantics, including the empty-set fallback. -/
theorem native_eq (window : Finset Native) (real : Native) (coordinates : Entropy ≃ State)
    (password : Password) (crypto : Tables Password Entropy) (target : Check)
    (adversary : WalletAdversary)
    (supported : Supported window adversary) :
    native window real coordinates password crypto target adversary=
      conditional window real coordinates password crypto target adversary := by
  unfold native conditional WalletAt.actual
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  congr 1
  funext omega
  rw [← PassphraseRows.sampling (sourceEmbedding window real),PMF.bind_map]
  congr 1
  funext table
  dsimp only [Function.comp_def]
  rw [PassphraseRows.real]
  congr 1
  funext chosen
  simp only [WalletAt.observe,FullGenerationCoupling.program,
    WalletGenerationCompiler.execution]
  refine Prod.ext (by rfl) ?_
  exact native_result window real adversary supported crypto omega table _ _

end PassphraseSource

namespace Theorem5Domains
open Gamma2Model PassphraseWindow PassphraseSource
variable {N : Nat} {Entropy Native Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Native] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

abbrev Program := Adversary (Password := Fin N) (Entropy := Entropy) (Native := Native)
  (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)

local notation "WalletProgram" => Program (N := N) (Entropy := Entropy) (Native := Native) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)

/-- The actual source uses native passphrase labels and the original independent prior. -/
def original (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check)
    (adversary : WalletProgram)
    (test : Fin N → Native → Seed → Result → Bool) : PMF Bool :=
  passwords.bind fun password => phrases.bind fun real => sampleTables.bind fun crypto =>
    (native window real coordinates password crypto target adversary).map
      (fun view => test password real view.1.seed view.2)

/-- Every sufficient larger window describes the same source experiment. -/
theorem original_between (smaller larger : Finset Native) (included : smaller ⊆ larger)
    (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check)
    (adversary : WalletProgram)
    (supported : Supported smaller adversary) (test : Fin N → Native → Seed → Result → Bool) :
    original smaller coordinates passwords phrases target adversary test=
      original larger coordinates passwords phrases target adversary test := by
  unfold original
  congr 1
  funext password
  congr 1
  funext real
  congr 1
  funext crypto
  rw [native_eq smaller real coordinates password crypto target adversary supported,
    native_eq larger real coordinates password crypto target adversary (supported_mono adversary _ _ included supported),
    conditional_between smaller larger included real coordinates password crypto target adversary supported]

/-- The finite category prior is only a change of the hidden label, not a conditional source distribution. -/
theorem seed_category (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check)
    (adversary : WalletProgram)
    (supported : Supported window adversary) (output : Result → Seed) :
    original window coordinates passwords phrases target adversary (fun _ _ seed result => decide (output result=seed))=
    FullSourceTransfer.original coordinates passwords (prior window phrases) target
      (fun data state => PassphraseRecoding.program (encode window) (adversary data state))
      (fun _ _ seed result => decide (output result=seed)) := by
  unfold original FullSourceTransfer.original prior
  simp only [PMF.bind_map]
  congr 1
  funext password
  congr 1
  funext real
  congr 1
  funext crypto
  rw [native_eq window real coordinates password crypto target adversary supported]
  exact finite_law window real coordinates password crypto target adversary (fun seed result => decide (output result=seed))

/-- The adversary can emit only finitely many passphrase labels for fixed private coins. -/
def outputWindow (adversary : WalletProgram) (output : Result → Fin N × Native) : Finset Native := by
  classical
  exact Finset.univ.biUnion fun input : Data × State =>
    (FiniteOracleViews.results (adversary input.1 input.2)).image (fun result => (output result).2)

def OutputSupported (window : Finset Native)
    (adversary : WalletProgram) (output : Result → Fin N × Native) : Prop :=
  ∀ data state table, (output (TranscriptErasure.execute table (adversary data state)).1).2 ∈ window

omit [DecidableEq Entropy] [DecidableEq Seed] [Fintype Entropy]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
theorem outputWindow_supported (adversary : WalletProgram) (output : Result → Fin N × Native) :
    OutputSupported (outputWindow adversary output) adversary output := by
  classical
  intro data state table
  exact Finset.mem_biUnion.mpr ⟨(data,state),Finset.mem_univ _,
    Finset.mem_image.mpr ⟨_,FiniteOracleViews.result_mem table (adversary data state),rfl⟩⟩

omit [DecidableEq Entropy] [DecidableEq Native] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
theorem output_mono (adversary : WalletProgram) (output : Result → Fin N × Native)
    (smaller larger : Finset Native) (included : smaller ⊆ larger) (supported : OutputSupported smaller adversary output) :
    OutputSupported larger adversary output := fun data state table => included (supported data state table)

omit [DecidableEq Entropy] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] in
/-- Other can never imitate a passphrase actually emitted by the covered program. -/
theorem pair_test (window : Finset Native) (real : Native) (password : Fin N)
    (candidate : Fin N × Native) (member : candidate.2 ∈ window) :
    decide (candidate=(password,real))=
      decide ((candidate.1,encode window candidate.2)=(password,encode window real)) := by
  have encoded : encode window candidate.2=some ⟨candidate.2,member⟩ := dif_pos member
  have same : encode window candidate.2=encode window real ↔ candidate.2=real := by
    rw [encoded]
    exact (encode_some window ⟨candidate.2,member⟩ real).trans eq_comm
  simp only [Prod.ext_iff,same]

/-- Exact-pair success also keeps the actual hidden label, including labels outside the query window. -/
theorem pair_category (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check)
    (adversary : WalletProgram)
    (supported : Supported window adversary) (output : Result → Fin N × Native)
    (outputs : OutputSupported window adversary output) :
    original window coordinates passwords phrases target adversary (fun password real _ result => decide (output result=(password,real)))=
    FullSourceTransfer.original coordinates passwords (prior window phrases) target
      (fun data state => PassphraseRecoding.program (encode window) (adversary data state))
      (fun password real _ result => decide (((output result).1,encode window (output result).2)=(password,real))) := by
  unfold original FullSourceTransfer.original prior
  simp only [PMF.bind_map]
  congr 1
  funext password
  congr 1
  funext real
  congr 1
  funext crypto
  rw [native_eq window real coordinates password crypto target adversary supported]
  rw [← finite_law window real coordinates password crypto target adversary
    (fun _ result => decide (((output result).1,encode window (output result).2)=(password,encode window real)))]
  unfold conditional
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  congr 1
  funext omega
  congr 1
  funext table
  congr 1
  funext chosen
  rw [PassphraseRecoding.execution]
  exact pair_test window real password _ (outputs _ _ _)

variable [Inhabited (Fin N)]

/-- Theorem 5(a) with arbitrary passphrase prior: no finite-support hypothesis and no extra tail error. -/
theorem seed_bound (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (sorted : Antitone passwords) (target : Check)
    (adversary : Program (N := N) (Entropy := Entropy) (Native := Native) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (supported : Supported window adversary) (output : Result → Seed)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password≤p1) (largestQ : ∀ phrase,phrases phrase≤s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : FullRawBound.Budgets adversary kA kS qB qH qT qOmega) :
    (original window coordinates passwords phrases target adversary
      (fun _ _ seed result => decide (output result=seed))) true ≤
      W1.top2 passwords phrases (kA/12) kS+
        Theorem5Base.error p1 s1 kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  obtain ⟨phrase,nonzero⟩ := phrases.support_nonempty
  have sPositive : 0<s1 := (pos_iff_ne_zero.mpr nonzero).trans_le (largestQ phrase)
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon positive _
  have ePositive : (0:ENNReal)<epsilon := ENNReal.coe_pos.mpr positive
  obtain ⟨larger,included,outside⟩ := finite_window window phrases (min s1 epsilon) (lt_min sPositive ePositive)
  have largeSupported := supported_mono adversary window larger included supported
  have massBound := largest larger phrases s1 largestQ (outside.trans (min_le_left _ _))
  have finiteBound := Theorem5Base.seed_bound coordinates passwords (prior larger phrases) sorted target output
    (fun data state => PassphraseRecoding.program (encode larger) (adversary data state))
    p1 s1 largestP massBound kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth
    (PassphraseRecoding.budgets (encode larger) adversary kA kS qB qH qT qOmega budget)
  rw [← seed_category larger coordinates passwords phrases target adversary largeSupported output,
    ← original_between window larger included coordinates passwords phrases target adversary supported] at finiteBound
  apply finiteBound.trans
  have topBound := top2_le larger passwords phrases (kA/12) kS
  have tailBound := outside.trans (min_le_right _ _)
  calc
    _ ≤ (W1.top2 passwords phrases (kA/12) kS+tail larger phrases)+
      Theorem5Base.error p1 s1 kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ :=
      add_le_add (add_le_add topBound le_rfl) le_rfl
    _ ≤ (W1.top2 passwords phrases (kA/12) kS+epsilon)+
      Theorem5Base.error p1 s1 kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ :=
      add_le_add (add_le_add (add_le_add le_rfl tailBound) le_rfl) le_rfl
    _ = _ := by abel

/-- Theorem 5(b) keeps the exact minimum for an arbitrary, possibly infinite passphrase alphabet. -/
theorem pair_bound (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (sorted : Antitone passwords) (target : Check)
    (adversary : Program (N := N) (Entropy := Entropy) (Native := Native) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (supported : Supported window adversary) (output : Result → Fin N × Native)
    (outputs : OutputSupported window adversary output)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password≤p1) (largestQ : ∀ phrase,phrases phrase≤s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : FullRawBound.Budgets adversary kA kS qB qH qT qOmega) :
    (original window coordinates passwords phrases target adversary
      (fun password real _ result => decide (output result=(password,real)))) true ≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+
        Theorem5Base.error p1 s1 kA kS qB qH qT qOmega := by
  obtain ⟨phrase,nonzero⟩ := phrases.support_nonempty
  have sPositive : 0<s1 := (pos_iff_ne_zero.mpr nonzero).trans_le (largestQ phrase)
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon positive _
  have ePositive : (0:ENNReal)<epsilon := ENNReal.coe_pos.mpr positive
  obtain ⟨larger,included,outside⟩ := finite_window window phrases (min s1 epsilon) (lt_min sPositive ePositive)
  have largeSupported := supported_mono adversary window larger included supported
  have largeOutputs := output_mono adversary output window larger included outputs
  have massBound := largest larger phrases s1 largestQ (outside.trans (min_le_left _ _))
  have finiteBound := Theorem5Base.pair_bound coordinates passwords (prior larger phrases) sorted target
    (fun result => ((output result).1,encode larger (output result).2))
    (fun data state => PassphraseRecoding.program (encode larger) (adversary data state))
    p1 s1 largestP massBound kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth
    (PassphraseRecoding.budgets (encode larger) adversary kA kS qB qH qT qOmega budget)
  rw [← pair_category larger coordinates passwords phrases target adversary largeSupported output largeOutputs,
    ← original_between window larger included coordinates passwords phrases target adversary supported] at finiteBound
  apply finiteBound.trans
  have first := top2_le larger passwords phrases (kA/12+1) (kS+1)
  have second := top2_le larger passwords phrases (kA/12) kS
  have tailBound := outside.trans (min_le_right _ _)
  have main := min_le_min first (add_le_add second (le_refl (p1*s1)))
  rw [add_right_comm _ (tail larger phrases) (p1*s1),min_add_add_right] at main
  calc
    _ ≤ (min (W1.top2 passwords phrases (kA/12+1) (kS+1))
      (W1.top2 passwords phrases (kA/12) kS+p1*s1)+tail larger phrases)+
        Theorem5Base.error p1 s1 kA kS qB qH qT qOmega := add_le_add main le_rfl
    _ ≤ (min (W1.top2 passwords phrases (kA/12+1) (kS+1))
      (W1.top2 passwords phrases (kA/12) kS+p1*s1)+epsilon)+
        Theorem5Base.error p1 s1 kA kS qB qH qT qOmega :=
      add_le_add (add_le_add le_rfl tailBound) le_rfl
    _ = _ := by abel

omit [Inhabited (Fin N)] in
/-- Condition only on the actual Q label, retaining its prior mass and every generated function. -/
theorem conditioned (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check)
    (adversary : Program (N := N) (Entropy := Entropy) (Native := Native) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (supported : Supported window adversary) (test : Fin N → Native → Seed → Result → Bool) :
    original window coordinates passwords phrases target adversary test=
    phrases.bind (fun real => FullSourceTransfer.original coordinates passwords (PMF.pure (encode window real)) target
      (fun data state => PassphraseRecoding.program (encode window) (adversary data state))
      (fun password _ seed result => test password real seed result)) := by
  unfold original FullSourceTransfer.original
  simp only [PMF.pure_bind]
  rw [PMF.bind_comm]
  congr 1
  funext real
  congr 1
  funext password
  congr 1
  funext crypto
  rw [native_eq window real coordinates password crypto target adversary supported]
  exact finite_law window real coordinates password crypto target adversary (test password real)

end Theorem5Domains

namespace PassphraseRefusal
open Gamma2Model TableFactors PassphraseWindow PassphraseSource
variable {N : Nat} {Entropy Native Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Native] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype
abbrev Context (window : Finset Native) := Native × FullSourceEnvironment.Context N Entropy
  (Category window) Seed Check Tail Data
abbrev Program := Theorem5Domains.Program (N := N) (Entropy := Entropy) (Native := Native)
  (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)

/-- Retain the native secret and all creation context while drawing H independently last. -/
def contexts (window : Finset Native) (passwords : PMF (Fin N)) (phrases : PMF Native)
    (target : Check) : PMF (Context (N := N) (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) window) :=
  phrases.bind fun real => (FullSourceEnvironment.contexts (Entropy := Entropy) (Seed := Seed)
    (Tail := Tail) (Data := Data) passwords (PMF.pure (encode window real)) target).map (fun context => (real,context))

def initial (window : Finset Native) (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check) :=
  ExactRefusalLift.initial (contexts (Entropy := Entropy) (Seed := Seed) (Tail := Tail) (Data := Data)
    window passwords phrases target) CryptoUniform.h

variable (window : Finset Native) (coordinates : Entropy ≃ State)

local notation "WalletProgram" => Program (N := N) (Entropy := Entropy) (Native := Native) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result)
local notation "GenerationContext" => Context (N := N) (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)

def score
    (adversary : WalletProgram)
    (test : Fin N → Native → Seed → Result → Bool)
    (sample : GenerationContext window × HTable) : Bool :=
  FullSourceEnvironment.score coordinates
    (fun data state => PassphraseRecoding.program (encode window) (adversary data state))
    (fun password _ seed result => test password sample.1.1 seed result) (sample.1.2,sample.2)

/-- Exact averaging of the already checked finite source environment, without conditioning on successful creation. -/
theorem original (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check)
    (adversary : WalletProgram)
    (supported : Supported window adversary) (test : Fin N → Native → Seed → Result → Bool) :
    Theorem5Domains.original window coordinates passwords phrases target adversary test=
      ((initial window passwords phrases target).map (score window coordinates adversary test)) := by
  rw [Theorem5Domains.conditioned window coordinates passwords phrases target adversary supported test]
  simp_rw [FullSourceEnvironment.original]
  simp only [initial,contexts,ExactRefusalLift.initial,PMF.map_bind,PMF.map_comp,PMF.bind_bind,
    PMF.bind_map,Function.comp_def,score]

def refused
    (sample : GenerationContext window × HTable) : Bool :=
  FullSourceRefusal.refused coordinates (sample.1.2,sample.2)

/-- H-independence survives arbitrary Q; the exact first-refusal rate is still 2^-256. -/
theorem probability (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check) : ((initial (Entropy := Entropy) (Seed := Seed) (Tail := Tail) (Data := Data) window passwords phrases target).map
      (refused window coordinates)) true=(2^256:ENNReal)⁻¹ :=
  G9Game.probability (contexts window passwords phrases target)
    (fun context => context.2.password) (fun context => context.2.other.1) (fun context => context.2.other.2.1)
    (fun context => coordinates context.2.chosen.entropy)

/-- The response may retry arbitrarily or report failure after the first refused creation. -/
def game
    (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check)
    (adversary : WalletProgram)
    (test : Fin N → Native → Seed → Result → Bool)
    (later : GenerationContext window × HTable → PMF Bool) : PMF Bool :=
  RefusalResponse.game (initial window passwords phrases target) (refused window coordinates)
    (score window coordinates adversary test) later

/-- Source-specific refusal lifting adds only the exact rate, retaining any native secret-dependent response. -/
theorem bound (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (target : Check)
    (adversary : WalletProgram)
    (supported : Supported window adversary) (test : Fin N → Native → Seed → Result → Bool)
    (later : GenerationContext window × HTable → PMF Bool)
    (upper : ENNReal)
    (base : (Theorem5Domains.original window coordinates passwords phrases target adversary test) true≤upper) :
    (game window coordinates passwords phrases target adversary test later) true≤upper+(2^256:ENNReal)⁻¹ := by
  rw [original window coordinates passwords phrases target adversary supported test] at base
  have lifted := RefusalResponse.bound (initial window passwords phrases target) (refused window coordinates)
    (score window coordinates adversary test) later upper base
  rw [probability window coordinates passwords phrases target] at lifted
  exact lifted

variable [Inhabited (Fin N)]

/-- Full Theorem 5(a), with arbitrary Q and the actual first-refusal response. -/
theorem seed_bound (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (sorted : Antitone passwords) (target : Check)
    (adversary : Program (N := N) (Entropy := Entropy) (Native := Native) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (supported : Supported window adversary) (output : Result → Seed)
    (later : Context (N := N) (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) window × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password≤p1) (largestQ : ∀ phrase,phrases phrase≤s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : FullRawBound.Budgets adversary kA kS qB qH qT qOmega) :
    (game window coordinates passwords phrases target adversary (fun _ _ seed result => decide (output result=seed)) later) true≤
      W1.top2 passwords phrases (kA/12) kS+
        Theorem5.error p1 s1 kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  have base := Theorem5Domains.seed_bound window coordinates passwords phrases sorted target adversary supported output
    p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  have lifted := bound window coordinates passwords phrases target adversary supported
    (fun _ _ seed result => decide (output result=seed)) later _ base
  exact lifted.trans (le_of_eq (by unfold Theorem5.error; abel))

/-- Full Theorem 5(b), preserving the exact minimum and the same explicit error. -/
theorem pair_bound (window : Finset Native) (coordinates : Entropy ≃ State)
    (passwords : PMF (Fin N)) (phrases : PMF Native) (sorted : Antitone passwords) (target : Check)
    (adversary : Program (N := N) (Entropy := Entropy) (Native := Native) (Seed := Seed)
      (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (supported : Supported window adversary) (output : Result → Fin N × Native)
    (outputs : Theorem5Domains.OutputSupported window adversary output)
    (later : Context (N := N) (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) window × HTable → PMF Bool)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password≤p1) (largestQ : ∀ phrase,phrases phrase≤s1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : FullRawBound.Budgets adversary kA kS qB qH qT qOmega) :
    (game window coordinates passwords phrases target adversary
      (fun password real _ result => decide (output result=(password,real))) later) true≤
      min (W1.top2 passwords phrases (kA/12+1) (kS+1))
        (W1.top2 passwords phrases (kA/12) kS+p1*s1)+
        Theorem5.error p1 s1 kA kS qB qH qT qOmega := by
  have base := Theorem5Domains.pair_bound window coordinates passwords phrases sorted target adversary supported output outputs
    p1 s1 largestP largestQ kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  have lifted := bound window coordinates passwords phrases target adversary supported
    (fun password real _ result => decide (output result=(password,real))) later _ base
  exact lifted.trans (le_of_eq (by unfold Theorem5.error; abel))

end PassphraseRefusal

end
end MhfeLean
