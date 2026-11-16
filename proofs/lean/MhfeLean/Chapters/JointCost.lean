import MhfeLean.Chapters.PasswordPairs
import MhfeLean.Chapters.SeedPairs
import MhfeLean.Chapters.ShortSources
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # Known passphrases, uniform dictionaries and one adaptive cost budget
-/

/-! Exact reduction of pair search to password search when the passphrase is known. -/
namespace KnownPassphrase
variable {N : Nat} {Passphrase : Type} [DecidableEq Passphrase]

/-- With a known passphrase only candidates in its column contribute mass. -/
theorem mass (p : Fin N → ENNReal) (phrase : Passphrase) (pairs : Finset (Fin N × Passphrase)) :
    W1.mass p (PMF.pure phrase) pairs =
      ∑ password ∈ (pairs.filter (fun pair => pair.2=phrase)).image Prod.fst,p password := by
  classical
  unfold W1.mass
  simp only [PMF.pure_apply,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  rw [Finset.sum_image]
  intro a ha b hb same
  apply Prod.ext same
  exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm

/-- The row limit and seed-query limit both constrain a known-passphrase test. -/
theorem top2 (p : Fin N → ENNReal) (sorted : Antitone p) (phrase : Passphrase) (rows pairs : Nat) :
    W1.top2 p (PMF.pure phrase) rows pairs =
      RankedMass.top p (min rows pairs) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro chosen
    apply iSup_le
    intro count
    apply iSup_le
    intro restricted
    rw [mass]
    let selected := (chosen.filter (fun pair => pair.2=phrase)).image Prod.fst
    have selected_subset : selected ⊆ Finset.univ.filter (fun password : Fin N => password.val < rows) := by
      intro password member
      obtain ⟨pair,inside,equal⟩ := Finset.mem_image.mp member
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,equal ▸ restricted pair (Finset.mem_filter.mp inside).1⟩
    have row_count : selected.card ≤ rows := by
      have card := Finset.card_le_card selected_subset
      simp only [Fin.card_filter_val_lt] at card
      exact card.trans (Nat.min_le_right _ _)
    have pair_count : selected.card ≤ pairs :=
      Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans count)
    exact RankedMass.set_bound p sorted selected _ (Nat.le_min.mpr ⟨row_count,pair_count⟩)
  · let leading := Finset.univ.filter (fun password : Fin N => password.val < min rows pairs)
    let chosen := leading.image (fun password => (password,phrase))
    have injective : Function.Injective (fun password : Fin N => (password,phrase)) := by
      intro a b equal
      exact congrArg Prod.fst equal
    have count : chosen.card ≤ pairs := by
      rw [Finset.card_image_of_injective _ injective]
      simp only [leading,Fin.card_filter_val_lt]
      omega
    have restricted : ∀ pair ∈ chosen,pair.1.val < rows := by
      intro pair member
      obtain ⟨password,inside,equal⟩ := Finset.mem_image.mp member
      rw [← equal]
      exact (Finset.mem_filter.mp inside).2.trans_le (Nat.min_le_left _ _)
    have value : W1.mass p (PMF.pure phrase) chosen = RankedMass.top p (min rows pairs) := by
      unfold W1.mass
      rw [Finset.sum_image]
      · simp only [PMF.pure_apply_self,mul_one]
        rfl
      · intro a _ b _ equal
        exact injective equal
    rw [← value]
    exact le_iSup_of_le chosen (le_iSup_of_le count (le_iSup_of_le restricted le_rfl))

/-- The first expression in the pair-game minimum gives the stated one-extra-password allowance. -/
theorem pair_main (p : Fin N → ENNReal) (sorted : Antitone p) (phrase : Passphrase)
    (rows pairs : Nat) (p1 : ENNReal) :
    min (W1.top2 p (PMF.pure phrase) (rows+1) (pairs+1))
      (W1.top2 p (PMF.pure phrase) rows pairs+p1) ≤
      RankedMass.top p (min rows pairs+1) := by
  apply (min_le_left _ _).trans
  rw [top2 p sorted phrase]
  have equal : min (rows+1) (pairs+1)=min rows pairs+1 := by omega
  rw [equal]

end KnownPassphrase

/-! Known-passphrase specializations keep the actual profile-source game and its exclusions. -/
namespace KnownProfile
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data] [Inhabited (Fin N)]
attribute [local instance] FiniteBits.fintype

/-- A known Q leaves min(floor(kA/12),kS) tested passwords in the seed bound. -/
theorem seed_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrase : Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullSourceRefusal.game coordinates passwords (PMF.pure phrase) target
      (score coordinates adversary (fun _ _ seed result => decide (output result=seed))) later) true ≤
      RankedMass.top passwords (min (kA/12) kS)+
        Theorem5.error p1 1 kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  have base := Theorem5.seed_bound coordinates passwords (PMF.pure phrase) sorted target output adversary
    later p1 1 largestP (PMF.pure phrase).coe_le_one kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  simpa only [KnownPassphrase.top2 passwords sorted phrase] using base

/-- The known-Q pair game permits one untested final password, with all original hypotheses retained. -/
theorem pair_bound (coordinates : Entropy ≃ State) (passwords : PMF (Fin N)) (phrase : Passphrase)
    (sorted : Antitone passwords) (target : Check) (output : Result → Fin N × Passphrase)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Passphrase)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy Passphrase Seed Check Tail Data × HTable → PMF Bool)
    (p1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullSourceRefusal.game coordinates passwords (PMF.pure phrase) target
      (score coordinates adversary (fun password q _ result => decide (output result=(password,q)))) later) true ≤
      RankedMass.top passwords (min (kA/12) kS+1)+
        Theorem5.error p1 1 kA kS qB qH qT qOmega := by
  have base := Theorem5.pair_bound coordinates passwords (PMF.pure phrase) sorted target output adversary
    later p1 1 largestP (PMF.pure phrase).coe_le_one kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  simp only [mul_one] at base
  exact base.trans (add_le_add (KnownPassphrase.pair_main passwords sorted phrase (kA/12) kS p1) le_rfl)

end KnownProfile

/-! The seed proof accepts a run-sensitive pair-mass bound instead of rectangular budgets. -/
namespace FlexibleSeedBound
open Gamma2Model GameExpectation MomentTools ProbabilityTools
open SeedQueryRun SeedQueryBounds QueryCounts
variable {N : Nat} {Entropy Passphrase Seed Check Tail Data Result : Type}
  [Fintype Entropy] [DecidableEq Entropy] [DecidableEq Passphrase] [Inhabited (Fin N)]
  [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]

theorem bound (source : State → Entropy) (injective : Function.Injective source)
    (firstHalf : Entropy → Half) (projects : ∀ state,firstHalf (source state)=state.1)
    (passwords : PMF (Fin N)) (phrases : PMF Passphrase) (seedOutput : Result → Seed)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (upper : ENNReal)
    (mainBound : moment (worlds passwords phrases)
      (fun world => if world.1 ∈ assigned source wallet adversary world.2 then 1 else 0) ≤ upper)
    (p1 s1 : ENNReal) (largestP : ∀ password,passwords password ≤ p1) (largestQ : ∀ phrase,phrases phrase ≤ s1)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budgetA : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (compiled wallet adversary container)).2.countP isH ≤ qH)
    (budgetS : ∀ input : Input (N := N) (Entropy := Entropy),(pairs wallet adversary input).length ≤ kS)
    (budgetT : ∀ input : Input (N := N) (Entropy := Entropy),(full wallet adversary input).2.countP SeedWalletModel.isT ≤ qT)
    (budgetOmega : ∀ input : Input (N := N) (Entropy := Entropy),(full wallet adversary input).2.countP SeedWalletModel.isOmega ≤ qOmega) :
    moment (independentPair (worlds passwords phrases) (PMF.uniformOfFintype Seed))
      (fun sample => if Theta2SeedBound.winOrBad source seedOutput wallet adversary sample then 1 else 0) ≤
      upper+(s1*kS+qB+(1+12*p1)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+
      (qT+qOmega)/(2^512:ENNReal)+(2^512:ENNReal)⁻¹ := by
  classical
  have included :
      moment (worlds passwords phrases) (fun world => if bad source wallet adversary world then 1 else 0) ≤
      moment (worlds passwords phrases) (fun world => if world.1 ∈ assigned source wallet adversary world.2 then 1 else 0)+
      moment (worlds passwords phrases) (SeedQueryEnvelope.errors firstHalf wallet adversary) := by
    rw [← MomentTools.add]
    exact mono _ _ _ (SeedQueryEnvelope.pointwise source injective firstHalf projects wallet adversary)
  have errorBound := SeedQueryEnvelope.bound firstHalf passwords phrases wallet adversary p1 s1 largestP largestQ
    kA kS qB qH budgetA budgetB budgetH budgetS
  have queryBound := included.trans (add_le_add mainBound errorBound)
  let chosen := fun world : World (N := N) (Entropy := Entropy) (Passphrase := Passphrase) =>
    insert (seedOutput (full wallet adversary world.2).1)
      (SeedWalletModel.blindSeeds (full wallet adversary world.2).2).toFinset
  have estimate := IndependentSeedUnion.bound (worlds passwords phrases) (bad source wallet adversary) chosen
    (Theta2SeedBound.winOrBad source seedOutput wallet adversary) (qT+qOmega+1)
    (fun world => (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
      (SeedWalletModel.blind_bound _ qT qOmega (budgetT world.2) (budgetOmega world.2)) 1))
    _ queryBound (fun sample hit => by
      have details := of_decide_eq_true hit
      rcases details with wins | badS | query
      · exact Or.inr (Finset.mem_insert.mpr (Or.inl wins.symm))
      · exact Or.inl badS
      · exact Or.inr (Finset.mem_insert_of_mem (List.mem_toFinset.mpr query)))
  apply estimate.trans_eq
  rw [seedWidth]
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,ENNReal.add_div,one_div]
  abel

end FlexibleSeedBound

/-! Uniform-dictionary interpretation of the actual profile-source seed bound. -/
namespace UniformPairModel
open Gamma2Model TableFactors FullRawBound FullSourceEnvironment
variable {N M : Nat} [Inhabited (Fin N)] [Inhabited (Fin M)]

/-- Uniform pair mass has both the seed-computation cap and the distinct-password cap. -/
theorem top2 (rows pairs : Nat) :
    W1.top2 (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) rows pairs =
      (min pairs (min N rows*M) : Nat)/(N*M : ENNReal) := by
  have first : (fun value : Fin N => PMF.uniformOfFintype (Fin N) value)=fun _ => (N:ENNReal)⁻¹ := by
    funext value
    simp only [PMF.uniformOfFintype_apply,Fintype.card_fin]
  have second : (fun value : Fin M => PMF.uniformOfFintype (Fin M) value)=fun _ => (M:ENNReal)⁻¹ := by
    funext value
    simp only [PMF.uniformOfFintype_apply,Fintype.card_fin]
  change W1.top2 (fun value : Fin N => PMF.uniformOfFintype (Fin N) value)
    (fun value : Fin M => PMF.uniformOfFintype (Fin M) value) rows pairs = _
  rw [first,second,UniformTop2.exact_top]
  rw [div_eq_mul_inv,ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top M)) (Or.inl (ENNReal.natCast_ne_top N))]

/-- The weaker uncapped-row expression used in the prose remains a valid upper bound. -/
theorem top2_le (rows pairs : Nat) :
    W1.top2 (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) rows pairs ≤
      (min pairs (rows*M) : Nat)/(N*M : ENNReal) := by
  rw [top2]
  apply ENNReal.div_le_div_right
  exact_mod_cast min_le_min le_rfl (Nat.mul_le_mul_right M (Nat.min_le_right N rows))

variable {Entropy Seed Check Tail Data Result : Type}
  [DecidableEq Entropy] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- The exact dictionary formula applies to the actual source game, including all error and refusal terms. -/
theorem seed_bound (coordinates : Entropy ≃ State) (target : Check) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Fin M)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy (Fin M) Seed Check Tail Data × HTable → PMF Bool)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullSourceRefusal.game coordinates (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) target
      (score coordinates adversary (fun _ _ seed result => decide (output result=seed))) later) true ≤
      (min kS (min N (kA/12)*M) : Nat)/(N*M : ENNReal)+
        Theorem5.error (N:ENNReal)⁻¹ (M:ENNReal)⁻¹ kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  have sorted : Antitone (PMF.uniformOfFintype (Fin N)) := by
    intro a b _
    simp only [PMF.uniformOfFintype_apply]
    exact le_rfl
  have first : ∀ value : Fin N,PMF.uniformOfFintype (Fin N) value ≤ (N:ENNReal)⁻¹ := by
    intro value
    simp only [PMF.uniformOfFintype_apply,Fintype.card_fin]
    exact le_rfl
  have second : ∀ value : Fin M,PMF.uniformOfFintype (Fin M) value ≤ (M:ENNReal)⁻¹ := by
    intro value
    simp only [PMF.uniformOfFintype_apply,Fintype.card_fin]
    exact le_rfl
  have base := Theorem5.seed_bound coordinates (PMF.uniformOfFintype (Fin N))
    (PMF.uniformOfFintype (Fin M)) sorted target output adversary later
    (N:ENNReal)⁻¹ (M:ENNReal)⁻¹ first second kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  simpa only [top2] using base

end UniformPairModel

/-! A pathwise combined work cap bounds the mass of adaptively selected uniform pairs. -/
namespace AdaptivePairCost
open GameExpectation MomentTools ProbabilityTools
variable {N M : Nat} [Inhabited (Fin N)] [Inhabited (Fin M)]

/-- The real-valued work calculation also bounds the exact extended-nonnegative pair mass. -/
theorem top2_bound (rows pairs : Nat) (costA costS budget : ℝ) (positiveA : 0 < costA)
    (nonnegativeS : 0 ≤ costS) (limit : 12*costA*(rows:ℝ)+costS*(pairs:ℝ) ≤ budget) :
    W1.top2 (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) rows pairs ≤
      ENNReal.ofReal (budget/((N:ℝ)*(12*costA+(M:ℝ)*costS))) := by
  have positiveN : 0 < N := (default : Fin N).isLt.trans_le' (Nat.zero_le _)
  have positiveM : 0 < M := (default : Fin M).isLt.trans_le' (Nat.zero_le _)
  have positiveNR : 0 < (N:ℝ) := by exact_mod_cast positiveN
  have positiveMR : 0 < (M:ℝ) := by exact_mod_cast positiveM
  have denominator : 0 < (N:ℝ)*(M:ℝ) := mul_pos positiveNR positiveMR
  have estimate := PairCost.probability (rows:ℝ) pairs N M costA costS budget
    positiveNR positiveMR positiveA nonnegativeS limit
  apply (UniformPairModel.top2_le (N := N) (M := M) rows pairs).trans
  have rewritten : ((min pairs (rows*M):Nat):ENNReal)/(N*M:ENNReal)=
      ENNReal.ofReal ((min (pairs:ℝ) ((rows:ℝ)*(M:ℝ)))/((N:ℝ)*(M:ℝ))) := by
    rw [ENNReal.ofReal_div_of_pos denominator]
    simp only [← Nat.cast_mul,← Nat.cast_min,ENNReal.ofReal_natCast]
  rw [rewritten]
  exact ENNReal.ofReal_le_ofReal estimate

/-- Adaptivity is averaged over an independent run; the total-work premise holds on each execution. -/
theorem adaptive {View : Type} (views : PMF View)
    (chosen : View → Finset (Fin N × Fin M)) (costA costS budget : ℝ)
    (positiveA : 0 < costA) (nonnegativeS : 0 ≤ costS)
    (limit : ∀ view,12*costA*(((chosen view).image Prod.fst).card:ℝ)+costS*((chosen view).card:ℝ) ≤ budget) :
    moment (independentPair (independentPair (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M))) views)
      (fun world => if world.1 ∈ chosen world.2 then 1 else 0) ≤
      ENNReal.ofReal (budget/((N:ℝ)*(12*costA+(M:ℝ)*costS))) := by
  have sorted : Antitone (PMF.uniformOfFintype (Fin N)) := by
    intro a b _
    simp only [PMF.uniformOfFintype_apply]
    exact le_rfl
  apply (PairMass.adaptive (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) sorted views chosen).trans
  exact MomentTools.bounded views _ _ (fun view =>
    top2_bound _ _ costA costS budget positiveA nonnegativeS (limit view))

end AdaptivePairCost

/-! Charge an actual assigned row once and every assigned seed pair separately. -/
namespace AssignmentCost
open Gamma2Model GameExpectation SeedQueryRun QueryCounts
variable {N M : Nat} {Entropy Seed Check Tail Data Result : Type}
  [Inhabited (Fin N)] [Inhabited (Fin M)] [DecidableEq Entropy]

omit [Inhabited (Fin N)] [Inhabited (Fin M)] in
/-- A pathwise cap on actual A/S calls pays for every row and pair in the assignment. -/
theorem paid (source : State → Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (input : Input (N := N) (Entropy := Entropy)) (costA costS budget : ℝ)
    (nonnegativeA : 0 ≤ costA) (nonnegativeS : 0 ≤ costS)
    (limit : costA*((execute input.2 (compiled wallet adversary input.1)).2.countP isA:ℝ)+
      costS*((pairs wallet adversary input).length:ℝ) ≤ budget) :
    12*costA*(((assigned source wallet adversary input).image Prod.fst).card:ℝ)+
      costS*((assigned source wallet adversary input).card:ℝ) ≤ budget := by
  have counts := ActualPairAssignment.counts source input.1 input.2 _ _
    ((execute input.2 (compiled wallet adversary input.1)).2.countP isA) ((pairs wallet adversary input).length) le_rfl le_rfl
  have rowPaid : 12*((assigned source wallet adversary input).image Prod.fst).card ≤
      (execute input.2 (compiled wallet adversary input.1)).2.countP isA := by
    apply (Nat.mul_le_mul_left 12 counts.1).trans
    exact Nat.mul_div_le _ _
  have rowReal : 12*((((assigned source wallet adversary input).image Prod.fst).card):ℝ) ≤
      ((execute input.2 (compiled wallet adversary input.1)).2.countP isA:ℝ) := by exact_mod_cast rowPaid
  have pairReal : ((assigned source wallet adversary input).card:ℝ) ≤ ((pairs wallet adversary input).length:ℝ) := by
    exact_mod_cast counts.2
  calc
    _ = costA*(12*((((assigned source wallet adversary input).image Prod.fst).card):ℝ))+
        costS*((assigned source wallet adversary input).card:ℝ) := by ring
    _ ≤ costA*((execute input.2 (compiled wallet adversary input.1)).2.countP isA:ℝ)+
        costS*((pairs wallet adversary input).length:ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left rowReal nonnegativeA) (mul_le_mul_of_nonneg_left pairReal nonnegativeS)
    _ ≤ _ := limit

variable [Fintype Entropy]

/-- The actual adaptive pair set has the one-budget mass bound for independent uniform secrets. -/
theorem main_bound (source : State → Entropy)
    (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data))
    (adversary : Program (N := N) (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Result := Result) (Check := Check) (Tail := Tail) (Data := Data))
    (costA costS budget : ℝ) (positiveA : 0 < costA) (nonnegativeS : 0 ≤ costS)
    (limit : ∀ input : Input (N := N) (Entropy := Entropy),
      costA*((execute input.2 (compiled wallet adversary input.1)).2.countP isA:ℝ)+
        costS*((pairs wallet adversary input).length:ℝ) ≤ budget) :
    moment (SeedQueryBounds.worlds (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)))
      (fun world => if world.1 ∈ assigned source wallet adversary world.2 then 1 else 0) ≤
      ENNReal.ofReal (budget/((N:ℝ)*(12*costA+(M:ℝ)*costS))) := by
  exact AdaptivePairCost.adaptive SeedQueryBounds.views (assigned source wallet adversary)
    costA costS budget positiveA nonnegativeS (fun input => paid source wallet adversary input costA costS budget
      positiveA.le nonnegativeS (limit input))

end AssignmentCost

/-! One adaptive work budget for actual profile-source seed recovery, with explicit error caps. -/
namespace FullCostBound
open Gamma2Model FullRawBound FullSourceEnvironment QueryCounts
variable {N M : Nat} {Entropy Seed Check Tail Data Result : Type}
  [Inhabited (Fin N)] [Inhabited (Fin M)] [DecidableEq Entropy] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- The same total cap holds on every transcript, without charging owner-generation calls. -/
def Costs (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Fin M)
    (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (costA costS budget : ℝ) : Prop :=
  ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed)
    (Check := Check) (Tail := Tail) (Data := Data)) data container crypto,
    costA*((execute crypto (SeedQueryRun.compiled wallet (adversary data) container)).2.countP isA:ℝ)+
      costS*((SeedQueryRun.pairs wallet (adversary data) (container,crypto)).length:ℝ) ≤ budget

omit [DecidableEq Check] in
/-- Raw-game pair mass is bounded by combined work; fixed hard caps still bound exceptional events. -/
theorem raw_bound (coordinates : Entropy ≃ State) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Fin M)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (costA costS cost : ℝ) (positiveA : 0 < costA) (nonnegativeS : 0 ≤ costS)
    (costLimit : Costs adversary costA costS cost)
    (kA kS qB qH qT qOmega : Nat) (seedWidth : Fintype.card Seed=2^512)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullRawInputs.rawGame coordinates (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) adversary
      (fun _ _ seed result => decide (output result=seed))) true ≤
      ENNReal.ofReal (cost/((N:ℝ)*(12*costA+(M:ℝ)*costS)))+
      ((M:ENNReal)⁻¹*kS+qB+(1+12*(N:ENNReal)⁻¹)*kA+66)/(2^128:ENNReal)+(qH+kA)/(2^256:ENNReal)+
      (qT+qOmega)/(2^512:ENNReal)+(2^512:ENNReal)⁻¹ := by
  apply FullRawBound.shared coordinates (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) adversary _ _
  intro wallet data
  simp_rw [FullRawEvents.seed_event]
  have main := AssignmentCost.main_bound coordinates.symm wallet (adversary data)
    costA costS cost positiveA nonnegativeS (fun input => costLimit wallet data input.1 input.2)
  have first : ∀ value : Fin N,PMF.uniformOfFintype (Fin N) value ≤ (N:ENNReal)⁻¹ := by
    intro value
    simp only [PMF.uniformOfFintype_apply,Fintype.card_fin]
    exact le_rfl
  have second : ∀ value : Fin M,PMF.uniformOfFintype (Fin M) value ≤ (M:ENNReal)⁻¹ := by
    intro value
    simp only [PMF.uniformOfFintype_apply,Fintype.card_fin]
    exact le_rfl
  exact FlexibleSeedBound.bound coordinates.symm coordinates.symm.injective
    (FullSourceCoordinates.firstHalf coordinates) (FullSourceCoordinates.projects coordinates)
    (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) output wallet (adversary data)
    _ main (N:ENNReal)⁻¹ (M:ENNReal)⁻¹ first second kA kS qB qH qT qOmega seedWidth
    (budget.a wallet data) (budget.b wallet data) (budget.h wallet data) (budget.s wallet data)
    (budget.t wallet data) (budget.omega wallet data)

/-- Actual generation and first-refusal response preserve the one-budget main term and full epsilon_W. -/
theorem bound (coordinates : Entropy ≃ State) (target : Check) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Fin M)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy (Fin M) Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (costA costS cost : ℝ) (positiveA : 0 < costA) (nonnegativeS : 0 ≤ costS)
    (costLimit : Costs adversary costA costS cost)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : Budgets adversary kA kS qB qH qT qOmega) :
    (FullSourceRefusal.game coordinates (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) target
      (score coordinates adversary (fun _ _ seed result => decide (output result=seed))) later) true ≤
      ENNReal.ofReal (cost/((N:ℝ)*(12*costA+(M:ℝ)*costS)))+
        Theorem5.error (N:ENNReal)⁻¹ (M:ENNReal)⁻¹ kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  have transfer := FullSourceTransfer.transfer coordinates (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) target adversary
    (fun _ _ seed result => decide (output result=seed)) kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth budget
  have raw := raw_bound coordinates output adversary costA costS cost positiveA nonnegativeS costLimit
    kA kS qB qH qT qOmega seedWidth budget
  have base : (FullSourceTransfer.original coordinates (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) target adversary
      (fun _ _ seed result => decide (output result=seed))) true ≤
      ENNReal.ofReal (cost/((N:ℝ)*(12*costA+(M:ℝ)*costS)))+
        Theorem5Base.error (N:ENNReal)⁻¹ (M:ENNReal)⁻¹ kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
    apply transfer.trans
    apply (add_le_add raw le_rfl).trans_eq
    unfold Theorem5Base.error
    abel
  rw [FullSourceEnvironment.original] at base
  have result := FullSourceRefusal.bound coordinates (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) target
    (score coordinates adversary (fun _ _ seed result => decide (output result=seed))) later _ base
  exact result.trans (le_of_eq (by unfold Theorem5.error; abel))

end FullCostBound

/-! A positive per-call cost turns one pathwise work cap into the exact floor query caps. -/
namespace CombinedBudget
open Gamma2Model FullRawBound QueryCounts

/-- Both individual call counts are bounded; no average-cost assumption is used. -/
theorem counts (a s : Nat) (costA costS cost : ℝ) (positiveA : 0 < costA) (positiveS : 0 < costS)
    (nonnegativeCost : 0 ≤ cost) (limit : costA*(a:ℝ)+costS*(s:ℝ) ≤ cost) :
    a ≤ ⌊cost/costA⌋₊ ∧ s ≤ ⌊cost/costS⌋₊ := by
  constructor
  · apply (Nat.le_floor_iff (div_nonneg nonnegativeCost positiveA.le)).2
    apply (le_div_iff₀ positiveA).2
    have estimate := (le_add_of_nonneg_right (mul_nonneg positiveS.le (Nat.cast_nonneg s))).trans limit
    simpa only [mul_comm] using estimate
  · apply (Nat.le_floor_iff (div_nonneg nonnegativeCost positiveS.le)).2
    apply (le_div_iff₀ positiveS).2
    have estimate := (le_add_of_nonneg_left (mul_nonneg positiveA.le (Nat.cast_nonneg a))).trans limit
    simpa only [mul_comm] using estimate

variable {N M : Nat} {Entropy Seed Check Tail Data Result : Type}

/-- Cheap-query caps and actual combined A/S work provide every hard budget required by the source proof. -/
theorem budgets
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Fin M)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (costA costS cost : ℝ) (positiveA : 0 < costA) (positiveS : 0 < costS) (nonnegativeCost : 0 ≤ cost)
    (costLimit : FullCostBound.Costs adversary costA costS cost)
    (qB qH qT qOmega : Nat)
    (budgetB : ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) data container crypto,
      (execute crypto (SeedQueryRun.compiled wallet (adversary data) container)).2.countP isB ≤ qB)
    (budgetH : ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) data container crypto,
      (execute crypto (SeedQueryRun.compiled wallet (adversary data) container)).2.countP isH ≤ qH)
    (budgetT : ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) data input,
      (SeedQueryRun.full wallet (adversary data) input).2.countP SeedWalletModel.isT ≤ qT)
    (budgetOmega : ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) data input,
      (SeedQueryRun.full wallet (adversary data) input).2.countP SeedWalletModel.isOmega ≤ qOmega) :
    Budgets adversary ⌊cost/costA⌋₊ ⌊cost/costS⌋₊ qB qH qT qOmega := by
  refine ⟨?_,budgetB,budgetH,?_,budgetT,budgetOmega⟩
  · intro wallet data container crypto
    exact (counts _ _ costA costS cost positiveA positiveS nonnegativeCost (costLimit wallet data container crypto)).1
  · intro wallet data input
    exact (counts _ _ costA costS cost positiveA positiveS nonnegativeCost (costLimit wallet data input.1 input.2)).2

end CombinedBudget

/-! The source theorem with exceptional-event caps derived from the single work budget. -/
namespace FullCostFloor
open Gamma2Model FullRawBound FullSourceEnvironment QueryCounts
variable {N M : Nat} {Entropy Seed Check Tail Data Result : Type}
  [Inhabited (Fin N)] [Inhabited (Fin M)] [DecidableEq Entropy] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- Epsilon uses floor(c/CA) and floor(c/CS), derived from the same pathwise cap as the main term. -/
theorem bound (coordinates : Entropy ≃ State) (target : Check) (output : Result → Seed)
    (adversary : FullProgram (N := N) (Entropy := Entropy) (Passphrase := Fin M)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Context N Entropy (Fin M) Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (costA costS cost : ℝ) (positiveA : 0 < costA) (positiveS : 0 < costS) (nonnegativeCost : 0 ≤ cost)
    (costLimit : FullCostBound.Costs adversary costA costS cost)
    (qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budgetB : ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) data container crypto,
      (execute crypto (SeedQueryRun.compiled wallet (adversary data) container)).2.countP isB ≤ qB)
    (budgetH : ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) data container crypto,
      (execute crypto (SeedQueryRun.compiled wallet (adversary data) container)).2.countP isH ≤ qH)
    (budgetT : ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) data input,
      (SeedQueryRun.full wallet (adversary data) input).2.countP SeedWalletModel.isT ≤ qT)
    (budgetOmega : ∀ (wallet : WalletTables (Entropy := Entropy) (Passphrase := Fin M) (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data)) data input,
      (SeedQueryRun.full wallet (adversary data) input).2.countP SeedWalletModel.isOmega ≤ qOmega) :
    (FullSourceRefusal.game coordinates (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) target
      (score coordinates adversary (fun _ _ seed result => decide (output result=seed))) later) true ≤
      ENNReal.ofReal (cost/((N:ℝ)*(12*costA+(M:ℝ)*costS)))+
        Theorem5.error (N:ENNReal)⁻¹ (M:ENNReal)⁻¹ ⌊cost/costA⌋₊ ⌊cost/costS⌋₊ qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  have budget := CombinedBudget.budgets adversary costA costS cost positiveA positiveS nonnegativeCost
    costLimit qB qH qT qOmega budgetB budgetH budgetT budgetOmega
  exact FullCostBound.bound coordinates target output adversary later costA costS cost positiveA positiveS.le
    costLimit ⌊cost/costA⌋₊ ⌊cost/costS⌋₊ qB qH qT qOmega entropyWidth seedWidth checkWidth budget

end FullCostFloor

/-! Independent private strategy coins preserve the pathwise combined-cost source bound. -/
namespace FullCostRandomized
open Gamma2Model FullRawBound FullSourceEnvironment
variable {N M : Nat} {Entropy Seed Check Tail Data Result Strategy : Type}
  [Inhabited (Fin N)] [Inhabited (Fin M)] [DecidableEq Entropy] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype

/-- Every strategy obeys the same actual work and query caps; the environment remains independently sampled. -/
theorem bound (coins : PMF Strategy) (coordinates : Entropy ≃ State) (target : Check) (output : Result → Seed)
    (adversary : Strategy → FullProgram (N := N) (Entropy := Entropy) (Passphrase := Fin M)
      (Seed := Seed) (Check := Check) (Tail := Tail) (Data := Data) (Result := Result))
    (later : Strategy → Context N Entropy (Fin M) Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (costA costS cost : ℝ) (positiveA : 0 < costA) (nonnegativeS : 0 ≤ costS)
    (costLimit : ∀ strategy,FullCostBound.Costs (adversary strategy) costA costS cost)
    (kA kS qB qH qT qOmega : Nat) (entropyWidth : Fintype.card Entropy=2^256)
    (seedWidth : Fintype.card Seed=2^512) (checkWidth : Fintype.card Check=2^16)
    (budget : ∀ strategy,Budgets (adversary strategy) kA kS qB qH qT qOmega) :
    (coins.bind fun strategy => FullSourceRefusal.game coordinates
      (PMF.uniformOfFintype (Fin N)) (PMF.uniformOfFintype (Fin M)) target
      (score coordinates (adversary strategy) (fun _ _ seed result => decide (output result=seed))) (later strategy)) true ≤
      ENNReal.ofReal (cost/((N:ℝ)*(12*costA+(M:ℝ)*costS)))+
        Theorem5.error (N:ENNReal)⁻¹ (M:ENNReal)⁻¹ kA kS qB qH qT qOmega+(2^512:ENNReal)⁻¹ := by
  rw [PMF.bind_apply]
  apply MomentTools.bounded
  intro strategy
  exact FullCostBound.bound coordinates target output (adversary strategy) (later strategy) costA costS cost
    positiveA nonnegativeS (costLimit strategy) kA kS qB qH qT qOmega entropyWidth seedWidth checkWidth (budget strategy)

end FullCostRandomized

end
end MhfeLean
