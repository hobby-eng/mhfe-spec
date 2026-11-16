import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.GenerationSurvival
import MhfeLean.Chapters.ShortSources

namespace MhfeLean
noncomputable section

/-! # Lemma W3: joint source, seed and check programming
-/

/-! Exact complete-table laws for one-point value programming and retained suffix programming. -/
namespace PointProgramming
open ProbabilityTools
variable {Domain Value Prefix Tail : Type} [DecidableEq Domain]

def exchange (point : Domain) : Equiv.Perm ((Domain → Value) × Value) where
  toFun := fun pair => (Function.update pair.1 point pair.2,pair.1 point)
  invFun := fun pair => (Function.update pair.1 point pair.2,pair.1 point)
  left_inv := by rintro ⟨table,value⟩; simp
  right_inv := by rintro ⟨table,value⟩; simp

def tailExchange (point : Domain) : Equiv.Perm ((Domain → Prefix × Tail) × Tail) where
  toFun := fun pair => (Function.update pair.1 point ((pair.1 point).1,pair.2),(pair.1 point).2)
  invFun := fun pair => (Function.update pair.1 point ((pair.1 point).1,pair.2),(pair.1 point).2)
  left_inv := by rintro ⟨table,value⟩; simp
  right_inv := by rintro ⟨table,value⟩; simp

variable [Fintype Domain] [Fintype Value] [Nonempty Value]

/-- Reading a uniform function at a fixed point equals programming a uniform value there, jointly with the whole function. -/
theorem value (point : Domain) :
    (PMF.uniformOfFintype (Domain → Value)).map (fun table => (table,table point)) =
      (PMF.uniformOfFintype Value).bind fun answer =>
        (PMF.uniformOfFintype (Domain → Value)).map (fun table => (Function.update table point answer,answer)) := by
  have transported := PMF.uniformOfFintype_map_of_bijective (exchange (Value := Value) point) (exchange point).bijective
  calc
    _ = ((PMF.uniformOfFintype ((Domain → Value) × Value)).map Prod.fst).map (fun table => (table,table point)) := by rw [uniform_fst]
    _ = (PMF.uniformOfFintype ((Domain → Value) × Value)).map
        ((fun pair => (Function.update pair.1 point pair.2,pair.2)) ∘ exchange point) := by
      rw [PMF.map_comp]
      congr 1
      funext pair
      simp only [Function.comp_def, exchange, Equiv.coe_fn_mk, Function.update_idem, Function.update_eq_self]
    _ = ((PMF.uniformOfFintype ((Domain → Value) × Value)).map (exchange point)).map
        (fun pair => (Function.update pair.1 point pair.2,pair.2)) := (PMF.map_comp _ _ _).symm
    _ = _ := by
      rw [transported, uniform_product]
      simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
      have simpaTerm := PMF.bind_comm (PMF.uniformOfFintype (Domain → Value)) (PMF.uniformOfFintype Value) (fun table answer => PMF.pure (Function.update table point answer,answer))
      (try simp only [PMF.map] at simpaTerm ⊢)
      exact simpaTerm

variable [Fintype Prefix] [Fintype Tail] [Nonempty Prefix] [Nonempty Tail]

omit [Fintype Value] [Nonempty Value] in
/-- A separately sampled suffix and an existing uniform suffix induce the same prefix-forced complete table. -/
theorem suffix (point : Domain) (target : Prefix) :
    (PMF.uniformOfFintype Tail).bind (fun tail =>
      (PMF.uniformOfFintype (Domain → Prefix × Tail)).map (fun table => Function.update table point (target,tail))) =
      (PMF.uniformOfFintype (Domain → Prefix × Tail)).map (fun table => Function.update table point (target,(table point).2)) := by
  have transported := PMF.uniformOfFintype_map_of_bijective (tailExchange (Prefix := Prefix) (Tail := Tail) point) (tailExchange point).bijective
  have invariant : (PMF.uniformOfFintype ((Domain → Prefix × Tail) × Tail)).map
      (fun pair => Function.update pair.1 point (target,pair.2)) =
      (PMF.uniformOfFintype ((Domain → Prefix × Tail) × Tail)).map
      (fun pair => Function.update pair.1 point (target,(pair.1 point).2)) := by
    calc
      _ = (PMF.uniformOfFintype ((Domain → Prefix × Tail) × Tail)).map
          ((fun pair => Function.update pair.1 point (target,(pair.1 point).2)) ∘ tailExchange point) := by
        congr 1
        funext pair
        simp only [Function.comp_def, tailExchange, Equiv.coe_fn_mk, Function.update_self, Function.update_idem]
      _ = _ := by rw [← PMF.map_comp, transported]
  rw [uniform_product] at invariant
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def] at invariant
  have drop (table : Domain → Prefix × Tail) : (PMF.uniformOfFintype Tail).map
      (fun _ => Function.update table point (target,(table point).2)) =
        PMF.pure (Function.update table point (target,(table point).2)) := PMF.map_const _ _
  simp_rw [drop] at invariant
  calc
    _ = (PMF.uniformOfFintype (Domain → Prefix × Tail)).bind (fun table =>
        (PMF.uniformOfFintype Tail).map (fun tail => Function.update table point (target,tail))) := by
      have simpaTerm := PMF.bind_comm (PMF.uniformOfFintype Tail) (PMF.uniformOfFintype (Domain → Prefix × Tail)) (fun tail table => PMF.pure (Function.update table point (target,tail)))
      (try simp only [PMF.map] at simpaTerm ⊢)
      exact simpaTerm
    _ = _ := invariant

end PointProgramming

/-! W3 exact complete-joint re-sampling, including both programmed wallet functions and wallet data. -/
namespace W3
open ProbabilityTools
variable {Entropy Passphrase Seed Check Tail Wallet : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Wallet]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Wallet]
abbrev STable := Entropy × Passphrase → Seed
abbrev TTable := Seed → Check × Tail
abbrev Omega := Seed → Wallet
abbrev Observation := Entropy × Entropy × Seed × (STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)) ×
  (TTable (Seed := Seed) (Check := Check) (Tail := Tail)) × (Omega (Seed := Seed) (Wallet := Wallet)) × Wallet

def tagOriginal (seed : Seed) (target : Check) : PMF (TTable (Seed := Seed) (Check := Check) (Tail := Tail)) :=
  (PMF.uniformOfFintype Tail).bind fun tail =>
    (PMF.uniformOfFintype (TTable (Seed := Seed) (Check := Check) (Tail := Tail))).map fun table => Function.update table seed (target,tail)

def tagProgrammed (seed : Seed) (target : Check) : PMF (TTable (Seed := Seed) (Check := Check) (Tail := Tail)) :=
  (PMF.uniformOfFintype (TTable (Seed := Seed) (Check := Check) (Tail := Tail))).map fun table =>
    Function.update table seed (target,(table seed).2)

def omegaOriginal (seed : Seed) : PMF ((Omega (Seed := Seed) (Wallet := Wallet)) × Wallet) :=
  (PMF.uniformOfFintype (Omega (Seed := Seed) (Wallet := Wallet))).map fun table => (table,table seed)

def omegaProgrammed (seed : Seed) : PMF ((Omega (Seed := Seed) (Wallet := Wallet)) × Wallet) :=
  (PMF.uniformOfFintype Wallet).bind fun wallet =>
    (PMF.uniformOfFintype (Omega (Seed := Seed) (Wallet := Wallet))).map fun table => (Function.update table seed wallet,wallet)

def payload (tagLaw : PMF (TTable (Seed := Seed) (Check := Check) (Tail := Tail)))
    (walletLaw : PMF ((Omega (Seed := Seed) (Wallet := Wallet)) × Wallet))
    (q : Passphrase) (s : STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)) (e y : Entropy) (seed : Seed) :
    PMF (Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Wallet := Wallet)) :=
  tagLaw.bind fun t => walletLaw.map fun pair => (e,y,seed,Function.update s (e,q) seed,t,pair.1,pair.2)

omit [Fintype Entropy] [Nonempty Entropy] [Nonempty Seed] in
/-- The tag suffix and wallet-data replacements preserve the full functions, not only their selected values. -/
theorem payload_eq (q : Passphrase) (s : STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))
    (e y : Entropy) (seed : Seed) (target : Check) :
    payload (tagOriginal (Tail := Tail) seed target) (omegaOriginal (Wallet := Wallet) seed) q s e y seed =
      payload (tagProgrammed (Tail := Tail) seed target) (omegaProgrammed (Wallet := Wallet) seed) q s e y seed := by
  unfold tagOriginal tagProgrammed omegaOriginal omegaProgrammed
  rw [PointProgramming.suffix, PointProgramming.value]

def original (cipher : Equiv.Perm Entropy) (q : Passphrase) (target : Check)
    (s : STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)) :
    PMF (Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Wallet := Wallet)) :=
  (PMF.uniformOfFintype Entropy).bind fun e => (PMF.uniformOfFintype Seed).bind fun seed =>
    payload (tagOriginal (Tail := Tail) seed target) (omegaOriginal (Wallet := Wallet) seed) q s e (cipher e) seed

def programmed (cipher : Equiv.Perm Entropy) (q : Passphrase) (target : Check)
    (s : STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)) :
    PMF (Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Wallet := Wallet)) :=
  (PMF.uniformOfFintype Entropy).bind fun y => (PMF.uniformOfFintype Seed).bind fun seed =>
    payload (tagProgrammed (Tail := Tail) seed target) (omegaProgrammed (Wallet := Wallet) seed) q s (cipher.symm y) y seed

/-- E, Y, seed, S, T, Omega and omega retain exactly the source joint distribution. -/
theorem resampling (cipher : Equiv.Perm Entropy) (q : Passphrase) (target : Check)
    (s : STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)) :
    original (Tail := Tail) (Wallet := Wallet) cipher q target s = programmed (Tail := Tail) (Wallet := Wallet) cipher q target s := by
  unfold original programmed
  have uniform := Lemma2.uniform_permutation cipher
  conv_rhs => rw [← uniform, PMF.bind_map]
  simp only [Function.comp_def, Equiv.symm_apply_apply]
  congr 1
  funext e
  congr 1
  funext seed
  exact payload_eq q s e (cipher e) seed target

/-- Retain P, Q, A, B, H and any independently sampled S' by conditioning on their common environment. -/
theorem joint {Context : Type} (prior : PMF Context) (cipher : Context → Equiv.Perm Entropy)
    (q : Context → Passphrase) (target : Check)
    (s : Context → STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed)) :
    (prior.bind fun context => (original (Tail := Tail) (Wallet := Wallet) (cipher context) (q context) target (s context)).map fun observation => (context,observation)) =
    (prior.bind fun context => (programmed (Tail := Tail) (Wallet := Wallet) (cipher context) (q context) target (s context)).map fun observation => (context,observation)) := by
  congr 1
  funext context
  rw [resampling]

/-- The cipher parameter is the actual twelve-round MHFE Feistel permutation. -/
def suite3Cipher {Password : Type} (password : Password) (a : TableFactors.ATable Password)
    (b : TableFactors.BTable) (h : TableFactors.HTable) : Equiv.Perm Gamma2Model.State :=
  KnownPairModel.roundsEquiv (KnownPairModel.allMasks password a b h)

/-- Applying the concrete permutation is exactly the source cipher, without a random-permutation assumption. -/
theorem suite3_cipher {Password : Type} (password : Password) (a : TableFactors.ATable Password)
    (b : TableFactors.BTable) (h : TableFactors.HTable) (e : Gamma2Model.State) :
    suite3Cipher password a b h e = KnownPairModel.cipher password a b h e := rfl

end W3

/-! Exact sampling bridge from W2's combined planted wallet table to W3's complete-joint kernels. -/
namespace W3Source
open WalletGeneration WalletFinite TranscriptErasure ProbabilityTools
variable {Entropy Passphrase Seed Check Tail Wallet : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Wallet]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Wallet]
abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)

omit [DecidableEq Entropy] [DecidableEq Seed] in
/-- The selected entropy, seed and suffix really are independent uniform coordinates. -/
theorem selected_sampling :
    PMF.uniformOfFintype (Selected Entropy Seed Tail) =
    (PMF.uniformOfFintype Entropy).bind (fun e => (PMF.uniformOfFintype Seed).bind
      (fun seed => (PMF.uniformOfFintype Tail).map (fun tail => (⟨e,seed,tail⟩ : Selected Entropy Seed Tail)))) := by
  have transported := PMF.uniformOfFintype_map_of_bijective (selectedEquiv (Entropy := Entropy) (Seed := Seed) (Tail := Tail)).symm selectedEquiv.symm.bijective
  rw [← transported, uniform_product, uniform_product]
  simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def, selectedEquiv, Equiv.coe_fn_symm_mk]

omit [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] in
/-- Combined-table programming is exactly the two separate function updates used in W3. -/
theorem restore_split (q : Passphrase) (target : Check) (chosen : Selected Entropy Seed Tail)
    (s : W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))
    (t : W3.TTable (Seed := Seed) (Check := Check) (Tail := Tail)) :
    WalletTableFactors.split
      (restore q target (some chosen) (WalletTableFactors.split.symm (s,t))) =
      (Function.update s (chosen.entropy,q) chosen.seed,Function.update t chosen.seed (target,chosen.tail)) := by
  apply Prod.ext
  · funext pair
    rcases pair with ⟨e,v⟩
    simp only [WalletTableFactors.split, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, restore,
      Function.update_apply, Prod.mk.injEq]
  · funext seed
    simp only [WalletTableFactors.split, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, restore,
      Function.update_apply]

def observation (cipher : Equiv.Perm Entropy) (q : Passphrase) (target : Check)
    (chosen : Selected Entropy Seed Tail) (table : Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))
    (omega : W3.Omega (Seed := Seed) (Wallet := Wallet)) :
    W3.Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Wallet := Wallet) :=
  let programmed := WalletTableFactors.split (restore q target (some chosen) table)
  (chosen.entropy,cipher chosen.entropy,chosen.seed,programmed.1,programmed.2,omega,omega chosen.seed)

def original (cipher : Equiv.Perm Entropy) (q : Passphrase) (target : Check) :
    PMF (W3.Observation (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) (Wallet := Wallet)) :=
  (PMF.uniformOfFintype (Selected Entropy Seed Tail)).bind fun chosen =>
    (PMF.uniformOfFintype (Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))).bind fun table =>
      (PMF.uniformOfFintype (W3.Omega (Seed := Seed) (Wallet := Wallet))).map (observation cipher q target chosen table)

/-- This is the actual combined-table sampling law, not an assumed equivalence to W3.original. -/
theorem sampling (cipher : Equiv.Perm Entropy) (q : Passphrase) (target : Check) : original (Tail := Tail) (Wallet := Wallet) cipher q target =
      (PMF.uniformOfFintype (W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind
        (W3.original (Tail := Tail) (Wallet := Wallet) cipher q target) := by
  unfold original
  rw [WalletTableFactors.sampling, uniform_product]
  simp only [independentPair, PMF.bind_map, PMF.bind_bind, Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext s
  rw [selected_sampling]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  unfold W3.original W3.payload W3.tagOriginal W3.omegaOriginal
  simp only [PMF.bind_map, PMF.bind_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext e
  congr 1
  funext seed
  congr 1
  funext tail
  congr 1
  funext t
  congr 1
  funext omega
  unfold observation
  rw [restore_split]

/-- Source W3, including the original uniform S', full programmed functions and all selected values. -/
theorem resampling (cipher : Equiv.Perm Entropy) (q : Passphrase) (target : Check) : original (Tail := Tail) (Wallet := Wallet) cipher q target =
      (PMF.uniformOfFintype (W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind
        (W3.programmed (Tail := Tail) (Wallet := Wallet) cipher q target) := by
  rw [sampling]
  congr 1
  funext s
  exact W3.resampling cipher q target s

/-- Retain the whole P,Q,A,B,H environment; the concrete suite3Cipher supplies its fixed permutation. -/
theorem joint {Context : Type} (prior : PMF Context) (cipher : Context → Equiv.Perm Entropy)
    (q : Context → Passphrase) (target : Check) : (prior.bind fun context => (original (Tail := Tail) (Wallet := Wallet) (cipher context) (q context) target).map
      (fun observation => (context,observation))) =
    (prior.bind fun context => ((PMF.uniformOfFintype (W3.STable (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed))).bind
      (W3.programmed (Tail := Tail) (Wallet := Wallet) (cipher context) (q context) target)).map
      (fun observation => (context,observation))) := by
  congr 1
  funext context
  rw [resampling]

end W3Source

end
end MhfeLean
