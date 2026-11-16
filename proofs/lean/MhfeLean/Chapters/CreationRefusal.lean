import MhfeLean.Chapters.KnownPairBound
import MhfeLean.Chapters.ShortSources
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # Creation refusal for the known-pair and short-source bounds
-/

/-! The actual known-pair source law with first creation refusal, retaining the complete H-independent context. -/
namespace KnownPairRefusal
open Gamma2Model TableFactors
variable {N : Nat} {Entropy : Type} [Fintype Entropy] [DecidableEq Entropy]
attribute [local instance] FiniteBits.fintype
abbrev Context := Fin N × DeltaInputs.Others (Fin N) Entropy

def initial (passwords : PMF (Fin N)) :=
  ExactRefusalLift.initial (DeltaInputs.environments (Entropy := Entropy) passwords)
    CryptoUniform.h

def score (source : State) (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N))
    (sample : Context (N := N) (Entropy := Entropy) × HTable) : Bool :=
  let env := sample.1
  decide ((execute (DeltaInputs.tables env.2 sample.2)
    (adversary (KnownPairModel.cipher env.1 env.2.1 env.2.2.1 sample.2 source))).1=env.1)

/-- Exactly the existing Delta0 experiment; the retained H sampler has not been replaced. -/
theorem original (source : State) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N)) :
    KnownPairSource.original source passwords adversary=
      ((initial passwords).map (score source adversary)) := by
  simp only [KnownPairSource.original,K1.realGame,PMF.pure_bind,initial,
    ExactRefusalLift.initial,CryptoUniform.h,PMF.map_bind,PMF.map_comp,Function.comp_def,
    KnownPairTransfer.score,K1.real,score,DeltaInputs.tables]
  rfl

def refused (source : State) (sample : Context (N := N) (Entropy := Entropy) × HTable) : Bool :=
  ExactRefusalLift.refused (fun env h =>
    KnownPairModel.cipher env.1 env.2.1 env.2.2.1 h source) (fun _ => source) sample

theorem probability (source : State) (passwords : PMF (Fin N)) : ((initial (Entropy := Entropy) passwords).map (refused source)) true=(2^256:ENNReal)⁻¹ :=
  G9Game.probability (DeltaInputs.environments passwords)
    (fun env => env.1) (fun env => env.2.1) (fun env => env.2.2.1) (fun _ => source)

def game (source : State) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N))
    (later : Context (N := N) (Entropy := Entropy) × HTable → PMF Bool) : PMF Bool :=
  RefusalResponse.game (initial passwords) (refused source) (score source adversary) later

end KnownPairRefusal

/-! Theorem 4 retains its fractional credit and explicit epsilon_K after the actual first creation refusal. -/
namespace Theorem4Refused
open Gamma2Model TableFactors KnownPairRefusal
variable {N : Nat} {Entropy : Type} [Fintype Entropy] [DecidableEq Entropy]

theorem bound (source : State) (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) Entropy) (Fin N))
    (later : Context (N := N) (Entropy := Entropy) × HTable → PMF Bool)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH) :
    (game source passwords adversary later) true ≤
      KnownPairMass.value passwords kA+
        (24*p1*kA+2*qB+419)/(2^128:ENNReal)+(2*qH+12)/(2^256:ENNReal)+(2^256:ENNReal)⁻¹ := by
  have base := Theorem4.bound source passwords sorted adversary p1 largest kA qB qH budgetA budgetB budgetH
  rw [original] at base
  have result := RefusalResponse.bound (initial passwords) (refused source) (score source adversary) later _ base
  rw [probability] at result
  exact result

end Theorem4Refused

/-! Retain source entropy and G when moving the short-source game's independent H sampler to the end. -/
namespace ShortSourceEnvironment
open Gamma2Model TableFactors CryptoInputs ProbabilityTools
variable {N : Nat} {E V R Result : Type}
attribute [local instance] FiniteBits.fintype
abbrev AB := ATable (Fin N) × BTable
abbrev Context := Fin N × AB (N := N) × (E × GTable E)

def packed (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (context : Context (N := N) (E := E)) : State :=
  state (context.2.2.1,(hash (context.2.2.2 context.2.2.1)).1)

def crypto (context : Context (N := N) (E := E)) (h : HTable) : Tables (Fin N) E :=
  ⟨context.2.1.1,context.2.1.2,h,context.2.2.2⟩

def score (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (adversary : State → OracleComp (spec (Fin N) E) Result)
    (test : Fin N → E → Result → Bool) (sample : Context (N := N) (E := E) × HTable) : Bool :=
  let ctx := sample.1
  test ctx.1 ctx.2.2.1 (execute (crypto ctx sample.2)
    (adversary (KnownPairModel.cipher ctx.1 ctx.2.1.1 ctx.2.1.2 sample.2 (packed state hash ctx)))).1

variable [DecidableEq E] [Fintype E] [Nonempty E]

def contexts (passwords : PMF (Fin N)) : PMF (Context (N := N) (E := E)) :=
  passwords.bind fun password => (PMF.uniformOfFintype (AB (N := N))).bind fun ab =>
    (PMF.uniformOfFintype (E × GTable E)).map fun input => (password,ab,input)

def initial (passwords : PMF (Fin N)) :=
  ExactRefusalLift.initial (contexts (E := E) passwords) CryptoUniform.h

private def regroup : ((AB (N := N)) × HTable) ≃ ABH (Fin N) := Equiv.prodAssoc _ _ _

private theorem factor : PMF.uniformOfFintype (ABH (Fin N))= (PMF.uniformOfFintype (AB (N := N))).bind fun ab =>
      (CryptoUniform.h).map fun h => (ab.1,ab.2,h) := by
  have transported := PMF.uniformOfFintype_map_of_bijective
    (regroup (N := N)) (regroup (N := N)).bijective
  rw [← transported,uniform_product]
  simp only [independentPair,PMF.map_bind,PMF.map_comp,Function.comp_def,regroup,CryptoUniform.h]
  rfl

/-- Password success is scored on the actual packed short source, preserving the G table that supplied its verifier. -/
theorem password_original [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
    (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) (Fin N)) :
    Theorem3.original state hash passwords adversary=
      ((initial passwords).map (score state hash adversary (fun password _ result => decide (result=password)))) := by
  unfold Theorem3.original
  rw [factor]
  unfold initial ExactRefusalLift.initial contexts
  simp only [PMF.map_bind,PMF.map_comp,PMF.bind_bind,PMF.bind_map,Function.comp_def,score,crypto,packed,
    Theorem3.score,CoordinateResampling.original,Theorem3.cipher,tables]
  apply congrArg (fun next => passwords.bind next)
  funext password
  apply congrArg (fun next => (PMF.uniformOfFintype (AB (N := N))).bind next)
  funext ab
  exact PMF.bind_comm _ _ _

/-- Source recovery is scored against the sampled E, not against an unrelated inverse of the container. -/
theorem entropy_original [Fintype V] [Nonempty V] [Fintype R] [Nonempty R] (state : (E × V) ≃ State)
    (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) E) :
    G6.original state hash passwords adversary=
      ((initial passwords).map (score state hash adversary (fun _ entropy result => decide (result=entropy)))) := by
  unfold G6.original
  simp only [PMF.map_comp,Function.comp_def,G6.score,G6.sampled_source]
  rw [factor]
  unfold initial ExactRefusalLift.initial contexts
  simp only [PMF.map_bind,PMF.map_comp,PMF.bind_bind,PMF.bind_map,Function.comp_def,score,crypto,packed,
    CoordinateResampling.original,Theorem3.cipher,tables]
  apply congrArg (fun next => passwords.bind next)
  funext password
  apply congrArg (fun next => (PMF.uniformOfFintype (AB (N := N))).bind next)
  funext ab
  exact PMF.bind_comm _ _ _

end ShortSourceEnvironment

/-! Creation refusal for uniformly generated short sources with their actual packed verifiers. -/
namespace ShortSourceRefusal
open Gamma2Model TableFactors ShortSourceEnvironment
variable {N : Nat} {E V R Result : Type}

def refused (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (sample : Context (N := N) (E := E) × HTable) : Bool :=
  ExactRefusalLift.refused (fun context h =>
    KnownPairModel.cipher context.1 context.2.1.1 context.2.1.2 h (packed state hash context))
    (packed state hash) sample

variable [DecidableEq E] [Fintype E] [Nonempty E]
attribute [local instance] FiniteBits.fintype

/-- The packed source may depend on G; the only required independence is from H. -/
theorem probability (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N)) :
    ((initial passwords).map (refused state hash)) true=(2^256:ENNReal)⁻¹ :=
  G9Game.probability (contexts passwords) (fun context => context.1)
    (fun context => context.2.1.1) (fun context => context.2.1.2) (packed state hash)

def game (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) Result) (test : Fin N → E → Result → Bool)
    (later : Context (N := N) (E := E) × HTable → PMF Bool) : PMF Bool :=
  RefusalResponse.game (initial passwords) (refused state hash) (score state hash adversary test) later

theorem bound (state : (E × V) ≃ State) (hash : Hash ≃ V × R) (passwords : PMF (Fin N))
    (adversary : State → OracleComp (spec (Fin N) E) Result) (test : Fin N → E → Result → Bool)
    (later : Context (N := N) (E := E) × HTable → PMF Bool) (upper : ENNReal)
    (original : ((initial passwords).map (score state hash adversary test)) true ≤ upper) :
    (game state hash passwords adversary test later) true ≤ upper+(2^256:ENNReal)⁻¹ := by
  have result := RefusalResponse.bound (initial passwords) (refused state hash)
    (score state hash adversary test) later upper original
  rw [probability] at result
  exact result

end ShortSourceRefusal

/-! Theorem 3 and G6 retain their exact main terms after first creation refusal. -/
namespace ShortSourceRefusedBounds
open Gamma2Model TableFactors ShortSourceEnvironment ShortSourceRefusal
variable {N : Nat} {E V R : Type} [DecidableEq E] [Fintype E] [Nonempty E]
  [Fintype V] [Nonempty V] [Fintype R] [Nonempty R]
attribute [local instance] FiniteBits.fintype

theorem password (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy state input)=input.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) E) (Fin N))
    (later : Context (N := N) (E := E) × HTable → PMF Bool)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH)
    (budgetG : ∀ container tables,(execute tables (adversary container)).2.countP G4Programs.isG ≤ qG) :
    (game state hash passwords adversary (fun password _ result => decide (result=password)) later) true ≤
      RankedMass.top passwords (kA/12+1)+(qG+qB+12*p1*kA+66)/(2^128:ENNReal)+
        qH/(2^256:ENNReal)+(2^256:ENNReal)⁻¹ := by
  have base := Theorem3.bound state hash firstHalf projects passwords sorted adversary p1 largest kA qB qH qG
    budgetA budgetB budgetH budgetG
  rw [password_original] at base
  exact ShortSourceRefusal.bound state hash passwords adversary _ later _ base

theorem entropy (state : (E × V) ≃ State) (hash : Hash ≃ V × R)
    (firstHalf : E → Half) (projects : ∀ input,firstHalf (Theorem3.entropy state input)=input.1)
    (passwords : PMF (Fin N)) (sorted : Antitone passwords)
    (adversary : State → OracleComp (spec (Fin N) E) E)
    (later : Context (N := N) (E := E) × HTable → PMF Bool)
    (p1 : ENNReal) (largest : ∀ password,passwords password ≤ p1) (kA qB qH qG : Nat)
    (budgetA : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isA ≤ kA)
    (budgetB : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isB ≤ qB)
    (budgetH : ∀ container tables,(execute tables (adversary container)).2.countP QueryCounts.isH ≤ qH)
    (budgetG : ∀ container tables,(execute tables (adversary container)).2.countP G4Programs.isG ≤ qG) :
    (game state hash passwords adversary (fun _ entropy result => decide (result=entropy)) later) true ≤
      RankedMass.top passwords (kA/12)+(qG+1+qB+12*p1*kA+66)/(2^128:ENNReal)+
        qH/(2^256:ENNReal)+(2^256:ENNReal)⁻¹ := by
  have base := G6.bound state hash firstHalf projects passwords sorted adversary p1 largest kA qB qH qG
    budgetA budgetB budgetH budgetG
  rw [entropy_original] at base
  exact ShortSourceRefusal.bound state hash passwords adversary _ later _ base

end ShortSourceRefusedBounds

end
end MhfeLean
