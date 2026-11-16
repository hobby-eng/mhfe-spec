/- long: the actual disclosure games, bad-event accounting and Theorem 2 stay together. -/
-- long: Theorem2 keeps its actual oracle games, coupling and probability assembly in one readable argument.
import MhfeLean.Chapters.Deniability
import MhfeLean.Chapters.DeniabilityModel
import MhfeLean.Chapters.WalletMatching

namespace MhfeLean
noncomputable section

/-! # Deniability games and their bad-event bounds

A public observation is generated from the ciphertext and the public oracles.
Its finite query sets retain the disclosed password, actual guessed passwords,
H keys and wallet lookups. Hidden source keys are those of the real forward run.
-/

namespace DeniabilityBound
open DeniabilityModel ProbabilityTools
open GameExpectation MomentTools
variable {width : Nat}
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] DeniabilityPrivate.key DeniabilityPrivate.cipher

structure Footprint (Password Phrase : Type) (k q l : Nat) where
  disclosed : Password
  guesses : Finset Password
  guesses_le : guesses.card ≤ k
  hKeys : Finset Key
  hKeys_le : hKeys.card ≤ q+12
  lookups : Finset Phrase
  lookups_le : lookups.card ≤ l

structure Trial (Password Entropy Phrase : Type) (k q l : Nat) where
  password : Password
  entropy : Entropy
  inner : (DeniabilityPrivate.World width)
  view : Footprint Password Phrase k q l

variable {Password Entropy Phrase : Type} [DecidableEq Password] [DecidableEq Phrase]
  [Fintype Entropy] [Nonempty Entropy] {k q l : Nat}

/-- The public observer receives Y, not the hidden password, entropy or source keys. -/
def worlds (passwords : PMF Password) (b : (BTable width)) (pack : Entropy → (State width))
    (observe : (State width) → PMF (Footprint Password Phrase k q l)) : PMF ((Trial (width := width)) Password Entropy Phrase k q l) :=
  passwords.bind fun password => (PMF.uniformOfFintype Entropy).bind fun entropy =>
    (PMF.uniformOfFintype (DeniabilityPrivate.World width)).bind fun inner =>
      (observe (DeniabilityPrivate.cipher b (pack entropy) inner)).map fun view =>
        ⟨password, entropy, inner, view⟩

/-- A finite set costs at most its cardinality times the largest point probability. -/
private theorem set_hit {Value : Type} [DecidableEq Value] (law : PMF Value) (maximum : ENNReal)
    (largest : ∀ value, law value ≤ maximum) (chosen : Finset Value) (limit : Nat)
    (size : chosen.card ≤ limit) :
    moment law (fun value => if value ∈ chosen then 1 else 0) ≤ (limit:ENNReal)*maximum := by
  rw [PairMass.finite_membership]
  calc
    _ ≤ ∑ _ ∈ chosen, maximum := Finset.sum_le_sum (fun value _ => largest value)
    _ = (chosen.card:ENNReal)*maximum := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_left (by exact_mod_cast size) _

private theorem uniform_hit {Value : Type} [Fintype Value] [Nonempty Value] [DecidableEq Value]
    (chosen : Finset Value) (limit : Nat) (size : chosen.card ≤ limit) :
    moment (PMF.uniformOfFintype Value) (fun value => if value ∈ chosen then 1 else 0) ≤
      (limit:ENNReal)/(Fintype.card Value:ENNReal) := by
  have estimate := set_hit (PMF.uniformOfFintype Value) (Fintype.card Value:ENNReal)⁻¹
    (fun value => by rw [PMF.uniformOfFintype_apply]) chosen limit size
  simpa only [div_eq_mul_inv] using estimate

omit [DecidableEq Password] [DecidableEq Phrase] in
/-- Forgetting private keys leaves an independent uniform ciphertext for every raw source. -/
theorem public_moment (passwords : PMF Password) (b : (BTable width))
    (pack : Entropy → (State width))
    (observe : (State width) → PMF (Footprint Password Phrase k q l))
    (value : Password → Entropy → Footprint Password Phrase k q l → ENNReal) :
    moment (worlds passwords b pack observe) (fun trial => value trial.password trial.entropy trial.view) =
      moment passwords (fun password => moment (PMF.uniformOfFintype Entropy) (fun entropy =>
        moment (PMF.uniformOfFintype (State width)) (fun container =>
          moment (observe container) (value password entropy)))) := by
  simp only [worlds, MomentTools.bind, moment_map, Function.comp_def]
  apply congrArg (moment passwords)
  funext password
  apply congrArg (moment (PMF.uniformOfFintype Entropy))
  funext entropy
  have projected := congrArg
    (fun law : PMF (State width) => moment law (fun container => moment (observe container) (value password entropy)))
    (DeniabilityPrivate.cipher_uniform b (pack entropy))
  simpa only [moment_map, Function.comp_def] using projected

omit [DecidableEq Phrase] in
/-- Q and the attacker's distinct A-passwords are guessed independently of the real P. -/
theorem password_bound (passwords : PMF Password) (p1 : ENNReal)
    (largest : ∀ password, passwords password ≤ p1) (b : (BTable width)) (pack : Entropy → (State width))
    (observe : (State width) → PMF (Footprint Password Phrase k q l)) :
    moment (worlds passwords b pack observe) (fun trial =>
      if trial.password ∈ insert trial.view.disclosed trial.view.guesses then 1 else 0) ≤
        ((k+1:Nat):ENNReal)*p1 := by
  rw [public_moment passwords b pack observe
    (fun password _ view => if password ∈ insert view.disclosed view.guesses then 1 else 0)]
  simp only [constant]
  rw [G8Transport.comm]
  apply bounded
  intro container
  rw [G8Transport.comm]
  apply bounded
  intro view
  apply set_hit passwords p1 largest
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right view.guesses_le 1)

omit [DecidableEq Password] in
/-- Injective phrase encoding turns at most l public guesses into at most l entropy candidates. -/
theorem lookup_bound (passwords : PMF Password) (b : (BTable width)) (pack : Entropy → (State width))
    (observe : (State width) → PMF (Footprint Password Phrase k q l))
    (phrase : Entropy → Phrase) (injective : Function.Injective phrase) :
    moment (worlds passwords b pack observe) (fun trial =>
      if phrase trial.entropy ∈ trial.view.lookups then 1 else 0) ≤
        (l:ENNReal)/(Fintype.card Entropy:ENNReal) := by
  classical
  rw [public_moment passwords b pack observe
    (fun _ entropy view => if phrase entropy ∈ view.lookups then 1 else 0)]
  simp only [constant]
  rw [G8Transport.comm]
  apply bounded
  intro container
  rw [G8Transport.comm]
  apply bounded
  intro view
  let candidates := Finset.univ.filter (fun entropy => phrase entropy ∈ view.lookups)
  have included : candidates.image phrase ⊆ view.lookups := by
    intro value member
    obtain ⟨entropy, within, equal⟩ := Finset.mem_image.mp member
    exact equal ▸ (Finset.mem_filter.mp within).2
  have size : candidates.card ≤ l := by
    calc
      _ = (candidates.image phrase).card := (Finset.card_image_of_injective candidates injective).symm
      _ ≤ view.lookups.card := Finset.card_le_card included
      _ ≤ l := view.lookups_le
  have estimate := uniform_hit candidates l size
  simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using estimate

omit [DecidableEq Password] [DecidableEq Phrase] in
/-- One actual source key stays independent of any subsequent public observation of Y. -/
theorem observed_key (b : (BTable width)) (source : (State width)) (round : Fin 12)
    (observe : (State width) → PMF (Footprint Password Phrase k q l)) :
    ((PMF.uniformOfFintype (DeniabilityPrivate.World width)).bind fun inner =>
      (observe (DeniabilityPrivate.cipher b source inner)).map fun view =>
        (DeniabilityPrivate.key b source inner round, view)) =
      independentPair (PMF.uniformOfFintype Key) ((PMF.uniformOfFintype (State width)).bind observe) := by
  set_option maxRecDepth 3000 in
  have coupled := congrArg (fun law : PMF ((State width) × Key) => law.bind fun pair =>
      (observe pair.1).map fun view => (pair.2, view))
    (DeniabilityPrivate.hidden_key b source round)
  simp only [PMF.bind_map, independentPair, PMF.bind_bind, PMF.map_bind, Function.comp_def] at coupled ⊢
  exact coupled.trans (PMF.bind_comm _ _ _)

omit [DecidableEq Password] [DecidableEq Phrase] in
/-- A key guess is charged against all public H calls, including the twelve decoy-recovery calls. -/
theorem round_bound (b : (BTable width)) (source : (State width)) (round : Fin 12)
    (observe : (State width) → PMF (Footprint Password Phrase k q l)) :
    moment (PMF.uniformOfFintype (DeniabilityPrivate.World width)) (fun inner =>
      moment (observe (DeniabilityPrivate.cipher b source inner)) (fun view =>
        if DeniabilityPrivate.key b source inner round ∈ view.hKeys then 1 else 0)) ≤
      ((q+12:Nat):ENNReal)/(Fintype.card Key:ENNReal) := by
  have law := congrArg
    (fun distribution : PMF (Key × Footprint Password Phrase k q l) =>
      moment distribution (fun pair => if pair.1 ∈ pair.2.hKeys then 1 else 0))
    (observed_key b source round observe)
  have left : moment ((PMF.uniformOfFintype (DeniabilityPrivate.World width)).bind fun inner =>
      (observe (DeniabilityPrivate.cipher b source inner)).map fun view =>
        (DeniabilityPrivate.key b source inner round, view))
      (fun pair => if pair.1 ∈ pair.2.hKeys then 1 else 0) =
      moment (PMF.uniformOfFintype (DeniabilityPrivate.World width)) (fun inner =>
        moment (observe (DeniabilityPrivate.cipher b source inner)) (fun view =>
          if DeniabilityPrivate.key b source inner round ∈ view.hKeys then 1 else 0)) := by
    rw [MomentTools.bind]
    simp only [moment_map, Function.comp_def]
  try dsimp only at law
  rw [left] at law
  rw [law, independentPair, MomentTools.bind]
  simp only [moment_map, Function.comp_def]
  rw [G8Transport.comm]
  apply bounded
  intro view
  exact uniform_hit view.hKeys (q+12) view.hKeys_le

omit [DecidableEq Password] [DecidableEq Phrase] in
/-- All twelve actual hidden keys are charged separately; they need not be mutually independent. -/
theorem keys_bound (passwords : PMF Password) (b : (BTable width)) (pack : Entropy → (State width))
    (observe : (State width) → PMF (Footprint Password Phrase k q l)) :
    moment (worlds passwords b pack observe) (fun trial =>
      if ∃ round : Fin 12, DeniabilityPrivate.key b (pack trial.entropy) trial.inner round ∈ trial.view.hKeys
      then 1 else 0) ≤ 12*((q+12:Nat):ENNReal)/(Fintype.card Key:ENNReal) := by
  classical
  calc
    _ ≤ moment (worlds passwords b pack observe) (fun trial => ∑ round : Fin 12,
        if DeniabilityPrivate.key b (pack trial.entropy) trial.inner round ∈ trial.view.hKeys
        then 1 else 0) := by
      apply mono
      intro trial
      split_ifs with witness
      · have estimate := G3Sums.one_le_indicator_sum
          (fun round : Fin 12 => decide (DeniabilityPrivate.key b (pack trial.entropy) trial.inner round ∈ trial.view.hKeys))
          (by obtain ⟨round, found⟩ := witness; exact ⟨round, decide_eq_true found⟩)
        simpa only [decide_eq_true_eq] using estimate
      · exact zero_le
    _ = ∑ round : Fin 12, moment (worlds passwords b pack observe) (fun trial =>
        if DeniabilityPrivate.key b (pack trial.entropy) trial.inner round ∈ trial.view.hKeys
        then 1 else 0) := finite_sum _ _
    _ ≤ ∑ _round : Fin 12, ((q+12:Nat):ENNReal)/(Fintype.card Key:ENNReal) := by
      apply Finset.sum_le_sum
      intro round _
      simp only [worlds, MomentTools.bind, moment_map, Function.comp_def]
      apply bounded
      intro password
      apply bounded
      intro entropy
      exact round_bound b (pack entropy) round observe
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_div_assoc, Nat.cast_ofNat]

/-- Password, phrase and actual-key exclusions depend only on the retained source signature. -/
def signatureBad (real : Password) (phrase : Phrase) (keys : Fin 12 → Key)
    (view : Footprint Password Phrase k q l) : Bool :=
  decide (real ∈ insert view.disclosed view.guesses ∨ phrase ∈ view.lookups ∨
    ∃ round : Fin 12, keys round ∈ view.hKeys)

/-- The erased experiment's complete bad event uses only the actual hidden source and query sets. -/
def bad (b : (BTable width)) (pack : Entropy → (State width)) (phrase : Entropy → Phrase)
    (trial : (Trial (width := width)) Password Entropy Phrase k q l) : Bool :=
  signatureBad trial.password (phrase trial.entropy)
    (DeniabilityPrivate.key b (pack trial.entropy) trial.inner) trial.view

/-- The middle hop's full error, before the password redraw and the two creation refusals. -/
theorem bad_bound (passwords : PMF Password) (p1 : ENNReal)
    (largest : ∀ password, passwords password ≤ p1) (b : (BTable width))
    (pack : Entropy → (State width))
    (observe : (State width) → PMF (Footprint Password Phrase k q l)) (phrase : Entropy → Phrase)
    (injective : Function.Injective phrase) :
    ((worlds passwords b pack observe).map (bad b pack phrase)) true ≤
      ((k+1:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal) := by
  classical
  have union : moment (worlds passwords b pack observe)
      (fun trial => if bad b pack phrase trial then 1 else 0) ≤
      moment (worlds passwords b pack observe) (fun trial =>
        (if trial.password ∈ insert trial.view.disclosed trial.view.guesses then 1 else 0)+
        (if phrase trial.entropy ∈ trial.view.lookups then 1 else 0)+
        (if ∃ round : Fin 12, DeniabilityPrivate.key b (pack trial.entropy) trial.inner round ∈ trial.view.hKeys
          then 1 else 0)) := by
    apply mono
    intro trial
    simp only [bad, signatureBad, decide_eq_true_eq]
    split_ifs <;> simp_all
  rw [MomentTools.add, MomentTools.add] at union
  have keycard : Fintype.card Key = 2^256 :=
    (Fintype.card_congr (Lemma3.bitEquivFin 256)).trans (Fintype.card_fin _)
  have keys := keys_bound passwords b pack observe
  rw [keycard, Nat.cast_pow, Nat.cast_ofNat] at keys
  rw [probability]
  exact union.trans (add_le_add (add_le_add (password_bound passwords p1 largest b pack observe)
    (lookup_bound passwords b pack observe phrase injective)) keys)

end DeniabilityBound

namespace DeniabilityRows
open DeniabilityModel ProbabilityTools
variable {width : Nat}
variable {Password : Type} [DecidableEq Password]
attribute [local instance] FiniteBits.fintype

abbrev Row := Salt → Key

def replace (password : Password) (table : ATable Password) (row : Row) : ATable Password :=
  fun point => if point.1=password then row point.2 else table point

/-- Swapping a whole selected row with an independent spare row is an involution. -/
def swap (password : Password) : Equiv.Perm (ATable Password × Row) where
  toFun pair := (replace password pair.1 pair.2, fun salt => pair.1 (password,salt))
  invFun pair := (replace password pair.1 pair.2, fun salt => pair.1 (password,salt))
  left_inv := by
    intro pair
    apply Prod.ext
    · funext point
      by_cases same : point.1=password
      · simp only [replace, if_pos same]
        exact congrArg pair.1 (Prod.ext same.symm rfl)
      · simp only [replace, if_neg same]
    · funext salt
      simp only [replace, if_true]
  right_inv := by
    intro pair
    apply Prod.ext
    · funext point
      by_cases same : point.1=password
      · simp only [replace, if_pos same]
        exact congrArg pair.1 (Prod.ext same.symm rfl)
      · simp only [replace, if_neg same]
    · funext salt
      simp only [replace, if_true]

variable [Fintype Password]

/-- The old private row and the entire public replacement table have independent uniform laws. -/
theorem joint (password : Password) :
    (PMF.uniformOfFintype (ATable Password × Row)).map
      (fun pair => (fun salt => pair.1 (password,salt), replace password pair.1 pair.2)) =
    independentPair (PMF.uniformOfFintype Row) (PMF.uniformOfFintype (ATable Password)) := by
  calc
    _ = ((PMF.uniformOfFintype (ATable Password × Row)).map (swap password)).map Prod.swap := by
      rw [PMF.map_comp]
      rfl
    _ = (PMF.uniformOfFintype (ATable Password × Row)).map Prod.swap := by
      rw [PMF.uniformOfFintype_map_of_bijective (swap password) (swap password).bijective]
    _ = PMF.uniformOfFintype (Row × ATable Password) :=
      PMF.uniformOfFintype_map_of_bijective (Equiv.prodComm _ _) (Equiv.prodComm _ _).bijective
    _ = _ := uniform_product

end DeniabilityRows

namespace DeniabilitySource
open DeniabilityModel ProbabilityTools
open DeniabilityPrivate
variable {width : Nat}
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] DeniabilityModel.forward

/-- Exactly the information retained from the private source: Y and its twelve actual H keys. -/
abbrev Signature (width : Nat) := (State width) × (Fin 12 → Key)

def signature
    (trace : (DeniabilityPrivateOracle.SourceResult width) × List (DeniabilityModel.HInput width)) :
    (Signature width) :=
  (trace.1.1.1, fun round => match trace.1.2.getD (3*round.val+2) fallbackPoint with
    | .h key _ _ => key
    | _ => 0)

variable (row : Salt → Key) (b : (BTable width)) (source : (State width))

/-- The retained H-focused transcript recovers the cipher and actual round keys. -/
theorem signature_actual (h : (HTable width)) :
    signature (TranscriptErasure.execute h (DeniabilityPrivateOracle.sourceProgram row b source)) =
      (cipher b source (row,h), key b source (row,h)) := by
  unfold signature
  rw [DeniabilityPrivateOracle.source_result]
  apply Prod.ext
  · exact forward_cipher b source (row,h)
  · rfl

/-- Erasure makes the complete public H independent while preserving the actual source signature. -/
theorem erased_signature {Output : Type} (row : Salt → Key) (b : (BTable width))
    (source : (State width)) (observe : (Signature width) → (HTable width) → PMF Output) :
    (PMF.uniformOfFintype ((HTable width) × (HTable width))).bind (fun pair =>
      observe (cipher b source (row,pair.1), key b source (row,pair.1))
        (TranscriptErasure.exchanged (DeniabilityPrivateOracle.sourceProgram row b source) pair).2) =
    (PMF.uniformOfFintype ((HTable width) × (HTable width))).bind (fun pair =>
      observe (cipher b source (row,pair.1), key b source (row,pair.1)) pair.2) := by
  have law := DeniabilityPrivateOracle.erase_source row b source
    (fun trace shared => observe (signature trace) shared)
  simpa only [signature_actual] using law

/-- The source is the very same cipher as the existing ideal-oracle model, with the selected A row. -/
theorem actual_cipher {Password : Type} (password : Password) (a : Password × Salt → Key)
    (b : (BTable width)) (h : (HTable width)) (source : (State width)) :
    cipher b source (fun salt => a (password,salt),h) =
      DeniabilityModel.cipher password a b h source := rfl

private theorem getD_present {Value : Type} (values : List Value) (index : Nat) (fallback : Value) :
    values.getD index fallback ∈ values ∨ values.getD index fallback = fallback := by
  induction values generalizing index with
  | nil => exact Or.inr rfl
  | cons first rest ih =>
    cases index with
    | zero => exact Or.inl List.mem_cons_self
    | succ index =>
      rcases ih index with member | equal
      · exact Or.inl (List.mem_cons_of_mem _ member)
      · exact Or.inr equal

/-- Each genuine H point uses the key at the corresponding indexed source slot. -/
theorem genuine_key (b : (BTable width)) (source : (State width)) (world : (World width))
    (value : Key) (round : Fin 12) (right : Branch width)
    (member : Point.h value round right ∈ chain b source world) : value = key b source world round := by
  let selected := (chain b source world).filter (DeniabilityModel.hFor round)
  have size : selected.length = 1 := by
    rw [← List.countP_eq_length_filter]
    have simpaTerm := DeniabilityModel.forward_h_count () (crypto b world) 12 0 source (by omega) round
    (try simp only [Nat.zero_add,Nat.zero_le,true_and,if_pos round.isLt] at simpaTerm ⊢)
    exact simpaTerm
  obtain ⟨point, singleton⟩ := List.length_eq_one_iff.mp size
  have first : Point.h value round right ∈ selected := by
    simp only [selected, List.mem_filter, DeniabilityModel.hFor, decide_true, and_true]
    exact member
  obtain ⟨otherRight, block⟩ := h_block b world 12 0 source (by omega) round.val round.isLt
  have blockMember : (chain b source world).getD (3*round.val+2) fallbackPoint ∈ chain b source world := by
    rcases getD_present (chain b source world) (3*round.val+2) fallbackPoint with inside | fallback
    · exact inside
    · change (execute (crypto b world) (DeniabilityModel.forward () 12 0 source (by omega))).2.getD
        (3*round.val+2) fallbackPoint = fallbackPoint at fallback
      rw [block] at fallback
      cases fallback
  have second : (chain b source world).getD (3*round.val+2) fallbackPoint ∈ selected := by
    apply List.mem_filter.mpr
    refine ⟨blockMember, ?_⟩
    change DeniabilityModel.hFor round
      ((execute (crypto b world) (DeniabilityModel.forward () 12 0 source (by omega))).2.getD
        (3*round.val+2) fallbackPoint) = true
    rw [block]
    simp only [DeniabilityModel.hFor, Nat.zero_add, Fin.eta, decide_true]
  rw [singleton, List.mem_singleton] at first second
  have same := first.trans second.symm
  unfold key
  rw [← same]

/-- H-erasure changes only inputs whose keys occur in the genuine source trace. -/
theorem source_input_key (h : (HTable width)) (input : (DeniabilityModel.HInput width))
    (member : input ∈ (TranscriptErasure.execute h (DeniabilityPrivateOracle.sourceProgram row b source)).2) :
    input.1 = key b source (row,h) input.2.1 := by
  rw [DeniabilityPrivateOracle.source_trace] at member
  obtain ⟨point, inside, decoded⟩ := List.mem_filterMap.mp member
  cases point with
  | a password salt => cases decoded
  | b round right => cases decoded
  | g entropy => cases decoded
  | h value round right =>
    change some (value,round,right)=some input at decoded
    cases Option.some.inj decoded
    exact genuine_key b source (row,h) value round right inside

/-- A later H input missing every real source key has exactly its old table value. -/
theorem erased_value (h spare : (HTable width)) (input : (DeniabilityModel.HInput width))
    (safe : ∀ round : Fin 12, input.1 ≠ key b source (row,h) round) :
    (TranscriptErasure.exchanged (DeniabilityPrivateOracle.sourceProgram row b source)
      (h,spare)).2 input = h input := by
  have absent : input ∉ (TranscriptErasure.execute h
      (DeniabilityPrivateOracle.sourceProgram row b source)).2 := by
    intro member
    exact safe input.2.1 (source_input_key row b source h input member)
  simp only [TranscriptErasure.exchanged, if_neg absent]

end DeniabilitySource

namespace DeniabilityInteraction
attribute [local irreducible] DeniabilityModel.execute TranscriptErasure.execute
open DeniabilityModel
variable {width : Nat}
variable {Password Entropy Phrase Record : Type}

abbrev RecordSpec (Phrase Record : Type) : OracleSpec Phrase := fun _ => Record
abbrev FullSpec (Password Entropy Phrase Record : Type) :=
  combinedSpec (width := width) (Password := Password) (Entropy := Entropy) (RecordSpec Phrase Record)
abbrev Program (Password Entropy Phrase Record : Type) :=
  (State width) → Password → (State width) → Record → OracleComp ((FullSpec (width := width)) Password Entropy Phrase Record) Bool
abbrev Query (Password Entropy Phrase : Type) := (Point width) Password Entropy ⊕ Phrase

def aPassword : (Query (width := width)) Password Entropy Phrase → Option Password
  | .inl (.a password _) => some password
  | _ => none

def hKey : (Query (width := width)) Password Entropy Phrase → Option Key
  | .inl (.h value _ _) => some value
  | _ => none

def lookup : (Query (width := width)) Password Entropy Phrase → Option Phrase
  | .inr phrase => some phrase
  | _ => none

/-- A typed combined table answers crypto and record queries, but is never an argument to the attacker. -/
def table (base : (Tables width) Password Entropy) (records : Phrase → Record) :=
  combinedAnswer (RecordSpec Phrase Record) base records

def trace (program : (Program (width := width)) Password Entropy Phrase Record)
    (base : (Tables width) Password Entropy) (records : Phrase → Record)
    (container : (State width)) (password : Password) (recovered : (State width)) (record : Record) :=
  (TranscriptErasure.execute (table base records)
    (program container password recovered record)).2

variable [DecidableEq Password] [DecidableEq Phrase]

/-- k counts distinct A passwords; q and l count actual H and record queries, including repeats. -/
def Bounded (program : (Program (width := width)) Password Entropy Phrase Record) (k q l : Nat) : Prop :=
  ∀ base records container password recovered record,
    let queries := trace program base records container password recovered record
    (queries.filterMap aPassword).toFinset.card ≤ k ∧
    (queries.filterMap hKey).length ≤ q ∧ (queries.filterMap lookup).length ≤ l

structure Adversary (Password Entropy Phrase Record : Type) [DecidableEq Password] [DecidableEq Phrase]
    (k q l : Nat) where
  run : (Program (width := width)) Password Entropy Phrase Record
  bounded : Bounded run k q l

structure Run (Password Entropy Phrase Record : Type) where
  disclosed : Password
  recovered : (State width)
  record : Record
  result : Bool
  owner : List ((Point width) Password Entropy)
  adversary : List ((Query (width := width)) Password Entropy Phrase)

attribute [local irreducible] finalize

/-- One actual owner recovery; later arguments use its result and recorded queries as a whole. -/
def recover (base : (Tables width) Password Entropy) (password : Password) (container : (State width)) :=
  execute base (finalize password 12 container (by omega))

attribute [local irreducible] recover

def finish (program : (Program (width := width)) Password Entropy Phrase Record) (base : (Tables width) Password Entropy)
    (baseRecords : Phrase → Record) (phrase : (State width) → Phrase) (container : (State width))
    (password : Password) (record : Record) : (Run (width := width)) Password Entropy Phrase Record :=
  let recovered := recover base password container
  let records := PreparedDisclosure.overlay baseRecords (phrase recovered.1.1) record
  let actual := TranscriptErasure.execute (table base records)
    (program container password recovered.1.1 record)
  ⟨password, recovered.1.1, record, actual.1, recovered.2, actual.2⟩

/-- U sees only the disclosed phrase and supplies no oracle answers. -/
def opening (program : (Program (width := width)) Password Entropy Phrase Record) (base : (Tables width) Password Entropy)
    (baseRecords : Phrase → Record) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record)
    (container : (State width)) (password : Password) : PMF ((Run (width := width)) Password Entropy Phrase Record) :=
  let recovered := (recover base password container).1.1
  (usage (phrase recovered)).map (finish program base baseRecords phrase container password)

def ownerKey : (Point width) Password Entropy → Option Key
  | .h key _ _ => some key
  | _ => none

omit [DecidableEq Password] in
private theorem owner_key_count (base : (Tables width) Password Entropy) (password : Password)
    (container : (State width)) : ((recover base password container).2.filterMap ownerKey).length=12 := by
  have count (queries : List ((Point width) Password Entropy)) :
      (queries.filterMap ownerKey).length=queries.countP DeniabilityModel.isH := by
    rw [List.length_filterMap_eq_countP]
    congr 1
    funext point
    cases point <;> rfl
  rw [count, recover]
  exact DeniabilityModel.inverse_h_total password base 12 container (by omega)

/-- Turn already recorded queries into distinct-password/key/phrase sets with their budgets. -/
def collect {k q l : Nat} (password : Password) (owner : List Key)
    (queries : List ((Query (width := width)) Password Entropy Phrase)) (ownerLength : owner.length=12)
    (budget : (queries.filterMap aPassword).toFinset.card ≤ k ∧
      (queries.filterMap hKey).length ≤ q ∧ (queries.filterMap lookup).length ≤ l) :
    DeniabilityBound.Footprint Password Phrase k q l := by
  refine ⟨password, (queries.filterMap aPassword).toFinset, budget.1,
    (owner++queries.filterMap hKey).toFinset, ?_, (queries.filterMap lookup).toFinset, ?_⟩
  · calc
      _ ≤ (owner++queries.filterMap hKey).length := List.toFinset_card_le _
      _ = 12+(queries.filterMap hKey).length := by rw [List.length_append, ownerLength]
      _ ≤ q+12 := (Nat.add_le_add_left budget.2.1 12).trans (le_of_eq (Nat.add_comm 12 q))
  · exact (List.toFinset_card_le _).trans budget.2.2

/-- Crypto safety refers to the real password and the retained source-key vector. -/
def crypto_guard (real : Password) (keys : Fin 12 → Key) : (Point width) Password Entropy → Prop
  | .a password _ => password ≠ real
  | .h value _ _ => ∀ round : Fin 12, value ≠ keys round
  | _ => True

def query_guard (real : Password) (phrase : Phrase) (keys : Fin 12 → Key) : (Query (width := width)) Password Entropy Phrase → Prop
  | .inl query => crypto_guard real keys query
  | .inr queried => queried ≠ phrase

/-- No good-event guards are assumed: all follow from the absence of the actual footprint's bad event. -/
theorem collect_guards {k q l : Nat} (real disclosed : Password) (phrase : Phrase)
    (keys : Fin 12 → Key) (owner : List Key) (queries : List ((Query (width := width)) Password Entropy Phrase))
    (ownerLength : owner.length=12)
    (budget : (queries.filterMap aPassword).toFinset.card ≤ k ∧
      (queries.filterMap hKey).length ≤ q ∧ (queries.filterMap lookup).length ≤ l)
    (clean : DeniabilityBound.signatureBad real phrase keys
      (collect disclosed owner queries ownerLength budget)=false) :
    disclosed ≠ real ∧ (∀ value ∈ owner, ∀ round : Fin 12, value ≠ keys round) ∧
      (∀ point ∈ queries, query_guard real phrase keys point) := by
  have excluded : ¬(real ∈ insert disclosed (queries.filterMap aPassword).toFinset ∨
      phrase ∈ (queries.filterMap lookup).toFinset ∨
      ∃ round : Fin 12, keys round ∈ (owner++queries.filterMap hKey).toFinset) :=
    of_decide_eq_false clean
  have noPW : real ∉ insert disclosed (queries.filterMap aPassword).toFinset :=
    fun member => excluded (Or.inl member)
  have noPhrase : phrase ∉ (queries.filterMap lookup).toFinset :=
    fun member => excluded (Or.inr (Or.inl member))
  have noKey (round : Fin 12) : keys round ∉ (owner++queries.filterMap hKey).toFinset :=
    fun member => excluded (Or.inr (Or.inr ⟨round,member⟩))
  refine ⟨?_, ?_, ?_⟩
  · intro same
    apply noPW
    rw [← same]
    exact Finset.mem_insert_self _ _
  · intro value member round same
    apply noKey round
    exact List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (same ▸ member)))
  · intro point member
    cases point with
    | inl query =>
      cases query with
      | a password salt =>
        intro same
        apply noPW
        apply Finset.mem_insert_of_mem
        apply List.mem_toFinset.mpr
        apply List.mem_filterMap.mpr
        exact ⟨.inl (.a password salt),member,congrArg some same⟩
      | b round right => trivial
      | g entropy => trivial
      | h value round right =>
        intro index same
        apply noKey index
        apply List.mem_toFinset.mpr
        apply List.mem_append.mpr
        apply Or.inr
        apply List.mem_filterMap.mpr
        exact ⟨.inl (.h value round right),member,congrArg some same⟩
    | inr queried =>
      intro same
      apply noPhrase
      apply List.mem_toFinset.mpr
      apply List.mem_filterMap.mpr
      exact ⟨.inr queried,member,congrArg some same⟩

/-- The actual transcript yields exactly the finite sets used by the statistical argument. -/
def summary {k q l : Nat} (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (base : (Tables width) Password Entropy) (baseRecords : Phrase → Record) (phrase : (State width) → Phrase)
    (container : (State width)) (password : Password) (record : Record) :
    DeniabilityBound.Footprint Password Phrase k q l :=
  -- Keep the recovery arguments identical: alias unfolding otherwise expands all twelve rounds.
  collect (Password := Password) (Entropy := Entropy) (Phrase := Phrase) (k := k) (q := q) (l := l)
    password ((recover base password container).2.filterMap ownerKey)
    (trace attacker.run base
      (PreparedDisclosure.overlay baseRecords (phrase (recover base password container).1.1) record)
      container password (recover base password container).1.1 record)
    (owner_key_count base password container)
    (attacker.bounded base
      (PreparedDisclosure.overlay baseRecords (phrase (recover base password container).1.1) record)
      container password (recover base password container).1.1 record)

/-- This observer uses only the public oracles, Y, Q and freshly sampled synthetic records. -/
def observe {k q l : Nat} (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (passwords : PMF Password) (base : (Tables width) Password Entropy) (empty : Record)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (container : (State width)) :
    PMF (DeniabilityBound.Footprint Password Phrase k q l) :=
  passwords.bind fun password =>
    let recovered := (recover base password container).1.1
    (usage (phrase recovered)).map fun record =>
      summary attacker base (fun _ => empty) phrase container password record

omit [DecidableEq Password] in
/-- The VCVio execution used here is the same generic table execution as the erasure coupling. -/
private theorem execution_as_table (base : (Tables width) Password Entropy)
    (program : OracleComp ((spec width) Password Entropy) Result) :
    execute base program = TranscriptErasure.execute (answer base) program := by
  unfold execute
  rfl

omit [DecidableEq Password] in
/-- Every A call of a genuine owner recovery uses the disclosed password. -/
private theorem owner_password (base : (Tables width) Password Entropy) (password other : Password)
    (fuel : Nat) (container : (State width)) (bound : fuel ≤ 12) (salt : Salt)
    (member : Point.a other salt ∈ (execute base (finalize password fuel container bound)).2) :
    other=password := by
  induction fuel generalizing container with
  | zero => simp only [finalize, execute_pure, List.not_mem_nil] at member
  | succ fuel ih =>
    rw [DeniabilityModel.finalize_step password base fuel (by omega) container] at member
    dsimp only at member
    simp only [List.cons_append, List.nil_append, List.mem_cons] at member
    rcases member with impossible | same | impossible | rest
    · cases impossible
    · exact Point.a.inj same |>.1
    · cases impossible
    · exact ih _ (by omega) rest

variable (real : Password) (base : (Tables width) Password Entropy) (source : (State width))
  (row : Salt → Key) (spare : (HTable width))

/-- Replace P's A row and erase just the H inputs genuinely used to encrypt the source. -/
def erased : (Tables width) Password Entropy :=
  { base with a := DeniabilityRows.replace real base.a row
              h := (TranscriptErasure.exchanged
                (DeniabilityPrivateOracle.sourceProgram (fun salt => base.a (real,salt)) base.b source)
                (base.h,spare)).2 }

def Safe (real : Password) (base : (Tables width) Password Entropy) (source : (State width)) :
    (Point width) Password Entropy → Prop :=
  crypto_guard real (DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h))

/-- Crypto answers agree at every safe query, with B/G shared in full. -/
theorem safe_answer (point : (Point width) Password Entropy) (safe : Safe real base source point) :
    answer (erased real base source row spare) point = answer base point := by
  cases point with
  | a password salt => exact if_neg safe
  | b round right => rfl
  | g entropy => rfl
  | h value round right =>
    exact DeniabilitySource.erased_value (fun salt => base.a (real,salt))
      base.b source base.h spare (value,round,right) safe

/-- Real adaptive crypto execution is identical off the stated query events. -/
theorem safe_execution (real : Password) (base : (Tables width) Password Entropy)
    (source : (State width)) (row : Salt → Key) (spare : (HTable width))
    (program : OracleComp ((spec width) Password Entropy) Result)
    (safe : ∀ point ∈ (execute (erased real base source row spare) program).2, Safe real base source point) :
    execute base program = execute (erased real base source row spare) program := by
  rw [execution_as_table, execution_as_table]
  apply TranscriptErasure.execute_agree
  intro point member
  rw [← execution_as_table] at member
  exact (safe_answer real base source row spare point (safe point member)).symm

/-- Owner recovery needs no A-password charge beyond Q=P; its H calls remain explicitly charged. -/
theorem owner_agreement (real disclosed : Password) (different : disclosed ≠ real)
    (base : (Tables width) Password Entropy) (source container : (State width)) (row : Salt → Key)
    (spare : (HTable width))
    (safeH : ∀ value round right, Point.h value round right ∈ (recover (erased real base source row spare) disclosed container).2 → ∀ index : Fin 12, value ≠ DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h) index) :
    recover base disclosed container = recover (erased real base source row spare) disclosed container := by
  unfold recover
  apply safe_execution
  intro point member
  cases point with
  | a password salt =>
    have same := owner_password (erased real base source row spare) disclosed password 12 container (by omega) salt member
    exact same ▸ different
  | b round right => trivial
  | g entropy => trivial
  | h value round right =>
    apply safeH value round right
    simpa only [recover] using member

/-- The complete adaptive record interaction agrees when no real password, key or phrase is queried. -/
theorem finish_agreement (program : (Program (width := width)) Password Entropy Phrase Record)
    (real disclosed : Password) (different : disclosed ≠ real) (base : (Tables width) Password Entropy)
    (source container : (State width)) (row : Salt → Key) (spare : (HTable width))
    (realPhrase : Phrase) (realRecord empty : Record) (phrase : (State width) → Phrase) (record : Record)
    (safeH : ∀ value round right,
      Point.h value round right ∈ (recover (erased real base source row spare) disclosed container).2 →
      ∀ index : Fin 12,
        value ≠ DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h) index)
    (safeAdv : ∀ point ∈ (finish program (erased real base source row spare)
        (fun _ => empty) phrase container disclosed record).adversary,
      match point with
      | .inl query => Safe real base source query
      | .inr queried => queried ≠ realPhrase) :
    finish program base (PreparedDisclosure.realOracle realPhrase realRecord empty)
      phrase container disclosed record =
    finish program (erased real base source row spare) (fun _ => empty)
      phrase container disclosed record := by
  have owner := owner_agreement real disclosed different base source container row spare safeH
  have same : TranscriptErasure.execute
      (table base (PreparedDisclosure.overlay
        (PreparedDisclosure.realOracle realPhrase realRecord empty)
        (phrase (recover (erased real base source row spare) disclosed container).1.1) record))
      (program container disclosed (recover (erased real base source row spare) disclosed container).1.1 record) =
    TranscriptErasure.execute
      (table (erased real base source row spare) (PreparedDisclosure.overlay (fun _ => empty)
        (phrase (recover (erased real base source row spare) disclosed container).1.1) record))
      (program container disclosed (recover (erased real base source row spare) disclosed container).1.1 record) := by
    apply TranscriptErasure.execute_agree
    intro point member
    have safe := safeAdv point (by simpa only [finish] using member)
    cases point with
    | inl query => exact (safe_answer real base source row spare query safe).symm
    | inr queried =>
      by_cases samePhrase : queried=phrase (recover (erased real base source row spare) disclosed container).1.1
      · simp only [table, combinedAnswer, PreparedDisclosure.overlay, if_pos samePhrase]
      · simp only [table, combinedAnswer, PreparedDisclosure.overlay, if_neg samePhrase,
          PreparedDisclosure.realOracle, if_neg safe]
  have result := congrArg (fun actual : Bool × List ((Query (width := width)) Password Entropy Phrase) =>
    (⟨disclosed, (recover (erased real base source row spare) disclosed container).1.1,
      record, actual.1, (recover (erased real base source row spare) disclosed container).2,
      actual.2⟩ : (Run (width := width)) Password Entropy Phrase Record)) same
  simpa only [finish, owner] using result

/-- The query guards for the actual erased run are consequences of its recorded bad event. -/
theorem same_if_clean {k q l : Nat} (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (real disclosed : Password) (base : (Tables width) Password Entropy) (source container : (State width))
    (row : Salt → Key) (spare : (HTable width)) (realPhrase : Phrase) (realRecord empty : Record)
    (phrase : (State width) → Phrase) (record : Record)
    (clean : DeniabilityBound.signatureBad real realPhrase
      (DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h))
      (summary attacker (erased real base source row spare) (fun _ => empty) phrase container disclosed record)=false) :
    finish attacker.run base (PreparedDisclosure.realOracle realPhrase realRecord empty)
      phrase container disclosed record =
    finish attacker.run (erased real base source row spare) (fun _ => empty)
      phrase container disclosed record := by
  have guards := collect_guards real disclosed realPhrase
    (DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h))
    ((recover (erased real base source row spare) disclosed container).2.filterMap ownerKey)
    (trace attacker.run (erased real base source row spare)
      (PreparedDisclosure.overlay (fun _ => empty)
        (phrase (recover (erased real base source row spare) disclosed container).1.1) record)
      container disclosed (recover (erased real base source row spare) disclosed container).1.1 record)
    (owner_key_count (erased real base source row spare) disclosed container)
    (attacker.bounded (erased real base source row spare)
      (PreparedDisclosure.overlay (fun _ => empty)
        (phrase (recover (erased real base source row spare) disclosed container).1.1) record)
      container disclosed (recover (erased real base source row spare) disclosed container).1.1 record)
    clean
  apply finish_agreement attacker.run real disclosed guards.1 base source container row spare
    realPhrase realRecord empty phrase record
  · intro value round right member index
    apply guards.2.1 value _ index
    exact List.mem_filterMap.mpr ⟨Point.h value round right,member,rfl⟩
  · intro point member
    have present : point ∈ trace attacker.run (erased real base source row spare)
        (PreparedDisclosure.overlay (fun _ => empty)
          (phrase (recover (erased real base source row spare) disclosed container).1.1) record)
        container disclosed (recover (erased real base source row spare) disclosed container).1.1 record := by
      simpa only [finish, trace] using member
    have guarded := guards.2.2 point present
    cases point with
    | inl query => exact guarded
    | inr queried => exact guarded

/-- Equal-until-bad includes the usage-record sampling; no success conditioning is introduced. -/
theorem opening_close {k q l : Nat} (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (real disclosed : Password) (base : (Tables width) Password Entropy) (source container : (State width))
    (row : Salt → Key) (spare : (HTable width)) (realPhrase : Phrase) (realRecord empty : Record)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) :
    StatisticalClose.Close
      ((opening attacker.run base (PreparedDisclosure.realOracle realPhrase realRecord empty)
        phrase usage container disclosed).map Run.result)
      ((opening attacker.run (erased real base source row spare) (fun _ => empty)
        phrase usage container disclosed).map Run.result)
      (((usage (phrase (recover (erased real base source row spare) disclosed container).1.1)).map fun record =>
        DeniabilityBound.signatureBad real realPhrase
          (DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h))
          (summary attacker (erased real base source row spare) (fun _ => empty) phrase container disclosed record)) true) := by
  classical
  let badR := fun record : Record => DeniabilityBound.signatureBad real realPhrase
    (DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h))
    (summary attacker (erased real base source row spare) (fun _ => empty) phrase container disclosed record)
  by_cases possible : ∃ record, badR record=false
  · obtain ⟨witness, clean⟩ := possible
    have state_eq := congrArg Run.recovered (same_if_clean attacker real disclosed base source container
      row spare realPhrase realRecord empty phrase witness clean)
    have law : usage (phrase (recover base disclosed container).1.1) =
        usage (phrase (recover (erased real base source row spare) disclosed container).1.1) := by
      apply congrArg (fun state => usage (phrase state))
      simpa only [finish] using state_eq
    have coupled := StatisticalClose.coupling
      (usage (phrase (recover (erased real base source row spare) disclosed container).1.1))
      (fun record => (finish attacker.run base (PreparedDisclosure.realOracle realPhrase realRecord empty)
        phrase container disclosed record).result)
      (fun record => (finish attacker.run (erased real base source row spare) (fun _ => empty)
        phrase container disclosed record).result)
      badR (fun record clean => congrArg Run.result
        (same_if_clean attacker real disclosed base source container row spare realPhrase realRecord empty phrase record clean))
    simpa only [opening, law, PMF.map_comp, Function.comp_def, badR] using coupled
  · have all (record : Record) : badR record=true := by
      cases found : badR record with
      | true => rfl
      | false => exact False.elim (possible ⟨record,found⟩)
    have certain : ((usage (phrase (recover (erased real base source row spare) disclosed container).1.1)).map badR) true=1 := by
      rw [MomentTools.probability]
      simp only [all, ite_true, MomentTools.constant]
    change StatisticalClose.Close _ _
      (((usage (phrase (recover (erased real base source row spare) disclosed container).1.1)).map badR) true)
    rw [certain]
    intro test
    constructor
    all_goals
      apply le_trans (b := (1:ENNReal))
      · exact PMF.coe_le_one _ true
      · exact le_add_of_nonneg_left (zero_le)

attribute [local instance] FiniteBits.fintype

/-- The middle-hop probability bound is instantiated with actual adaptive interaction traces. -/
theorem actual_bad_bound [Fintype Entropy] [Nonempty Entropy] {k q l : Nat}
    (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (passwords : PMF Password) (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (base : (Tables width) Password Entropy) (empty : Record) (pack : Entropy → (State width))
    (realPhrase : Entropy → Phrase) (injective : Function.Injective realPhrase)
    (disclosedPhrase : (State width) → Phrase) (usage : Phrase → PMF Record) :
    ((DeniabilityBound.worlds passwords base.b pack
      (observe attacker passwords base empty disclosedPhrase usage)).map
      (DeniabilityBound.bad base.b pack realPhrase)) true ≤
      ((k+1:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal) :=
  DeniabilityBound.bad_bound passwords p1 largest base.b pack
    (observe attacker passwords base empty disclosedPhrase usage) realPhrase injective

/-- The public experiment draws a uniform Y, then creates exactly the disclosed opening and empty other records. -/
def public_game (program : (Program (width := width)) Password Entropy Phrase Record) (passwords : PMF Password)
    (base : (Tables width) Password Entropy) (empty : Record) (phrase : (State width) → Phrase)
    (usage : Phrase → PMF Record) : PMF Bool :=
  (PMF.uniformOfFintype (State width)).bind fun container =>
    passwords.bind fun disclosed =>
      (opening program base (fun _ => empty) phrase usage container disclosed).map Run.result

/-- The honest experiment begins with a uniform24-word source and keeps its first password. -/
def honest_game (program : (Program (width := width)) Password Entropy Phrase Record) (passwords : PMF Password)
    (base : (Tables width) Password Entropy) (empty : Record) (phrase : (State width) → Phrase)
    (usage : Phrase → PMF Record) : PMF Bool :=
  passwords.bind fun disclosed => (PMF.uniformOfFintype (State width)).bind fun source =>
    (opening program base (fun _ => empty) phrase usage
      (DeniabilityModel.cipher disclosed base.a base.b base.h source) disclosed).map Run.result

omit [DecidableEq Password] in
/-- Reindexing by the actual MHFE permutation gives the same complete adaptive output law. -/
theorem honest_eq_public (program : (Program (width := width)) Password Entropy Phrase Record) (passwords : PMF Password)
    (base : (Tables width) Password Entropy) (empty : Record) (phrase : (State width) → Phrase)
    (usage : Phrase → PMF Record) :
    honest_game program passwords base empty phrase usage =
      public_game program passwords base empty phrase usage := by
  unfold honest_game public_game
  have fixed (disclosed : Password) := Theorem1.uniform_bind
    (DeniabilityModel.cipher disclosed base.a base.b base.h)
    (fun container => (opening program base (fun _ => empty) phrase usage container disclosed).map Run.result)
  simp_rw [fixed]
  exact PMF.bind_comm _ _ _

omit [DecidableEq Password] in
/-- A private source of any fixed entropy has the same public output law as the honest experiment. -/
theorem private_eq_public (program : (Program (width := width)) Password Entropy Phrase Record) (passwords : PMF Password)
    (base : (Tables width) Password Entropy) (empty : Record) (phrase : (State width) → Phrase)
    (usage : Phrase → PMF Record) (source : (State width)) :
    ((PMF.uniformOfFintype (DeniabilityPrivate.World width)).bind fun inner =>
      passwords.bind fun disclosed =>
        (opening program base (fun _ => empty) phrase usage
          (DeniabilityPrivate.cipher base.b source inner) disclosed).map Run.result) =
      public_game program passwords base empty phrase usage := by
  have law := congrArg (fun distribution : PMF (State width) => distribution.bind fun container =>
      passwords.bind fun disclosed =>
        (opening program base (fun _ => empty) phrase usage container disclosed).map Run.result)
    (DeniabilityPrivate.cipher_uniform base.b source)
  simpa only [PMF.bind_map, Function.comp_def, public_game] using law

end DeniabilityInteraction

namespace DeniabilityReprogramming
attribute [local irreducible] TranscriptErasure.exchanged
  TranscriptErasure.execute DeniabilityPrivateOracle.sourceProgram
open DeniabilityModel ProbabilityTools
open DeniabilityRows DeniabilitySource DeniabilityPrivate
variable {width : Nat}
variable {Password : Type} [DecidableEq Password]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] DeniabilityPrivate.cipher DeniabilityPrivate.key

abbrev Seed (Password : Type) := (ATable Password × Row) × ((HTable width) × (HTable width))

/-- Erasing the source H transcript is an involution even when the chosen A row is retained. -/
def hswap (real : Password) (b : (BTable width)) (source : (State width)) : Equiv.Perm ((Seed (width := width)) Password) where
  toFun seed := (seed.1, TranscriptErasure.exchanged
    (DeniabilityPrivateOracle.sourceProgram (fun salt => seed.1.1 (real,salt)) b source) seed.2)
  invFun seed := (seed.1, TranscriptErasure.exchanged
    (DeniabilityPrivateOracle.sourceProgram (fun salt => seed.1.1 (real,salt)) b source) seed.2)
  left_inv := by
    intro seed
    apply Prod.ext
    · rfl
    · exact TranscriptErasure.involutive _ seed.2
  right_inv := by
    intro seed
    apply Prod.ext
    · rfl
    · exact TranscriptErasure.involutive _ seed.2

/-- Keep the old P row private and move the independent replacement row to the public A table. -/
def reprogram (real : Password) (b : (BTable width)) (source : (State width)) :
    Equiv.Perm ((Seed (width := width)) Password) :=
  (hswap real b source).trans
    (Equiv.prodCongr (DeniabilityRows.swap real) (Equiv.refl ((HTable width) × (HTable width))))

def shuffle : (Seed (width := width)) Password ≃ ((World width) × (ATable Password × (HTable width))) where
  toFun seed := ((seed.1.2,seed.2.1),(seed.1.1,seed.2.2))
  invFun fields := ((fields.2.1,fields.1.1),(fields.1.2,fields.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Source signature, public A and public H after the genuine pointwise reprogramming. -/
def coupled {Output : Type} (real : Password) (b : (BTable width)) (source : (State width))
    (observe : (Signature width) → ATable Password → (HTable width) → PMF Output) [Fintype Password] :
    PMF Output :=
  (PMF.uniformOfFintype ((Seed (width := width)) Password)).bind fun seed =>
    observe
      (cipher b source (fun salt => seed.1.1 (real,salt),seed.2.1),
        key b source (fun salt => seed.1.1 (real,salt),seed.2.1))
      (replace real seed.1.1 seed.1.2)
      (TranscriptErasure.exchanged
        (DeniabilityPrivateOracle.sourceProgram (fun salt => seed.1.1 (real,salt)) b source) seed.2).2

/-- The erased public tables have exactly fresh independent laws, jointly with all observed source keys. -/
theorem joint [Fintype Password] {Output : Type} (real : Password) (b : (BTable width))
    (source : (State width))
    (observe : (Signature width) → ATable Password → (HTable width) → PMF Output) :
    coupled real b source observe =
      (PMF.uniformOfFintype (World width)).bind fun inner =>
        (PMF.uniformOfFintype (ATable Password × (HTable width))).bind fun shared =>
          observe (cipher b source inner,key b source inner) shared.1 shared.2 := by
  let transform := (reprogram real b source).trans shuffle
  let post := fun fields : (World width) × (ATable Password × (HTable width)) =>
    observe (cipher b source fields.1,key b source fields.1) fields.2.1 fields.2.2
  have pointwise (seed : (Seed (width := width)) Password) :
      observe
        (cipher b source (fun salt => seed.1.1 (real,salt),seed.2.1),
          key b source (fun salt => seed.1.1 (real,salt),seed.2.1))
        (replace real seed.1.1 seed.1.2)
        (TranscriptErasure.exchanged
          (DeniabilityPrivateOracle.sourceProgram (fun salt => seed.1.1 (real,salt)) b source) seed.2).2 =
      post (transform seed) := by
    have stable := congrArg signature (TranscriptErasure.stable
      (DeniabilityPrivateOracle.sourceProgram (fun salt => seed.1.1 (real,salt)) b source) seed.2)
    rw [signature_actual, signature_actual] at stable
    have result := congrArg (fun sig => observe sig (replace real seed.1.1 seed.1.2)
      (TranscriptErasure.exchanged
        (DeniabilityPrivateOracle.sourceProgram (fun salt => seed.1.1 (real,salt)) b source) seed.2).2) stable.symm
    (try simp only [post, transform, reprogram, shuffle, hswap, DeniabilityRows.swap, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply, Equiv.coe_fn_mk] at result ⊢)
    exact result
  calc
    _ = ((PMF.uniformOfFintype ((Seed (width := width)) Password)).map transform).bind post := by
      rw [PMF.bind_map]
      apply congrArg (fun next => (PMF.uniformOfFintype ((Seed (width := width)) Password)).bind next)
      funext seed
      exact pointwise seed
    _ = (PMF.uniformOfFintype ((World width) × (ATable Password × (HTable width)))).bind post := by
      rw [PMF.uniformOfFintype_map_of_bijective transform transform.bijective]
    _ = _ := by
      rw [uniform_product]
      simp only [independentPair, PMF.bind_bind, PMF.bind_map, Function.comp_def, post]

/-- Scalar expectations use the same joint law without unfolding the observer's internal distribution. -/
theorem expectation [Fintype Password] (real : Password) (b : (BTable width))
    (source : (State width))
    (value : (Signature width) → ATable Password → (HTable width) → ENNReal) :
    GameExpectation.moment (PMF.uniformOfFintype ((Seed (width := width)) Password)) (fun seed =>
      value (cipher b source (fun salt => seed.1.1 (real,salt),seed.2.1),
          key b source (fun salt => seed.1.1 (real,salt),seed.2.1))
        (replace real seed.1.1 seed.1.2)
        (TranscriptErasure.exchanged
          (DeniabilityPrivateOracle.sourceProgram (fun salt => seed.1.1 (real,salt)) b source) seed.2).2) =
    GameExpectation.moment (PMF.uniformOfFintype (World width)) (fun inner =>
      GameExpectation.moment (PMF.uniformOfFintype (ATable Password × (HTable width)))
        (fun shared => value (cipher b source inner,key b source inner) shared.1 shared.2)) := by
  let observe := fun signature : (Signature width) => fun a : ATable Password => fun h : (HTable width) =>
    PMF.pure (signature,(a,h))
  let score := fun output : (Signature width) × (ATable Password × (HTable width)) =>
    value output.1 output.2.1 output.2.2
  have pure_score (output : (Signature width) × (ATable Password × (HTable width))) :
      GameExpectation.moment (PMF.pure output) score = score output := by
    classical
    simp [GameExpectation.moment, PMF.pure_apply]
  have result := congrArg (fun law => GameExpectation.moment law score)
    (joint real b source observe)
  simp only [coupled, MomentTools.bind, observe, pure_score, score] at result
  exact result

end DeniabilityReprogramming

namespace Theorem2
attribute [local irreducible] DeniabilityReprogramming.coupled
open DeniabilityModel ProbabilityTools
open GameExpectation MomentTools StatisticalClose
open DeniabilityInteraction DeniabilityBound
variable {width : Nat}
variable {Password Entropy Phrase Record : Type} [DecidableEq Password] [DecidableEq Phrase]
  [Fintype Password] [Fintype Entropy] [Nonempty Entropy] {k q l : Nat}
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] DeniabilityPrivate.cipher DeniabilityPrivate.key
  TranscriptErasure.execute DeniabilityModel.execute recover
  DeniabilityModel.cipher

abbrev Sample (Password : Type) := DeniabilityReprogramming.Seed (width := width) Password
abbrev Public (Password : Type) := ATable Password × (HTable width)
abbrev Context (Password Entropy : Type) := Password × Entropy × (Sample (width := width)) Password

/-- B/G are shared fixed context here; the final bound can be averaged over their independent laws. -/
def tables (b : (BTable width)) (g : GTable Entropy) (a : ATable Password) (h : (HTable width)) :
    (Tables width) Password Entropy :=
  ⟨a,b,h,g⟩

def originalTables (b : (BTable width)) (g : GTable Entropy) (sample : (Sample (width := width)) Password) : (Tables width) Password Entropy :=
  tables b g sample.1.1 sample.2.1

def sig (real : Password) (b : (BTable width)) (source : (State width)) (sample : (Sample (width := width)) Password) : (DeniabilitySource.Signature width) :=
  (DeniabilityPrivate.cipher b source (fun salt => sample.1.1 (real,salt),sample.2.1),
    DeniabilityPrivate.key b source (fun salt => sample.1.1 (real,salt),sample.2.1))

def changed (real : Password) (b : (BTable width)) (g : GTable Entropy) (source : (State width))
    (sample : (Sample (width := width)) Password) : (Tables width) Password Entropy :=
  erased real (originalTables b g sample) source sample.1.2 sample.2.2

/-- Extra independent spare tables are unobserved setup coins, not adversary inputs. -/
def prior (passwords : PMF Password) : PMF ((Context (width := width)) Password Entropy) :=
  passwords.bind fun real => (PMF.uniformOfFintype Entropy).bind fun entropy =>
    (PMF.uniformOfFintype ((Sample (width := width)) Password)).map fun sample => (real,entropy,sample)

/-- The genuine wallet record may depend on the source and oracles; only the decoy uses U. -/
def oldKernel (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → PMF Record)
    (context : (Context (width := width)) Password Entropy) : PMF Bool :=
  (realRecords context.1 context.2.1 (originalTables b g context.2.2)).bind fun realRecord =>
    passwords.bind fun disclosed =>
      (opening attacker.run (originalTables b g context.2.2)
        (PreparedDisclosure.realOracle (realPhrase context.2.1) realRecord empty)
        phrase usage (sig context.1 b (pack context.2.1) context.2.2).1 disclosed).map Run.result

def newKernel (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width))
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (context : (Context (width := width)) Password Entropy) : PMF Bool :=
  passwords.bind fun disclosed =>
    (opening attacker.run (changed context.1 b g (pack context.2.1) context.2.2)
      (fun _ => empty) phrase usage (sig context.1 b (pack context.2.1) context.2.2).1 disclosed).map Run.result

def errorKernel (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (context : (Context (width := width)) Password Entropy) : ENNReal :=
  ((observe attacker passwords (changed context.1 b g (pack context.2.1) context.2.2) empty phrase usage
    (sig context.1 b (pack context.2.1) context.2.2).1).map
      (signatureBad context.1 (realPhrase context.2.1)
        (sig context.1 b (pack context.2.1) context.2.2).2)) true

omit [Fintype Password] [Fintype Entropy] [Nonempty Entropy] in
/-- The middle game hop has exactly the erased-run bad probability, with arbitrary real records integrated out. -/
theorem conditional_close (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → PMF Record)
    (context : (Context (width := width)) Password Entropy) :
    Close (oldKernel attacker passwords b g pack realPhrase phrase usage empty realRecords context)
      (newKernel attacker passwords b g pack phrase usage empty context)
      (errorKernel attacker passwords b g pack realPhrase phrase usage empty context) := by
  rcases context with ⟨real,entropy,sample⟩
  have perRecord (realRecord : Record) := CloseComposition.bind passwords _ _ _
    (fun disclosed => opening_close attacker real disclosed (originalTables b g sample)
      (pack entropy) (sig real b (pack entropy) sample).1 sample.1.2 sample.2.2
      (realPhrase entropy) realRecord empty phrase usage)
  have across := CloseComposition.bind
    (realRecords real entropy (originalTables b g sample)) _ _ _ perRecord
  simp only [MomentTools.constant, PMF.bind_const] at across
  simpa only [oldKernel, newKernel, errorKernel, observe, changed, sig, originalTables, tables,
    PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_apply, moment] using across

omit [Fintype Entropy] [Nonempty Entropy] in
/-- Reprogramming preserves the full signature/public-table law used by the actual bad test. -/
theorem fixed_error (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record) (real : Password) (entropy : Entropy) :
    moment (PMF.uniformOfFintype ((Sample (width := width)) Password)) (fun sample =>
      errorKernel attacker passwords b g pack realPhrase phrase usage empty (real,entropy,sample)) =
    moment (PMF.uniformOfFintype (DeniabilityPrivate.World width)) (fun inner =>
      moment (PMF.uniformOfFintype ((Public (width := width)) Password)) (fun shared =>
        ((observe attacker passwords (tables b g shared.1 shared.2) empty phrase usage
          (DeniabilityPrivate.cipher b (pack entropy) inner)).map
          (signatureBad real (realPhrase entropy) (DeniabilityPrivate.key b (pack entropy) inner))) true)) := by
  exact DeniabilityReprogramming.expectation real b (pack entropy)
    (fun signature a h =>
      ((observe attacker passwords (tables b g a h) empty phrase usage signature.1).map
        (signatureBad real (realPhrase entropy) signature.2)) true)

/-- The complete mean bad probability is derived from the actual adversary budgets. -/
theorem error_bound (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (injective : Function.Injective realPhrase) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record) :
    moment (prior (Entropy := Entropy) passwords)
      (errorKernel attacker passwords b g pack realPhrase phrase usage empty) ≤
      ((k+1:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal) := by
  simp only [prior, MomentTools.bind, moment_map, Function.comp_def]
  simp_rw [fixed_error attacker passwords b g pack realPhrase phrase usage empty]
  conv_lhs =>
    arg 2
    ext real
    arg 2
    ext entropy
    rw [G8Transport.comm]
  conv_lhs =>
    arg 2
    ext real
    rw [G8Transport.comm]
  rw [G8Transport.comm]
  apply bounded
  intro shared
  have estimate := actual_bad_bound attacker passwords p1 largest (tables b g shared.1 shared.2)
    empty pack realPhrase injective phrase usage
  (try simp only [worlds, MomentTools.probability, MomentTools.bind, moment_map, Function.comp_def, bad, tables] at estimate ⊢)
  exact estimate

/-- The source-faithful middle hop; no game-distance or bad-probability bound is a hypothesis. -/
theorem middle_bound (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (injective : Function.Injective realPhrase) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → PMF Record) :
    Close ((prior passwords).bind (oldKernel attacker passwords b g pack realPhrase phrase usage empty realRecords))
      ((prior passwords).bind (newKernel attacker passwords b g pack phrase usage empty))
      (((k+1:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal)) := by
  have hop := CloseComposition.bind (prior passwords) _ _ _
    (conditional_close attacker passwords b g pack realPhrase phrase usage empty realRecords)
  exact StatisticalClose.mono _ _ _ _ hop
    (error_bound attacker passwords p1 largest b g pack realPhrase injective phrase usage empty)

omit [Fintype Entropy] [Nonempty Entropy] in
/-- Averaging a single erased setup removes the hidden source completely. -/
theorem fixed_new (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width))
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record) (real : Password) (entropy : Entropy) :
    (PMF.uniformOfFintype ((Sample (width := width)) Password)).bind (fun sample =>
      newKernel attacker passwords b g pack phrase usage empty (real,entropy,sample)) =
    (PMF.uniformOfFintype ((Public (width := width)) Password)).bind (fun shared =>
      honest_game attacker.run passwords (tables b g shared.1 shared.2) empty phrase usage) := by
  let observe := fun signature : (DeniabilitySource.Signature width) =>
    fun a : ATable Password => fun h : (HTable width) => passwords.bind fun disclosed =>
      (opening attacker.run (tables b g a h) (fun _ => empty) phrase usage signature.1 disclosed).map Run.result
  have left : (PMF.uniformOfFintype ((Sample (width := width)) Password)).bind (fun sample =>
      newKernel attacker passwords b g pack phrase usage empty (real,entropy,sample)) =
      DeniabilityReprogramming.coupled real b (pack entropy) observe := by
    unfold DeniabilityReprogramming.coupled
    rfl
  rw [left, DeniabilityReprogramming.joint, PMF.bind_comm]
  apply congrArg (fun next => (PMF.uniformOfFintype ((Public (width := width)) Password)).bind next)
  funext shared
  exact (private_eq_public attacker.run passwords (tables b g shared.1 shared.2) empty phrase usage (pack entropy)).trans
    (honest_eq_public attacker.run passwords (tables b g shared.1 shared.2) empty phrase usage).symm

/-- The erased experiment is exactly the honest experiment before its first creation refusal. -/
theorem new_eq_honest (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width))
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record) :
    (prior passwords).bind (newKernel attacker passwords b g pack phrase usage empty) =
    (PMF.uniformOfFintype ((Public (width := width)) Password)).bind (fun shared =>
      honest_game attacker.run passwords (tables b g shared.1 shared.2) empty phrase usage) := by
  simp only [prior, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  simp_rw [fixed_new attacker passwords b g pack phrase usage empty]
  simp only [PMF.bind_const]

omit [DecidableEq Phrase] [Fintype Entropy] [Nonempty Entropy] in
/-- Source-dependent packing is allowed because the source is fixed before the independent H table. -/
theorem fixed_point (real : Password) (b : (BTable width)) (source : (State width)) :
    moment (PMF.uniformOfFintype ((Sample (width := width)) Password)) (fun sample =>
      if (sig real b source sample).1=source then 1 else 0) = (2^(2*width):ENNReal)⁻¹ := by
  have reprogram := DeniabilityReprogramming.expectation real b source
    (fun signature _ _ => if signature.1=source then 1 else 0)
  simp only [MomentTools.constant] at reprogram
  have uniform := congrArg (fun law : PMF (State width) => law source)
    (DeniabilityPrivate.cipher_uniform b source)
  try dsimp only at uniform
  rw [← PointMassEvent.equality _ source, MomentTools.probability,
    moment_map, PMF.uniformOfFintype_apply, DeniabilityModel.state_card,Nat.cast_pow,Nat.cast_ofNat] at uniform
  have exactMass : moment (PMF.uniformOfFintype (DeniabilityPrivate.World width))
      (fun inner => if DeniabilityPrivate.cipher b source inner=source then 1 else 0) =
      (2^(2*width):ENNReal)⁻¹ := by
    simpa only [Function.comp_def, decide_eq_true_eq] using uniform
  exact reprogram.trans exactMass

/-- The first unconditional opening, before either password-redraw rule is applied. -/
def preparedOnce (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → PMF Record)
    (context : (Context (width := width)) Password Entropy) (disclosed : Password) : PMF Bool :=
  (realRecords context.1 context.2.1 (originalTables b g context.2.2)).bind fun realRecord =>
    (opening attacker.run (originalTables b g context.2.2)
      (PreparedDisclosure.realOracle (realPhrase context.2.1) realRecord empty)
      phrase usage (sig context.1 b (pack context.2.1) context.2.2).1 disclosed).map Run.result

def preparedFlag (b : (BTable width)) (pack : Entropy → (State width))
    (context : (Context (width := width)) Password Entropy) (disclosed : Password) : Bool :=
  decide (disclosed=context.1 ∨ (sig context.1 b (pack context.2.1) context.2.2).1=pack context.2.1)

/-- On a refused first draw, later includes the full conditional redraw or common failure response. -/
def prepared (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → PMF Record)
    (later : (Context (width := width)) Password Entropy → Password → PMF Bool) : PMF Bool :=
  (prior passwords).bind fun context => passwords.bind fun disclosed =>
    if preparedFlag b pack context disclosed then later context disclosed else
      preparedOnce attacker b g pack realPhrase phrase usage empty realRecords context disclosed

omit [DecidableEq Password] [DecidableEq Phrase] [Fintype Password] [Fintype Entropy] [Nonempty Entropy] in
/-- A possibly randomized experiment changes by at most its first-refusal mass. -/
private theorem response_close {Environment Output : Type} (law : PMF Environment)
    (flag : Environment → Bool) (original later : Environment → PMF Output) :
    Close (law.bind fun env => if flag env then later env else original env) (law.bind original)
      (moment law (fun env => if flag env then 1 else 0)) := by
  apply CloseComposition.bind
  intro env
  cases hit : flag env with
  | false => exact of_eq _ _ rfl
  | true =>
    intro test
    constructor
    · exact (((later env).map test).coe_le_one true).trans (le_add_of_nonneg_left (zero_le))
    · exact (((original env).map test).coe_le_one true).trans (le_add_of_nonneg_left (zero_le))

omit [DecidableEq Phrase] in
/-- Both prepared refusals are charged before conditioning, retaining all failure mass. -/
theorem prepared_flag_bound (passwords : PMF Password) (p1 : ENNReal)
    (largest : ∀ password, passwords password ≤ p1) (b : (BTable width)) (pack : Entropy → (State width)) :
    moment (prior passwords) (fun context => moment passwords (fun disclosed =>
      if preparedFlag b pack context disclosed then 1 else 0)) ≤ p1+(2^(2*width):ENNReal)⁻¹ := by
  have indicator (context : (Context (width := width)) Password Entropy) (disclosed : Password) :
      (if preparedFlag b pack context disclosed then (1:ENNReal) else 0) ≤
        (if disclosed=context.1 then 1 else 0)+
        (if (sig context.1 b (pack context.2.1) context.2.2).1=pack context.2.1 then 1 else 0) := by
    simp only [preparedFlag, decide_eq_true_eq]
    split_ifs <;> simp_all
  have password_mass (real : Password) :
      moment passwords (fun disclosed => if disclosed=real then 1 else 0) = passwords real := by
    simpa only [decide_eq_true_eq] using
      (MomentTools.probability passwords (fun disclosed => decide (disclosed=real))).symm.trans
        (PointMassEvent.equality passwords real)
  calc
    _ ≤ moment (prior passwords) (fun context => moment passwords (fun disclosed =>
        (if disclosed=context.1 then 1 else 0)+
        (if (sig context.1 b (pack context.2.1) context.2.2).1=pack context.2.1 then 1 else 0))) :=
      mono _ _ _ (fun context => mono _ _ _ (indicator context))
    _ = moment (prior passwords) (fun context => passwords context.1+
        (if (sig context.1 b (pack context.2.1) context.2.2).1=pack context.2.1 then 1 else 0)) := by
      simp only [MomentTools.add, password_mass, constant]
    _ = moment (prior passwords) (fun context => passwords context.1)+(2^(2*width):ENNReal)⁻¹ := by
      rw [MomentTools.add]
      congr 1
      simp only [prior, MomentTools.bind, moment_map, Function.comp_def]
      simp_rw [fixed_point]
      simp only [constant]
    _ ≤ _ := add_le_add (bounded _ _ _ (fun context => largest context.1)) le_rfl

/-- This hop allows arbitrary later work on a refused first draw, including an empty allowed set. -/
theorem prepared_close (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → PMF Record)
    (later : (Context (width := width)) Password Entropy → Password → PMF Bool) :
    Close (prepared attacker passwords b g pack realPhrase phrase usage empty realRecords later)
      ((prior passwords).bind (oldKernel attacker passwords b g pack realPhrase phrase usage empty realRecords))
      (p1+(2^(2*width):ENNReal)⁻¹) := by
  have per (context : (Context (width := width)) Password Entropy) := response_close passwords
    (preparedFlag b pack context)
    (preparedOnce attacker b g pack realPhrase phrase usage empty realRecords context) (later context)
  have combined := CloseComposition.bind (prior passwords) _ _ _ per
  have before (context : (Context (width := width)) Password Entropy) :
      (passwords.bind (preparedOnce attacker b g pack realPhrase phrase usage empty realRecords context)) =
      oldKernel attacker passwords b g pack realPhrase phrase usage empty realRecords context := by
    exact PMF.bind_comm _ _ _
  simp_rw [before] at combined
  exact StatisticalClose.mono _ _ _ _ combined (prepared_flag_bound passwords p1 largest b pack)

abbrev HonestContext (Password : Type) := (Public (width := width)) Password × Password × (State width)

/-- Honest source generation retains the public tables and the first password. -/
def honestPrior (passwords : PMF Password) : PMF ((HonestContext (width := width)) Password) :=
  (PMF.uniformOfFintype ((Public (width := width)) Password)).bind fun shared =>
    passwords.bind fun disclosed => (PMF.uniformOfFintype (State width)).map fun source => (shared,disclosed,source)

def honestOnce (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (b : (BTable width)) (g : GTable Entropy) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record)
    (empty : Record) (context : (HonestContext (width := width)) Password) : PMF Bool :=
  (opening attacker.run (tables b g context.1.1 context.1.2) (fun _ => empty) phrase usage
    (DeniabilityModel.cipher context.2.1 context.1.1 b context.1.2 context.2.2) context.2.1).map Run.result

def honestFlag (b : (BTable width)) (context : (HonestContext (width := width)) Password) : Bool :=
  decide (DeniabilityModel.cipher context.2.1 context.1.1 b context.1.2 context.2.2=context.2.2)

/-- Later may redraw the refused honest password or return the common failure outcome. -/
def honest (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record)
    (empty : Record) (later : (HonestContext (width := width)) Password → PMF Bool) : PMF Bool :=
  (honestPrior passwords).bind fun context =>
    if honestFlag b context then later context else honestOnce attacker b g phrase usage empty context

omit [DecidableEq Password] [DecidableEq Phrase] [Fintype Password] [Fintype Entropy] [Nonempty Entropy] in
/-- The genuine public H sampler gives the same exact refusal rate for each fixed A/P/source. -/
private theorem h_fixed_point (password : Password) (a : ATable Password) (b : (BTable width)) (source : (State width)) :
    moment (PMF.uniformOfFintype (HTable width)) (fun h =>
      if DeniabilityModel.cipher password a b h source=source then 1 else 0) = (2^(2*width):ENNReal)⁻¹ := by
  have uniform := congrArg (fun law : PMF (State width) => law source)
    (DeniabilityModel.cipher_uniform password a b source)
  try dsimp only at uniform
  rw [← PointMassEvent.equality _ source,MomentTools.probability,
    moment_map,PMF.uniformOfFintype_apply,DeniabilityModel.state_card,Nat.cast_pow,Nat.cast_ofNat] at uniform
  simpa only [Function.comp_def,decide_eq_true_eq] using uniform

omit [DecidableEq Phrase] [Fintype Entropy] [Nonempty Entropy] in
/-- The honest first refusal has its exact mass before the redraw or failure branch. -/
theorem honest_flag_mass (passwords : PMF Password) (b : (BTable width)) :
    moment (honestPrior passwords) (fun context => if honestFlag b context then 1 else 0) =
      (2^(2*width):ENNReal)⁻¹ := by
  simp only [honestPrior, MomentTools.bind, moment_map, Function.comp_def,
    honestFlag, decide_eq_true_eq]
  rw [uniform_product]
  simp only [independentPair, MomentTools.bind, moment_map, Function.comp_def]
  conv_lhs =>
    arg 2
    ext a
    rw [G8Transport.comm]
    arg 2
    ext disclosed
    rw [G8Transport.comm]
  simp_rw [h_fixed_point]
  simp only [constant]

omit [Fintype Entropy] [Nonempty Entropy] in
/-- Averaging the first honest kernel is the existing honest experiment, including all adaptive answers. -/
theorem honest_original (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record) :
    (honestPrior passwords).bind (honestOnce attacker b g phrase usage empty) =
      (PMF.uniformOfFintype ((Public (width := width)) Password)).bind fun shared =>
        honest_game attacker.run passwords (tables b g shared.1 shared.2) empty phrase usage := by
  simp only [honestPrior, PMF.bind_bind, PMF.bind_map, Function.comp_def, honestOnce, honest_game, tables]

omit [Fintype Entropy] [Nonempty Entropy] in
/-- All later honest creation work is covered by the first-refusal loss, without conditioning away failure. -/
theorem honest_close (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (later : (HonestContext (width := width)) Password → PMF Bool) :
    Close ((PMF.uniformOfFintype ((Public (width := width)) Password)).bind fun shared =>
      honest_game attacker.run passwords (tables b g shared.1 shared.2) empty phrase usage)
      (honest attacker passwords b g phrase usage empty later) (2^(2*width):ENNReal)⁻¹ := by
  have hop := response_close (honestPrior passwords) (honestFlag b)
    (honestOnce attacker b g phrase usage empty) later
  rw [honest_flag_mass, honest_original attacker passwords b g phrase usage empty] at hop
  intro test
  exact (hop test).symm

/-- Theorem2 at a common branch width: full honest/prepared oracle games, actual budgets, and both refusal conventions. -/
theorem bound (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (injective : Function.Injective realPhrase) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → PMF Record)
    (preparedLater : (Context (width := width)) Password Entropy → Password → PMF Bool)
    (honestLater : (HonestContext (width := width)) Password → PMF Bool) :
    Close (prepared attacker passwords b g pack realPhrase phrase usage empty realRecords preparedLater)
      (honest attacker passwords b g phrase usage empty honestLater)
      (((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal)) := by
  have first := prepared_close attacker passwords p1 largest b g pack realPhrase phrase usage empty realRecords preparedLater
  have middle := middle_bound attacker passwords p1 largest b g pack realPhrase injective phrase usage empty realRecords
  rw [new_eq_honest attacker passwords b g pack phrase usage empty] at middle
  have last := honest_close attacker passwords b g phrase usage empty honestLater
  have combined := CloseComposition.trans _ _ _ _ _
    (CloseComposition.trans _ _ _ _ _ first middle) last
  convert combined using 1
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- Independent B/G tables and private adversary coins can be averaged without changing the bound. -/
theorem averaged_bound {Setup : Type} (law : PMF Setup)
    (attacker : Setup → (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : Setup → (BTable width)) (g : Setup → GTable Entropy) (pack : Setup → Entropy → (State width))
    (realPhrase : Setup → Entropy → Phrase) (injective : ∀ setup, Function.Injective (realPhrase setup))
    (phrase : Setup → State width → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Setup → Password → Entropy → (Tables width) Password Entropy → PMF Record)
    (preparedLater : Setup → (Context (width := width)) Password Entropy → Password → PMF Bool)
    (honestLater : Setup → (HonestContext (width := width)) Password → PMF Bool) :
    Close (law.bind fun setup => prepared (attacker setup) passwords (b setup) (g setup) (pack setup)
      (realPhrase setup) (phrase setup) usage empty (realRecords setup) (preparedLater setup))
      (law.bind fun setup => honest (attacker setup) passwords (b setup) (g setup) (phrase setup) usage empty (honestLater setup))
      (((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal)) := by
  have averaged := CloseComposition.bind law _ _ (fun _ =>
      ((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal))
    (fun setup => bound (attacker setup) passwords p1 largest (b setup) (g setup) (pack setup) (realPhrase setup) (injective setup)
      (phrase setup) usage empty (realRecords setup) (preparedLater setup) (honestLater setup))
  simpa only [constant] using averaged

omit [Fintype Entropy] [Nonempty Entropy] in
/-- One bit-width specialization covers all five normative source entropies and retains outer context. -/
theorem bits {Setup : Type} (ENT : Nat) (law : PMF Setup)
    (attacker : Setup → (Adversary (width := width)) Password (BitVec ENT) Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : Setup → (BTable width)) (g : Setup → GTable (BitVec ENT)) (pack : Setup → BitVec ENT → (State width))
    (realPhrase : Setup → BitVec ENT → Phrase) (injective : ∀ setup, Function.Injective (realPhrase setup))
    (phrase : Setup → State width → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Setup → Password → BitVec ENT → (Tables width) Password (BitVec ENT) → PMF Record)
    (preparedLater : Setup → (Context (width := width)) Password (BitVec ENT) → Password → PMF Bool)
    (honestLater : Setup → (HonestContext (width := width)) Password → PMF Bool) :
    Close (law.bind fun setup => prepared (attacker setup) passwords (b setup) (g setup) (pack setup)
      (realPhrase setup) (phrase setup) usage empty (realRecords setup) (preparedLater setup))
      (law.bind fun setup => honest (attacker setup) passwords (b setup) (g setup) (phrase setup) usage empty (honestLater setup))
      (((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(2^ENT:ENNReal)+12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal)) := by
  have estimate := averaged_bound law attacker passwords p1 largest b g pack realPhrase injective phrase usage empty
    realRecords preparedLater honestLater
  have cardinality : Fintype.card (BitVec ENT)=2^ENT := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Lemma3.bitEquivFin ENT)
  simpa only [cardinality, Nat.cast_pow, Nat.cast_ofNat] using estimate

omit [DecidableEq Password] [DecidableEq Phrase] [Fintype Password] [Fintype Entropy] [Nonempty Entropy] in
/-- The common error at h=128 is exactly the printed suite3 constant146. -/
theorem suite3_error (k q l ENT : Nat) (p1 : ENNReal) :
    ((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(2^ENT:ENNReal)+
      12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*128):ENNReal)=
    ((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(2^ENT:ENNReal)+(12*(q:ENNReal)+146)/(2^256:ENNReal) := by
  norm_num only [Nat.reduceMul]
  push_cast
  simp only [div_eq_mul_inv]
  ring

omit [DecidableEq Password] [DecidableEq Phrase] [Fintype Password] [Fintype Entropy] [Nonempty Entropy] in
/-- With the full raw suite4 source ENT=2h, source guesses and both refusals share denominator2^(2h). -/
theorem suite4_error (k q l : Nat) (p1 : ENNReal) :
    ((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(2^(2*width):ENNReal)+
      12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal)=
    ((k+2:Nat):ENNReal)*p1+((l+2:Nat):ENNReal)/(2^(2*width):ENNReal)+
      12*((q+12:Nat):ENNReal)/(2^256:ENNReal) := by
  push_cast
  simp only [div_eq_mul_inv]
  ring

end Theorem2

end
end MhfeLean
