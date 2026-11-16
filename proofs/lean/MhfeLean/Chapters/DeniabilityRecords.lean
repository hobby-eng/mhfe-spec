import MhfeLean.Chapters.DeniabilityGames

namespace MhfeLean
noncomputable section

/-! # Theorem 2 for a genuine-wallet record that may depend on the decoy opening

`Theorem2.bound` draws the genuine wallet's record from the genuine password, the source entropy
and the oracle tables, before the decoy password and the disclosed record are drawn. The supplement
lets the genuine wallet be used in any way. Here its record is drawn last, from a kernel that also
receives the container, the decoy password, the recovered decoy state and the realized disclosed
record. The bound is the one of `Theorem2.bound`: the genuine record is read only by a lookup of
the genuine phrase, which the bad event already charges. `Theorem2Records.independent` shows that
the experiment of `Theorem2.bound` is the case of a kernel that ignores the new arguments.
-/

namespace Theorem2Records
open DeniabilityModel ProbabilityTools
open GameExpectation MomentTools StatisticalClose
open DeniabilityInteraction DeniabilityBound
variable {width : Nat}
variable {Password Entropy Phrase Record : Type} [DecidableEq Password] [DecidableEq Phrase]
  {k q l : Nat}
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] DeniabilityPrivate.cipher DeniabilityPrivate.key
  TranscriptErasure.execute DeniabilityModel.execute recover
  DeniabilityModel.cipher

/-- One opening whose genuine record is drawn after the disclosed record, from the recovered decoy
state and that record. -/
def disclosure (program : (Program (width := width)) Password Entropy Phrase Record)
    (base : (Tables width) Password Entropy) (realPhrase : Phrase) (empty : Record)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record)
    (genuine : (State width) → Record → PMF Record)
    (container : (State width)) (password : Password) : PMF Bool :=
  (usage (phrase (recover base password container).1.1)).bind fun record =>
    (genuine (recover base password container).1.1 record).map fun realRecord =>
      (finish program base (PreparedDisclosure.realOracle realPhrase realRecord empty)
        phrase container password record).result

omit [DecidableEq Password] in
/-- The result of an opening, written as a draw of the disclosed record. -/
theorem opening_result (program : (Program (width := width)) Password Entropy Phrase Record)
    (base : (Tables width) Password Entropy) (records : Phrase → Record)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record)
    (container : (State width)) (password : Password) :
    (opening program base records phrase usage container password).map Run.result =
      (usage (phrase (recover base password container).1.1)).bind fun record =>
        PMF.pure (finish program base records phrase container password record).result := by
  simp only [opening, PMF.map_comp]
  rfl

/-- Equal until bad for a genuine record drawn from the realized disclosure: on a clean run the
record is never read, whatever its law. -/
theorem disclosure_close (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (real disclosed : Password) (base : (Tables width) Password Entropy) (source container : (State width))
    (row : Salt → Key) (spare : (HTable width)) (realPhrase : Phrase) (empty : Record)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record)
    (genuine : (State width) → Record → PMF Record) :
    Close (disclosure attacker.run base realPhrase empty phrase usage genuine container disclosed)
      ((opening attacker.run (erased real base source row spare) (fun _ => empty)
        phrase usage container disclosed).map Run.result)
      (((usage (phrase (recover (erased real base source row spare) disclosed container).1.1)).map fun record =>
        signatureBad real realPhrase
          (DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h))
          (summary attacker (erased real base source row spare) (fun _ => empty) phrase container disclosed record)) true) := by
  classical
  let badR := fun record : Record => signatureBad real realPhrase
    (DeniabilityPrivate.key base.b source (fun salt => base.a (real,salt),base.h))
    (summary attacker (erased real base source row spare) (fun _ => empty) phrase container disclosed record)
  by_cases possible : ∃ record, badR record=false
  · obtain ⟨witness, clean⟩ := possible
    have state_eq : (recover base disclosed container).1.1 =
        (recover (erased real base source row spare) disclosed container).1.1 := by
      have same := congrArg Run.recovered (same_if_clean attacker real disclosed base source container
        row spare realPhrase witness empty phrase witness clean)
      simpa only [finish] using same
    have perRecord (record : Record) :
        Close ((genuine (recover (erased real base source row spare) disclosed container).1.1 record).map
            fun realRecord => (finish attacker.run base
              (PreparedDisclosure.realOracle realPhrase realRecord empty) phrase container disclosed record).result)
          (PMF.pure (finish attacker.run (erased real base source row spare) (fun _ => empty)
            phrase container disclosed record).result)
          (if badR record then 1 else 0) := by
      cases found : badR record with
      | false =>
        have constant : (fun realRecord : Record => (finish attacker.run base
              (PreparedDisclosure.realOracle realPhrase realRecord empty) phrase container disclosed record).result) =
            Function.const Record (finish attacker.run (erased real base source row spare) (fun _ => empty)
              phrase container disclosed record).result := by
          funext realRecord
          exact congrArg Run.result (same_if_clean attacker real disclosed base source container
            row spare realPhrase realRecord empty phrase record found)
        rw [constant, PMF.map_const]
        exact of_eq _ _ rfl
      | true =>
        intro test
        constructor
        · exact (PMF.coe_le_one _ true).trans (le_add_of_nonneg_left (zero_le))
        · exact (PMF.coe_le_one _ true).trans (le_add_of_nonneg_left (zero_le))
    have combined := CloseComposition.bind
      (usage (phrase (recover (erased real base source row spare) disclosed container).1.1)) _ _ _ perRecord
    rw [← MomentTools.probability] at combined
    rw [opening_result]
    unfold disclosure
    rw [state_eq]
    exact combined
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

variable [Fintype Password] [Fintype Entropy] [Nonempty Entropy]

/-- The first unconditional opening. The genuine record's kernel receives the genuine password,
the entropy, the tables and the container, then the decoy password, the recovered decoy state and
the disclosed record. -/
def once (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → (State width) →
      Password → (State width) → Record → PMF Record)
    (context : (Theorem2.Context (width := width)) Password Entropy) (disclosed : Password) : PMF Bool :=
  disclosure attacker.run (Theorem2.originalTables b g context.2.2) (realPhrase context.2.1) empty phrase usage
    (realRecords context.1 context.2.1 (Theorem2.originalTables b g context.2.2)
      (Theorem2.sig context.1 b (pack context.2.1) context.2.2).1 disclosed)
    (Theorem2.sig context.1 b (pack context.2.1) context.2.2).1 disclosed

/-- The opening before either redraw rule, with the decoy password drawn. -/
def kernel (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → (State width) →
      Password → (State width) → Record → PMF Record)
    (context : (Theorem2.Context (width := width)) Password Entropy) : PMF Bool :=
  passwords.bind fun disclosed =>
    once attacker b g pack realPhrase phrase usage empty realRecords context disclosed

omit [Fintype Password] [Fintype Entropy] [Nonempty Entropy] in
/-- The middle hop for the dependent record, with the error of `Theorem2.conditional_close`. -/
theorem conditional_close (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → (State width) →
      Password → (State width) → Record → PMF Record)
    (context : (Theorem2.Context (width := width)) Password Entropy) :
    Close (kernel attacker passwords b g pack realPhrase phrase usage empty realRecords context)
      (Theorem2.newKernel attacker passwords b g pack phrase usage empty context)
      (Theorem2.errorKernel attacker passwords b g pack realPhrase phrase usage empty context) := by
  rcases context with ⟨real,entropy,sample⟩
  have across := CloseComposition.bind passwords _ _ _
    (fun disclosed => disclosure_close attacker real disclosed (Theorem2.originalTables b g sample)
      (pack entropy) (Theorem2.sig real b (pack entropy) sample).1 sample.1.2 sample.2.2
      (realPhrase entropy) empty phrase usage
      (realRecords real entropy (Theorem2.originalTables b g sample)
        (Theorem2.sig real b (pack entropy) sample).1 disclosed))
  simpa only [kernel, once, Theorem2.newKernel, Theorem2.errorKernel, observe, Theorem2.changed, Theorem2.sig,
    Theorem2.originalTables, Theorem2.tables,
    PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_apply, moment] using across

/-- The middle hop with the bound of `Theorem2.middle_bound`. -/
theorem middle_bound (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (injective : Function.Injective realPhrase) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → (State width) →
      Password → (State width) → Record → PMF Record) :
    Close ((Theorem2.prior passwords).bind (kernel attacker passwords b g pack realPhrase phrase usage empty realRecords))
      ((Theorem2.prior passwords).bind (Theorem2.newKernel attacker passwords b g pack phrase usage empty))
      (((k+1:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal)) := by
  have hop := CloseComposition.bind (Theorem2.prior passwords) _ _ _
    (conditional_close attacker passwords b g pack realPhrase phrase usage empty realRecords)
  exact StatisticalClose.mono _ _ _ _ hop
    (Theorem2.error_bound attacker passwords p1 largest b g pack realPhrase injective phrase usage empty)

/-- The prepared experiment: on a refused first draw, `later` is arbitrary, as in `Theorem2.prepared`. -/
def prepared (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → (State width) →
      Password → (State width) → Record → PMF Record)
    (later : (Theorem2.Context (width := width)) Password Entropy → Password → PMF Bool) : PMF Bool :=
  (Theorem2.prior passwords).bind fun context => passwords.bind fun disclosed =>
    if Theorem2.preparedFlag b pack context disclosed then later context disclosed else
      once attacker b g pack realPhrase phrase usage empty realRecords context disclosed

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

/-- Both prepared refusals are charged before conditioning, as in `Theorem2.prepared_close`. -/
theorem prepared_close (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → (State width) →
      Password → (State width) → Record → PMF Record)
    (later : (Theorem2.Context (width := width)) Password Entropy → Password → PMF Bool) :
    Close (prepared attacker passwords b g pack realPhrase phrase usage empty realRecords later)
      ((Theorem2.prior passwords).bind (kernel attacker passwords b g pack realPhrase phrase usage empty realRecords))
      (p1+(2^(2*width):ENNReal)⁻¹) := by
  have per (context : (Theorem2.Context (width := width)) Password Entropy) := response_close passwords
    (Theorem2.preparedFlag b pack context)
    (once attacker b g pack realPhrase phrase usage empty realRecords context) (later context)
  have combined := CloseComposition.bind (Theorem2.prior passwords) _ _ _ per
  exact StatisticalClose.mono _ _ _ _ combined (Theorem2.prepared_flag_bound passwords p1 largest b pack)

/-- Theorem 2 with a genuine-wallet record that may depend on the whole realized disclosure: the
genuine password, entropy, tables and container, the decoy password, the recovered decoy state and
the disclosed record. The honest experiment and the bound are those of `Theorem2.bound`. -/
theorem bound (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (injective : Function.Injective realPhrase) (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → (State width) →
      Password → (State width) → Record → PMF Record)
    (preparedLater : (Theorem2.Context (width := width)) Password Entropy → Password → PMF Bool)
    (honestLater : (Theorem2.HonestContext (width := width)) Password → PMF Bool) :
    Close (prepared attacker passwords b g pack realPhrase phrase usage empty realRecords preparedLater)
      (Theorem2.honest attacker passwords b g phrase usage empty honestLater)
      (((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal)) := by
  have first := prepared_close attacker passwords p1 largest b g pack realPhrase phrase usage empty realRecords preparedLater
  have middle := middle_bound attacker passwords p1 largest b g pack realPhrase injective phrase usage empty realRecords
  rw [Theorem2.new_eq_honest attacker passwords b g pack phrase usage empty] at middle
  have last := Theorem2.honest_close attacker passwords b g phrase usage empty honestLater
  have combined := CloseComposition.trans _ _ _ _ _
    (CloseComposition.trans _ _ _ _ _ first middle) last
  convert combined using 1
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- Independent B/G tables and private adversary coins are averaged as in `Theorem2.averaged_bound`. -/
theorem averaged_bound {Setup : Type} (law : PMF Setup)
    (attacker : Setup → (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : Setup → (BTable width)) (g : Setup → GTable Entropy) (pack : Setup → Entropy → (State width))
    (realPhrase : Setup → Entropy → Phrase) (injective : ∀ setup, Function.Injective (realPhrase setup))
    (phrase : Setup → State width → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Setup → Password → Entropy → (Tables width) Password Entropy → (State width) →
      Password → (State width) → Record → PMF Record)
    (preparedLater : Setup → (Theorem2.Context (width := width)) Password Entropy → Password → PMF Bool)
    (honestLater : Setup → (Theorem2.HonestContext (width := width)) Password → PMF Bool) :
    Close (law.bind fun setup => prepared (attacker setup) passwords (b setup) (g setup) (pack setup)
      (realPhrase setup) (phrase setup) usage empty (realRecords setup) (preparedLater setup))
      (law.bind fun setup => Theorem2.honest (attacker setup) passwords (b setup) (g setup) (phrase setup) usage empty (honestLater setup))
      (((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+
        12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal)) := by
  have averaged := CloseComposition.bind law _ _ (fun _ =>
      ((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(Fintype.card Entropy:ENNReal)+12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal))
    (fun setup => bound (attacker setup) passwords p1 largest (b setup) (g setup) (pack setup) (realPhrase setup) (injective setup)
      (phrase setup) usage empty (realRecords setup) (preparedLater setup) (honestLater setup))
  simpa only [constant] using averaged

omit [Fintype Entropy] [Nonempty Entropy] in
/-- The bit-width form, as `Theorem2.bits`; `Theorem2.suite3_error` and `Theorem2.suite4_error`
give the printed constants. -/
theorem bits {Setup : Type} (ENT : Nat) (law : PMF Setup)
    (attacker : Setup → (Adversary (width := width)) Password (BitVec ENT) Phrase Record k q l) (passwords : PMF Password)
    (p1 : ENNReal) (largest : ∀ password, passwords password ≤ p1)
    (b : Setup → (BTable width)) (g : Setup → GTable (BitVec ENT)) (pack : Setup → BitVec ENT → (State width))
    (realPhrase : Setup → BitVec ENT → Phrase) (injective : ∀ setup, Function.Injective (realPhrase setup))
    (phrase : Setup → State width → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Setup → Password → BitVec ENT → (Tables width) Password (BitVec ENT) → (State width) →
      Password → (State width) → Record → PMF Record)
    (preparedLater : Setup → (Theorem2.Context (width := width)) Password (BitVec ENT) → Password → PMF Bool)
    (honestLater : Setup → (Theorem2.HonestContext (width := width)) Password → PMF Bool) :
    Close (law.bind fun setup => prepared (attacker setup) passwords (b setup) (g setup) (pack setup)
      (realPhrase setup) (phrase setup) usage empty (realRecords setup) (preparedLater setup))
      (law.bind fun setup => Theorem2.honest (attacker setup) passwords (b setup) (g setup) (phrase setup) usage empty (honestLater setup))
      (((k+2:Nat):ENNReal)*p1+(l:ENNReal)/(2^ENT:ENNReal)+12*((q+12:Nat):ENNReal)/(2^256:ENNReal)+2/(2^(2*width):ENNReal)) := by
  have estimate := averaged_bound law attacker passwords p1 largest b g pack realPhrase injective phrase usage empty
    realRecords preparedLater honestLater
  have cardinality : Fintype.card (BitVec ENT)=2^ENT := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Lemma3.bitEquivFin ENT)
  simpa only [cardinality, Nat.cast_pow, Nat.cast_ofNat] using estimate

/-- The experiment of `Theorem2.bound` is the case of a kernel that ignores the container and the
decoy opening. -/
theorem independent (attacker : (Adversary (width := width)) Password Entropy Phrase Record k q l) (passwords : PMF Password)
    (b : (BTable width)) (g : GTable Entropy) (pack : Entropy → (State width)) (realPhrase : Entropy → Phrase)
    (phrase : (State width) → Phrase) (usage : Phrase → PMF Record) (empty : Record)
    (realRecords : Password → Entropy → (Tables width) Password Entropy → PMF Record)
    (later : (Theorem2.Context (width := width)) Password Entropy → Password → PMF Bool) :
    Theorem2.prepared attacker passwords b g pack realPhrase phrase usage empty realRecords later =
      prepared attacker passwords b g pack realPhrase phrase usage empty
        (fun real entropy tables _ _ _ _ => realRecords real entropy tables) later := by
  unfold Theorem2.prepared prepared
  apply congrArg (fun next => (Theorem2.prior passwords).bind next)
  funext context
  apply congrArg (fun next => passwords.bind next)
  funext disclosed
  cases Theorem2.preparedFlag b pack context disclosed with
  | true => rfl
  | false =>
    change Theorem2.preparedOnce attacker b g pack realPhrase phrase usage empty realRecords context disclosed =
      once attacker b g pack realPhrase phrase usage empty
        (fun real entropy tables _ _ _ _ => realRecords real entropy tables) context disclosed
    unfold Theorem2.preparedOnce once disclosure
    simp only [opening_result]
    exact PMF.bind_comm _ _ _

end Theorem2Records

/-! The two sampling orders give different joint laws of the two records: a genuine record drawn
before a fresh fair disclosed record agrees with it with probability one half, whatever its law,
and a genuine record drawn afterwards can copy it. This separates the experiments of
`Theorem2.bound` and `Theorem2Records.bound`; it is not a distinguishing attack, since the genuine
record is read only by a lookup of the genuine phrase. -/
namespace RecordOrder
open GameExpectation MomentTools

/-- A Boolean record drawn independently of a fair one agrees with it with probability one half. -/
theorem independent_agreement (genuine : PMF Bool) :
    (genuine.bind fun realRecord =>
      (PMF.uniformOfFintype Bool).map fun record => decide (record=realRecord)) true = 2⁻¹ := by
  have fixed (realRecord : Bool) :
      ((PMF.uniformOfFintype Bool).map fun record => decide (record=realRecord)) true = 2⁻¹ := by
    rw [PointMassEvent.equality, PMF.uniformOfFintype_apply, Fintype.card_bool]
    norm_num
  rw [PMF.bind_apply]
  simp_rw [fixed]
  rw [ENNReal.tsum_mul_right, genuine.tsum_coe, one_mul]

/-- A Boolean record drawn after a fair one can copy it. -/
theorem copied_agreement :
    ((PMF.uniformOfFintype Bool).bind fun record =>
      (PMF.pure record).map fun realRecord => decide (record=realRecord)) true = 1 := by
  have fixed (record : Bool) :
      ((PMF.pure record).map fun realRecord => decide (record=realRecord)) = PMF.pure true := by
    rw [PMF.pure_map]
    simp only [decide_true]
  simp_rw [fixed]
  rw [PMF.bind_const]
  exact PMF.pure_apply_self true

end RecordOrder

end
end MhfeLean
