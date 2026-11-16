/- long: the three cached-search modes share one operational attack and counting proof. -/
-- long: W7 keeps its executable cached attack and both probability/source arguments in one mathematical chapter.
import MhfeLean.Chapters.WalletMatching
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

namespace WalletPairPort

/-- Port to Lean 4.35: `simp` now rewrites `x >>= fun a => pure (f a)` to `f <$> x` before the
transcript laws apply; this is the transcript law for that form. -/
theorem transcript_map {Point Result Output : Type} {spec : OracleSpec Point}
    (table : TranscriptErasure.Table spec) (program : OracleComp spec Result) (transform : Result → Output) :
    TranscriptErasure.execute table (transform <$> program)=
      (transform (TranscriptErasure.execute table program).1,(TranscriptErasure.execute table program).2) := by
  rw [← bind_pure_comp,TranscriptErasure.execute_bind]
  simp only [TranscriptErasure.execute_pure,List.append_nil]

end WalletPairPort

/-! # Proposition W7: cached phrase recovery and ordered pair search

The program pays for each MHFE inversion once. Further passphrase tests reuse
that recovered entropy. A preceding match with the genuine seed wins the seed
game even if its password/passphrase pair is wrong.
-/

namespace W7Attack
open Gamma2Model WalletCryptoCompiler
variable {Password Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Passphrase]
  [DecidableEq Seed] [DecidableEq Data]

abbrev Wallet (Entropy Passphrase Seed Check Tail Data : Type) :=
  SeedWalletModel.Tables Entropy Passphrase Seed Check Tail Data
abbrev WalletSpec (Entropy Passphrase Seed Check Tail Data : Type) :=
  SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data
abbrev FullSpec (Password Entropy Passphrase Seed Check Tail Data : Type) :=
  combinedSpec (Password := Password) (Entropy := Entropy)
    (SeedWalletModel.spec Entropy Passphrase Seed Check Tail Data)
abbrev Output (Password Passphrase Seed : Type) := (Password × Passphrase) × Seed

def recoverRows (coordinates : Entropy ≃ State) (container : State) (salt : Half) :
    List Password → OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) (Password → Entropy)
  | [] => pure (fun _ => coordinates.symm (0,0))
  | password :: rest => do
    let source ← CryptoEmbedding.embed (WalletSpec Entropy Passphrase Seed Check Tail Data) (SharedInverse.recover password container salt)
    let cached ← recoverRows coordinates container salt rest
    pure (Function.update cached password (coordinates.symm source))

/-- All verifier modes use the same S-query and first-match loop. -/
def runUsing (cache : Password → Entropy)
    (probe : Seed → OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool)
    (fallback : Output Password Passphrase Seed) : List (Password × Passphrase) →
      OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) (Output Password Passphrase Seed)
  | [] => pure fallback
  | pair :: rest => do
    let seed : Seed ← TranscriptErasure.ask
      (spec := FullSpec Password Entropy Passphrase Seed Check Tail Data) (.inr (.s (cache pair.1) pair.2))
    let passes ← probe seed
    if passes then pure (pair,seed) else runUsing cache probe fallback rest

def walletProbe (data : Data) (seed : Seed) :
    OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool := do
  let found : Data ← TranscriptErasure.ask
    (spec := FullSpec Password Entropy Passphrase Seed Check Tail Data) (.inr (.omega seed))
  pure (decide (found=data))

/-- The original wallet-only search is the wallet probe instance of the common loop. -/
def run (cache : Password → Entropy) (data : Data) (fallback : Output Password Passphrase Seed)
    (pairs : List (Password × Passphrase)) :
    OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) (Output Password Passphrase Seed) :=
  runUsing cache (walletProbe data) fallback pairs

/-- Row inversion is shared by every verifier; only the seed probe changes. -/
def attackUsing (coordinates : Entropy ≃ State) (rows : List Password)
    (pairs : List (Password × Passphrase)) (fallback : Output Password Passphrase Seed)
    (probe : Seed → OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool)
    (container : State) :
    OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) (Output Password Passphrase Seed) := do
  let salt : Half ← TranscriptErasure.ask
    (spec := FullSpec Password Entropy Passphrase Seed Check Tail Data) (.inl (.b 11 container.1))
  let cache ← recoverRows coordinates container salt rows
  runUsing cache probe fallback pairs

/-- Only Y and the public wallet reference enter the attack; P,Q and seed* do not. -/
def attack (coordinates : Entropy ≃ State) (rows : List Password)
    (pairs : List (Password × Passphrase)) (fallback : Output Password Passphrase Seed)
    (data : Data) (container : State) :
    OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) (Output Password Passphrase Seed) :=
  attackUsing coordinates rows pairs fallback (walletProbe data) container

attribute [local irreducible] SharedInverse.recover Gamma2Model.execute
  TranscriptErasure.execute

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] in
/-- Full recovery values and logs for the cache, with the initial B query already shared. -/
theorem recover_execution (coordinates : Entropy ≃ State) (container : State)
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (rows : List Password) :
    TranscriptErasure.execute (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (recoverRows coordinates container (crypto.b (11,container.1)) rows) =
    ((fun password => if password ∈ rows then
        coordinates.symm (execute crypto (finalize password 12 container (by omega))).1.1
      else coordinates.symm (0,0)),
      rows.flatMap fun password =>
        (execute crypto (SharedInverse.recover password container (crypto.b (11,container.1)))).2.map Sum.inl) := by
  induction rows with
  | nil => simp only [recoverRows, TranscriptErasure.execute_pure, List.not_mem_nil,
      if_false, List.flatMap_nil]
  | cons password rest ih =>
    simp only [recoverRows, TranscriptErasure.execute_bind, CryptoEmbedding.execution,
      TranscriptErasure.execute_pure]
    rw [ih, SharedInverse.execution]
    apply Prod.ext
    · funext other
      by_cases same : other=password
      · subst other
        simp only [Function.update_self, List.mem_cons_self, if_true]
      · simp only [Function.update_of_ne same, List.mem_cons, same, false_or]
    · simp only [List.flatMap_cons, List.append_nil, SharedInverse.execution]

omit [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] in
/-- Any seed probe gives the same first-match search semantics. -/
theorem runUsing_result (cache : Password → Entropy)
    (probe : Seed → OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool)
    (fallback : Output Password Passphrase Seed) (crypto : Tables Password Entropy)
    (wallet : Wallet Entropy Passphrase Seed Check Tail Data) (pairs : List (Password × Passphrase)) :
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (runUsing cache probe fallback pairs)).1 =
    FirstPass.choose (fun item : Output Password Passphrase Seed =>
      (TranscriptErasure.execute
        (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
        (probe item.2)).1) fallback (pairs.map fun pair => (pair,wallet.s (cache pair.1,pair.2))) := by
  induction pairs with
  | nil => simp only [runUsing, TranscriptErasure.execute_pure, List.map_nil, FirstPass.choose]
  | cons pair rest ih =>
    simp only [runUsing, TranscriptErasure.execute_bind, TranscriptErasure.execute_ask,
      combinedAnswer, SeedWalletModel.answer, List.map_cons, FirstPass.choose]
    split_ifs <;> simp only [TranscriptErasure.execute_pure, ih]

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] in
/-- Cached inversion costs add over rows, for any query counter. -/
theorem recover_count (coordinates : Entropy ≃ State) (container : State)
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (rows : List Password)
    (tag : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed → Bool)
    (cost : Nat)
    (per : ∀ password, ((execute crypto (SharedInverse.recover password container (crypto.b (11,container.1)))).2.map Sum.inl).countP tag=cost) :
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (recoverRows coordinates container (crypto.b (11,container.1)) rows)).2.countP tag=rows.length*cost := by
  rw [recover_execution]
  change (rows.flatMap fun password =>
    (execute crypto (SharedInverse.recover password container (crypto.b (11,container.1)))).2.map Sum.inl).countP tag=rows.length*cost
  induction rows with
  | nil => simp only [List.flatMap_nil, List.countP_nil, List.length_nil, Nat.zero_mul]
  | cons password rest ih =>
    rw [List.flatMap_cons, List.countP_append, per password, ih]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

omit [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] in
/-- Loop cost is one S query plus the actual probe cost for each tested pair. -/
theorem runUsing_count (cache : Password → Entropy)
    (probe : Seed → OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool)
    (fallback : Output Password Passphrase Seed) (crypto : Tables Password Entropy)
    (wallet : Wallet Entropy Passphrase Seed Check Tail Data) (pairs : List (Password × Passphrase))
    (tag : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed → Bool)
    (cost : Nat)
    (per : ∀ entropy phrase seed, (if tag (.inr (.s entropy phrase)) then 1 else 0)+
      (TranscriptErasure.execute
        (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
        (probe seed)).2.countP tag ≤ cost) :
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (runUsing cache probe fallback pairs)).2.countP tag ≤ pairs.length*cost := by
  induction pairs with
  | nil => simp only [runUsing, TranscriptErasure.execute_pure, List.countP_nil, List.length_nil,
      Nat.zero_mul, le_refl]
  | cons pair rest ih =>
    have head := per (cache pair.1) pair.2 (wallet.s (cache pair.1,pair.2))
    simp only [runUsing, TranscriptErasure.execute_bind, TranscriptErasure.execute_ask,
      combinedAnswer, SeedWalletModel.answer]
    split_ifs
    all_goals
      simp only [TranscriptErasure.execute_pure, List.singleton_append, List.countP_cons,
        List.countP_append, List.countP_nil, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

omit [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] in
/-- A per-probe equality of counters is preserved by early stopping in the common loop. -/
theorem runUsing_balance (cache : Password → Entropy)
    (probe : Seed → OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool)
    (fallback : Output Password Passphrase Seed) (crypto : Tables Password Entropy)
    (wallet : Wallet Entropy Passphrase Seed Check Tail Data) (pairs : List (Password × Passphrase))
    (left right : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed → Bool)
    (sameS : ∀ e q, left (.inr (.s e q))=right (.inr (.s e q)))
    (sameProbe : ∀ seed, let queries := (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (probe seed)).2; queries.countP left=queries.countP right) :
    let queries := (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (runUsing cache probe fallback pairs)).2
    queries.countP left=queries.countP right := by
  induction pairs with
  | nil => simp only [runUsing, TranscriptErasure.execute_pure, List.countP_nil]
  | cons pair rest ih =>
    have head := sameProbe (wallet.s (cache pair.1,pair.2))
    simp only [runUsing, TranscriptErasure.execute_bind, TranscriptErasure.execute_ask,
      combinedAnswer, SeedWalletModel.answer]
    split_ifs
    all_goals
      simp only [TranscriptErasure.execute_pure, List.singleton_append, List.countP_cons,
        List.countP_append, List.countP_nil, sameS]
      omega

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] in
/-- All verifier modes share the same cache cost and add only their own seed-probe costs. -/
theorem attackUsing_count (coordinates : Entropy ≃ State) (container : State)
    (probe : Seed → OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool)
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (rows : List Password) (pairs : List (Password × Passphrase)) (fallback : Output Password Passphrase Seed)
    (tag : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed → Bool)
    (rowCost pairCost : Nat)
    (rowPer : ∀ password,
      ((execute crypto (SharedInverse.recover password container (crypto.b (11,container.1)))).2.map Sum.inl).countP tag=rowCost)
    (pairPer : ∀ entropy phrase seed, (if tag (.inr (.s entropy phrase)) then 1 else 0)+
      (TranscriptErasure.execute
        (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
        (probe seed)).2.countP tag ≤ pairCost) :
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (attackUsing coordinates rows pairs fallback probe container)).2.countP tag ≤
      rows.length*rowCost+pairs.length*pairCost+(if tag (.inl (.b 11 container.1)) then 1 else 0) := by
  have cached := recover_count coordinates container crypto wallet rows tag rowCost rowPer
  have tested := runUsing_count
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (recoverRows coordinates container (crypto.b (11,container.1)) rows)).1
    probe fallback crypto wallet pairs tag pairCost pairPer
  simp only [attackUsing, TranscriptErasure.execute_bind, TranscriptErasure.execute_ask,
    combinedAnswer, answer, List.singleton_append, List.countP_cons, List.countP_append]
  omega

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] in
/-- The actual cache and any probe yield the same evaluated candidate list. -/
theorem attackUsing_result (coordinates : Entropy ≃ State) (rows : List Password) (pairs : List (Password × Passphrase))
    (covered : ∀ pair ∈ pairs, pair.1 ∈ rows) (fallback : Output Password Passphrase Seed)
    (probe : Seed → OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool)
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data) (container : State) :
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (attackUsing coordinates rows pairs fallback probe container)).1 =
    FirstPass.choose (fun item : Output Password Passphrase Seed =>
      (TranscriptErasure.execute
        (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
        (probe item.2)).1) fallback (pairs.map fun pair =>
          (pair,wallet.s (coordinates.symm (execute crypto (finalize pair.1 12 container (by omega))).1.1,pair.2))) := by
  simp only [attackUsing, TranscriptErasure.execute_bind, TranscriptErasure.execute_ask,
    combinedAnswer, answer]
  rw [recover_execution, runUsing_result]
  congr 1
  apply List.map_congr_left
  intro pair member
  simp only [if_pos (covered pair member)]

def isS (point : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed) : Bool :=
  (SeedQueryMetadata.extract SeedWalletModel.seedPair point).isSome

/-- The deterministic candidate entropy is the actual twelve-round inverse, not an additional oracle answer. -/
def entropy (coordinates : Entropy ≃ State) (crypto : Tables Password Entropy) (container : State)
    (password : Password) : Entropy :=
  coordinates.symm (execute crypto (finalize password 12 container (by omega))).1.1

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] in
/-- The complete cached program returns the same first match as the mathematical pair list. -/
theorem result (coordinates : Entropy ≃ State) (rows : List Password)
    (pairs : List (Password × Passphrase)) (covered : ∀ pair ∈ pairs, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (crypto : Tables Password Entropy)
    (wallet : Wallet Entropy Passphrase Seed Check Tail Data) (data : Data) (container : State) :
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (attack coordinates rows pairs fallback data container)).1 =
    FirstPass.choose (fun item : Output Password Passphrase Seed => decide (wallet.omega item.2=data))
      fallback (pairs.map fun pair => (pair,wallet.s (entropy coordinates crypto container pair.1,pair.2))) := by
  simpa only [attack,walletProbe,TranscriptErasure.execute_bind,
    TranscriptErasure.execute_ask,TranscriptErasure.execute_pure,
    combinedAnswer,SeedWalletModel.answer,entropy] using
    attackUsing_result coordinates rows pairs covered fallback (walletProbe data) crypto wallet container

end W7Attack

namespace FirstPass
variable {Item : Type}

/-- Passing before the true candidate is harmless whenever that passing value is itself successful. -/
theorem good_before (test : Item → Bool) (good : Item → Prop) (fallback real : Item)
    (earlier later : List Item) (good_real : good real) (pass_real : test real=true)
    (harmless : ∀ item ∈ earlier, test item=true → good item) :
    good (choose test fallback (earlier++real::later)) := by
  induction earlier with
  | nil => simpa only [List.nil_append, choose, pass_real, ite_true] using good_real
  | cons first rest ih =>
    by_cases pass : test first=true
    · simpa only [List.cons_append, choose, pass, ite_true] using harmless first List.mem_cons_self pass
    · simp only [List.cons_append, choose, pass]
      exact ih (fun item member => harmless item (List.mem_cons_of_mem first member))

end FirstPass

namespace W7FalseMatch
open ProbabilityTools GameExpectation MomentTools

/-- A single value of an ideal finite function has the uniform point-match probability. -/
private theorem uniform_equal {Input Answer : Type} [Fintype Input] [DecidableEq Input]
    [Fintype Answer] [Nonempty Answer] [DecidableEq Answer] (point : Input) (target : Answer) :
    moment (PMF.uniformOfFintype (Input → Answer)) (fun table => if table point=target then 1 else 0) =
      (Fintype.card Answer:ENNReal)⁻¹ := by
  letI : Nonempty Input := ⟨point⟩
  have single : moment (PMF.uniformOfFintype Answer) (fun answer => if answer=target then 1 else 0) =
      (PMF.uniformOfFintype Answer) target := by
    unfold moment
    simp only [mul_ite, mul_one, mul_zero]
    exact tsum_ite_eq target (fun answer => (PMF.uniformOfFintype Answer) answer)
  have law := congrArg (fun distribution : PMF Answer =>
      moment distribution (fun answer => if answer=target then 1 else 0)) (uniform_eval point)
  simpa only [moment_map, Function.comp_def, single, PMF.uniformOfFintype_apply] using law

variable {Input Seed Data : Type} [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]
  [Fintype Data] [Nonempty Data] [DecidableEq Data]

omit [Nonempty Seed] in
/-- The genuine seed passes with certainty; every other fixed seed has the ideal wallet-match rate. -/
theorem exact_match (target candidate : Seed) (data : Data) :
    moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
      if Function.update omega target data candidate=data then 1 else 0) =
      if candidate=target then 1 else (Fintype.card Data:ENNReal)⁻¹ := by
  by_cases same : candidate=target
  · subst candidate
    simp only [Function.update_self, ite_true, MomentTools.constant]
  · simpa only [Function.update_of_ne same, if_neg same] using uniform_equal candidate data

omit [Nonempty Seed] in
/-- A preceding match is harmful to seed recovery only when its seed differs from the genuine one. -/
theorem harmful_bound (target candidate : Seed) (data : Data) :
    moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
      if candidate ≠ target ∧ Function.update omega target data candidate=data then 1 else 0) ≤
      (Fintype.card Data:ENNReal)⁻¹ := by
  by_cases same : candidate=target
  · simp [same, MomentTools.constant]
  · have law := exact_match target candidate data
    rw [if_neg same] at law
    simpa only [ne_eq, same, not_false_eq_true, true_and] using le_of_eq law

variable [Fintype Input] [DecidableEq Input]

/-- At an unprogrammed seed-function input, a wrong pair can also collide with the genuine seed. -/
theorem off_input_bound (real point : Input) (different : point ≠ real) (target : Seed) (data : Data) :
    moment (PMF.uniformOfFintype (Input → Seed)) (fun s =>
      moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
        if Function.update omega target data (Function.update s real target point)=data then 1 else 0)) ≤
      (Fintype.card Data:ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹ := by
  have fixed (s : Input → Seed) :
      moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
        if Function.update omega target data (Function.update s real target point)=data then 1 else 0) =
      if s point=target then 1 else (Fintype.card Data:ENNReal)⁻¹ := by
    rw [Function.update_of_ne different]
    exact exact_match target (s point) data
  rw [show (fun s : Input → Seed =>
    moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
      if Function.update omega target data (Function.update s real target point)=data then 1 else 0)) =
    (fun s => if s point=target then 1 else (Fintype.card Data:ENNReal)⁻¹) from funext fixed]
  have pointwise (s : Input → Seed) :
      (if s point=target then 1 else (Fintype.card Data:ENNReal)⁻¹) ≤
        (Fintype.card Data:ENNReal)⁻¹+(if s point=target then 1 else 0) := by
    by_cases same : s point=target
    · simp only [if_pos same]
      exact le_add_of_nonneg_left (zero_le)
    · simp only [if_neg same, add_zero, le_refl]
  calc
    _ ≤ moment (PMF.uniformOfFintype (Input → Seed)) (fun s =>
      (Fintype.card Data:ENNReal)⁻¹+(if s point=target then 1 else 0)) := mono _ _ _ pointwise
    _ = _ := by rw [MomentTools.add, MomentTools.constant, uniform_equal]

omit [Fintype Input] [DecidableEq Input] [Nonempty Seed] in
/-- The first-match seed loss counts harmful preceding matches, without requiring their independence. -/
theorem seed_success {Pair : Type} (candidate : Pair → Seed) (real : Pair) (target : Seed)
    (real_seed : candidate real=target) (data : Data) (fallback : Pair × Seed)
    (earlier later : List Pair) :
    1-(earlier.length:ENNReal)*(Fintype.card Data:ENNReal)⁻¹ ≤
      moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
        if (FirstPass.choose
          (fun item : Pair × Seed => decide (Function.update omega target data item.2=data)) fallback
          ((earlier++real::later).map fun pair => (pair,candidate pair))).2=target then 1 else 0) := by
  classical
  let test := fun omega : Seed → Data => fun item : Pair × Seed =>
    decide (Function.update omega target data item.2=data)
  let win := fun omega : Seed → Data => decide ((FirstPass.choose (test omega) fallback
    ((earlier++real::later).map fun pair => (pair,candidate pair))).2=target)
  let bad := fun index : Fin earlier.length => fun omega : Seed → Data =>
    decide (candidate (earlier.get index)≠target ∧
      Function.update omega target data (candidate (earlier.get index))=data)
  have cover (omega : Seed → Data) : win omega=true ∨ ∃ index, bad index omega=true := by
    by_cases hit : ∃ index, bad index omega=true
    · exact Or.inr hit
    · left
      apply decide_eq_true
      change (FirstPass.choose (test omega) fallback
        ((earlier++real::later).map fun pair => (pair,candidate pair))).2=target
      simp only [List.map_append, List.map_cons]
      apply FirstPass.good_before (test omega) (fun item : Pair × Seed => item.2=target)
        fallback (real,candidate real) (earlier.map fun pair => (pair,candidate pair))
        (later.map fun pair => (pair,candidate pair)) real_seed
      · simp [test, real_seed]
      · intro item member passes
        obtain ⟨pair,inEarlier,item_eq⟩ : ∃ pair ∈ earlier, (pair,candidate pair)=item := List.mem_map.mp member
        subst item
        by_contra wrong
        obtain ⟨index,atIndex⟩ := List.get_of_mem inEarlier
        apply hit
        refine ⟨index,?_⟩
        change decide (candidate (earlier.get index)≠target ∧
          Function.update omega target data (candidate (earlier.get index))=data)=true
        rw [atIndex]
        exact decide_eq_true ⟨wrong, of_decide_eq_true passes⟩
  have bounds (index : Fin earlier.length) :
      moment (PMF.uniformOfFintype (Seed → Data)) (fun omega => if bad index omega then 1 else 0) ≤
      (Fintype.card Data:ENNReal)⁻¹ := by
    simpa only [bad, decide_eq_true_eq] using harmful_bound target (candidate (earlier.get index)) data
  simpa only [win, test, decide_eq_true_eq] using FirstPass.probability
    (PMF.uniformOfFintype (Seed → Data)) win earlier.length bad
    (Fintype.card Data:ENNReal)⁻¹ cover bounds

/-- Off the real input, pair recovery also pays for a seed-function collision. -/
theorem pair_success {Pair : Type} [DecidableEq Pair] (input : Pair → Input) (real : Pair)
    (target : Seed) (data : Data) (fallback : Pair × Seed) (earlier later : List Pair)
    (off_real : ∀ pair ∈ earlier, input pair ≠ input real) :
    1-(earlier.length:ENNReal)*((Fintype.card Data:ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹) ≤
      moment (independentPair (PMF.uniformOfFintype (Input → Seed))
        (PMF.uniformOfFintype (Seed → Data))) (fun joint =>
        if (FirstPass.choose
          (fun item : Pair × Seed => decide (Function.update joint.2 target data item.2=data)) fallback
          ((earlier++real::later).map fun pair =>
            (pair,Function.update joint.1 (input real) target (input pair)))).1=real then 1 else 0) := by
  classical
  let candidate := fun s : Input → Seed => fun pair : Pair => Function.update s (input real) target (input pair)
  let test := fun omega : Seed → Data => fun item : Pair × Seed =>
    decide (Function.update omega target data item.2=data)
  let win := fun joint : (Input → Seed) × (Seed → Data) => decide ((FirstPass.choose
    (test joint.2) fallback ((earlier++real::later).map fun pair => (pair,candidate joint.1 pair))).1=real)
  let bad := fun index : Fin earlier.length => fun joint : (Input → Seed) × (Seed → Data) =>
    decide (Function.update joint.2 target data (candidate joint.1 (earlier.get index))=data)
  have cover (joint : (Input → Seed) × (Seed → Data)) : win joint=true ∨ ∃ index, bad index joint=true := by
    by_cases hit : ∃ index, bad index joint=true
    · exact Or.inr hit
    · left
      apply decide_eq_true
      change (FirstPass.choose (test joint.2) fallback
        ((earlier++real::later).map fun pair => (pair,candidate joint.1 pair))).1=real
      simp only [List.map_append, List.map_cons]
      apply FirstPass.good_before (test joint.2) (fun item : Pair × Seed => item.1=real)
        fallback (real,candidate joint.1 real) (earlier.map fun pair => (pair,candidate joint.1 pair))
        (later.map fun pair => (pair,candidate joint.1 pair)) rfl
      · simp [test, candidate]
      · intro item member passes
        obtain ⟨pair,inEarlier,item_eq⟩ : ∃ pair ∈ earlier, (pair,candidate joint.1 pair)=item := List.mem_map.mp member
        subst item
        obtain ⟨index,atIndex⟩ := List.get_of_mem inEarlier
        apply False.elim
        apply hit
        refine ⟨index,?_⟩
        change decide (Function.update joint.2 target data (candidate joint.1 (earlier.get index))=data)=true
        rw [atIndex]
        exact passes
  have bounds (index : Fin earlier.length) :
      moment (independentPair (PMF.uniformOfFintype (Input → Seed))
        (PMF.uniformOfFintype (Seed → Data))) (fun joint => if bad index joint then 1 else 0) ≤
      (Fintype.card Data:ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹ := by
    simpa only [independentPair, MomentTools.bind, moment_map, Function.comp_def,
      bad, candidate, decide_eq_true_eq] using off_input_bound (input real) (input (earlier.get index))
        (off_real _ (List.get_mem earlier index)) target data
  simpa only [win, test, candidate, decide_eq_true_eq] using FirstPass.probability
    (independentPair (PMF.uniformOfFintype (Input → Seed)) (PMF.uniformOfFintype (Seed → Data)))
    win earlier.length bad ((Fintype.card Data:ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹) cover bounds

end W7FalseMatch

namespace W7Conditional
attribute [local irreducible] Gamma2Model.execute TranscriptErasure.execute
  Gamma2Model.finalize W7Attack.entropy
open Gamma2Model WalletCryptoCompiler W7Attack
open ProbabilityTools GameExpectation MomentTools
variable {Password Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Passphrase]
  [DecidableEq Seed] [DecidableEq Data] [Fintype Seed] [Fintype Data] [Nonempty Data]

/-- Run the actual program against the planted S/Omega points; its T table can be arbitrary. -/
def output (coordinates : Entropy ≃ State) (crypto : Tables Password Entropy) (container : State)
    (rows : List Password) (pairs : List (Password × Passphrase))
    (fallback : Output Password Passphrase Seed) (real : Password × Passphrase) (target : Seed)
    (s : Entropy × Passphrase → Seed) (t : Seed → Check × Tail) (omega : Seed → Data) (data : Data) :
    Output Password Passphrase Seed :=
  (TranscriptErasure.execute
    (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto
      (SeedWalletModel.answer ⟨Function.update s (entropy coordinates crypto container real.1,real.2) target,
        t,Function.update omega target data⟩))
    (attack coordinates rows pairs fallback data container)).1

/-- The seed lower bound is for the genuine cached oracle program, conditional on arbitrary crypto and S/T tables. -/
theorem seed_tested (coordinates : Entropy ≃ State) (crypto : Tables Password Entropy) (container : State)
    (rows : List Password) (real : Password × Passphrase) (earlier later : List (Password × Passphrase))
    (covered : ∀ pair ∈ earlier++real::later, pair.1 ∈ rows) (fallback : Output Password Passphrase Seed)
    (target : Seed) (s : Entropy × Passphrase → Seed) (t : Seed → Check × Tail) (data : Data) :
    1-(earlier.length:ENNReal)*(Fintype.card Data:ENNReal)⁻¹ ≤
      moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
        if (output coordinates crypto container rows (earlier++real::later) fallback real target s t omega data).2=target
        then 1 else 0) := by
  have pointwise (omega : Seed → Data) := result coordinates rows (earlier++real::later) covered fallback crypto
    (⟨Function.update s (entropy coordinates crypto container real.1,real.2) target,
      t,Function.update omega target data⟩ : Wallet Entropy Passphrase Seed Check Tail Data) data container
  simp only [output, pointwise]
  exact W7FalseMatch.seed_success
    (fun pair => Function.update s (entropy coordinates crypto container real.1,real.2) target
      (entropy coordinates crypto container pair.1,pair.2)) real target
    (Function.update_self _ _ _) data fallback earlier later

/-- Pair recovery has the additional seed-collision term once all preceding S inputs differ from the real one. -/
theorem pair_tested [Nonempty Seed] (coordinates : Entropy ≃ State)
    (crypto : Tables Password Entropy) (container : State)
    (rows : List Password) (real : Password × Passphrase) (earlier later : List (Password × Passphrase))
    (covered : ∀ pair ∈ earlier++real::later, pair.1 ∈ rows) (fallback : Output Password Passphrase Seed)
    (target : Seed) (t : Seed → Check × Tail) (data : Data) [Fintype Entropy] [Fintype Passphrase]
    (off_real : ∀ pair ∈ earlier, (entropy coordinates crypto container pair.1,pair.2)≠
      (entropy coordinates crypto container real.1,real.2)) :
    1-(earlier.length:ENNReal)*((Fintype.card Data:ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹) ≤
      moment (independentPair (PMF.uniformOfFintype (Entropy × Passphrase → Seed))
        (PMF.uniformOfFintype (Seed → Data))) (fun joint =>
        if (output coordinates crypto container rows (earlier++real::later) fallback real target joint.1 t joint.2 data).1=real
        then 1 else 0) := by
  have pointwise (joint : (Entropy × Passphrase → Seed) × (Seed → Data)) := result coordinates rows
    (earlier++real::later) covered fallback crypto
    (⟨Function.update joint.1 (entropy coordinates crypto container real.1,real.2) target,
      t,Function.update joint.2 target data⟩ : Wallet Entropy Passphrase Seed Check Tail Data) data container
  simp only [output, pointwise]
  exact W7FalseMatch.pair_success
    (fun pair : Password × Passphrase => (entropy coordinates crypto container pair.1,pair.2))
    real target data fallback earlier later off_real

end W7Conditional

namespace W7Alias
open Gamma2Model ProbabilityTools GameExpectation MomentTools
variable {Password Entropy : Type} [DecidableEq Password] [DecidableEq Entropy]
  [Fintype Password] [Fintype Entropy]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] Gamma2Model.execute Gamma2Model.finalize

def delta : ENNReal := 1/(2^128:ENNReal)+12/(2^256:ENNReal)

/-- ENT256 has a one-point verifier coordinate, so the existing entropy-collision theorem applies unchanged. -/
def unitCoordinates (coordinates : Entropy ≃ State) : Entropy × Unit ≃ State where
  toFun pair := coordinates pair.1
  invFun state := (coordinates.symm state,())
  left_inv pair := by
    rcases pair with ⟨value,tag⟩
    cases tag
    simp only [Equiv.symm_apply_apply]
  right_inv state := coordinates.apply_symm_apply state

/-- The actual recovered entropy collision has the stated delta_X, including repeated salts. -/
theorem collision (coordinates : Entropy ≃ State) (real focus : Password) (different : real≠focus)
    (container : State) : moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun crypto =>
      if W7Attack.entropy coordinates crypto container focus=
        W7Attack.entropy coordinates crypto container real then 1 else 0) ≤ delta := by
  have estimate := EntropyCollision.probability (unitCoordinates coordinates)
    (fun entropy => (coordinates entropy).1)
    (fun state => by simp only [Theorem3.entropy, unitCoordinates, Equiv.coe_fn_symm_mk, Equiv.apply_symm_apply])
    focus real different container
  simp only [EntropyCollision.event, decide_eq_true_eq] at estimate
  (try simp only [Theorem3.entropy, unitCoordinates, Equiv.coe_fn_symm_mk, W7Attack.entropy, delta] at estimate ⊢)
  exact estimate

/-- Alias losses are charged once per other recovered password row, not per passphrase. -/
theorem union (coordinates : Entropy ≃ State) (real : Password) (others : List Password)
    (different : ∀ focus ∈ others, real≠focus) (container : State) : moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun crypto =>
      if ∃ focus ∈ others, W7Attack.entropy coordinates crypto container focus=
        W7Attack.entropy coordinates crypto container real then 1 else 0) ≤
      (others.length:ENNReal)*delta := by
  classical
  let events := fun index : Fin others.length => fun crypto : Tables Password Entropy =>
    decide (W7Attack.entropy coordinates crypto container (others.get index)=
      W7Attack.entropy coordinates crypto container real)
  have same (crypto : Tables Password Entropy) :
      (∃ focus ∈ others, W7Attack.entropy coordinates crypto container focus=
        W7Attack.entropy coordinates crypto container real) ↔ ∃ index, events index crypto=true := by
    simp [events, List.mem_iff_get]
  simp_rw [same]
  have combined := FiberMembership.union_bound
    (sampleTables (Password := Password) (Entropy := Entropy)) events
  rw [MomentTools.probability] at combined
  simp only [decide_eq_true_eq] at combined
  calc
    _ ≤ ∑ index : Fin others.length,
        ((sampleTables (Password := Password) (Entropy := Entropy)).map (events index)) true :=
      combined
    _ ≤ ∑ _index : Fin others.length, delta := by
      gcongr with index
      rw [MomentTools.probability]
      simpa only [events, decide_eq_true_eq] using collision coordinates real (others.get index)
        (different _ (List.get_mem others index)) container
    _ = _ := by simp

end W7Alias

namespace W7Pair
open Gamma2Model W7Attack W7Conditional
open ProbabilityTools GameExpectation MomentTools
variable {Password Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data]
  [Fintype Password] [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Data]
  [Nonempty Seed] [Nonempty Data]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] Gamma2Model.execute TranscriptErasure.execute W7Attack.entropy

def beta : ENNReal := (Fintype.card Data:ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹

/-- Uniform crypto makes the alias loss global over rows; off it, independent S/Omega give the pair-test loss. -/
theorem raw_bound (coordinates : Entropy ≃ State) (container : State) (rows others : List Password)
    (real : Password × Passphrase) (earlier later : List (Password × Passphrase))
    (absent : real ∉ earlier) (among : ∀ pair ∈ earlier, pair.1=real.1 ∨ pair.1 ∈ others)
    (different : ∀ focus ∈ others, real.1≠focus)
    (covered : ∀ pair ∈ earlier++real::later, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (target : Seed) (t : Seed → Check × Tail)
    (data : Data) : (1-(earlier.length:ENNReal)*beta (Seed := Seed) (Data := Data))-(others.length:ENNReal)*W7Alias.delta ≤
      moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun crypto =>
        moment (independentPair (PMF.uniformOfFintype (Entropy × Passphrase → Seed))
          (PMF.uniformOfFintype (Seed → Data))) (fun joint =>
          if (output coordinates crypto container rows (earlier++real::later) fallback real target joint.1 t joint.2 data).1=real
          then 1 else 0)) := by
  classical
  let aliases := fun crypto : Tables Password Entropy => ∃ focus ∈ others,
    entropy coordinates crypto container focus=entropy coordinates crypto container real.1
  let success := fun crypto : Tables Password Entropy =>
    moment (independentPair (PMF.uniformOfFintype (Entropy × Passphrase → Seed))
      (PMF.uniformOfFintype (Seed → Data))) (fun joint =>
      if (output coordinates crypto container rows (earlier++real::later) fallback real target joint.1 t joint.2 data).1=real
      then 1 else 0)
  let loss := 1-(earlier.length:ENNReal)*beta (Seed := Seed) (Data := Data)
  have pointwise (crypto : Tables Password Entropy) : loss ≤ success crypto+(if aliases crypto then 1 else 0) := by
    by_cases hit : aliases crypto
    · rw [if_pos hit]
      exact (tsub_le_self : loss ≤ (1:ENNReal)).trans (le_add_of_nonneg_left (zero_le))
    · have off : ∀ pair ∈ earlier, (entropy coordinates crypto container pair.1,pair.2)≠
          (entropy coordinates crypto container real.1,real.2) := by
        intro pair member equal
        have entropy_eq := congrArg Prod.fst equal
        have phrase_eq := congrArg Prod.snd equal
        rcases among pair member with same | other
        · exact absent (Prod.ext same phrase_eq ▸ member)
        · exact hit ⟨pair.1,other,entropy_eq⟩
      have pair_estimate := pair_tested coordinates crypto container rows real earlier later covered fallback target t data off
      simpa only [if_neg hit, add_zero, loss, beta, success] using pair_estimate
  have averaged : loss ≤ moment (sampleTables (Password := Password) (Entropy := Entropy)) success+
      (others.length:ENNReal)*W7Alias.delta := by
    calc
      _ = moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun _ => loss) := (constant _ _).symm
      _ ≤ moment sampleTables (fun crypto => success crypto+(if aliases crypto then 1 else 0)) := mono _ _ _ pointwise
      _ = moment sampleTables success+moment sampleTables (fun crypto => if aliases crypto then 1 else 0) := MomentTools.add _ _ _
      _ ≤ _ := add_le_add le_rfl (W7Alias.union coordinates real.1 others different container)
  exact tsub_le_iff_right.mpr averaged

/-- For distinct recovered rows, deleting the true password leaves exactly m-1 possible aliases. -/
theorem rows_bound (coordinates : Entropy ≃ State) (container : State) (rows : List Password)
    (unique : rows.Nodup) (real : Password × Passphrase)
    (earlier later : List (Password × Passphrase)) (absent : real ∉ earlier)
    (covered : ∀ pair ∈ earlier++real::later, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (target : Seed) (t : Seed → Check × Tail)
    (data : Data) : (1-(earlier.length:ENNReal)*beta (Seed := Seed) (Data := Data))-
      ((rows.length-1:Nat):ENNReal)*W7Alias.delta ≤
      moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun crypto =>
        moment (independentPair (PMF.uniformOfFintype (Entropy × Passphrase → Seed))
          (PMF.uniformOfFintype (Seed → Data))) (fun joint =>
          if (output coordinates crypto container rows (earlier++real::later) fallback real target joint.1 t joint.2 data).1=real
          then 1 else 0)) := by
  have real_mem : real.1 ∈ rows := covered real (by simp)
  have among : ∀ pair ∈ earlier, pair.1=real.1 ∨ pair.1 ∈ rows.erase real.1 := by
    intro pair member
    by_cases same : pair.1=real.1
    · exact Or.inl same
    · exact Or.inr ((List.mem_erase_of_ne same).mpr (covered pair (List.mem_append_left _ member)))
  have different : ∀ focus ∈ rows.erase real.1, real.1≠focus := by
    intro focus member equal
    exact unique.not_mem_erase (equal.symm ▸ member)
  have estimate := raw_bound coordinates container rows (rows.erase real.1) real earlier later absent among different covered
    fallback target t data
  simpa only [List.length_erase_of_mem real_mem] using estimate

variable [Nonempty Entropy] [Fintype Check] [Fintype Tail] [Nonempty Check] [Nonempty Tail]
attribute [local irreducible] FullSourceCoordinates.cipher

end W7Pair

namespace W7OtherTests
attribute [local irreducible] Gamma2Model.execute TranscriptErasure.execute
  Gamma2Model.finalize W7Attack.entropy
open Gamma2Model W7Attack WalletCryptoCompiler
open ProbabilityTools GameExpectation MomentTools
variable {Password Entropy Passphrase Seed Check Tail Data : Type}

/-- A T-only probe reads the full check hash but uses only the check prefix. -/
def checkProbe [DecidableEq Check] (target : Check) (seed : Seed) :
    OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool := do
  let value : Check × Tail ← TranscriptErasure.ask
    (spec := FullSpec Password Entropy Passphrase Seed Check Tail Data) (.inr (.t seed))
  pure (decide (value.1=target))

/-- Omega is queried only after the check passes. -/
def bothProbe [DecidableEq Check] [DecidableEq Data] (target : Check) (data : Data) (seed : Seed) :
    OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool := do
  let passes ← checkProbe target seed
  if passes then
    let found : Data ← TranscriptErasure.ask
      (spec := FullSpec Password Entropy Passphrase Seed Check Tail Data) (.inr (.omega seed))
    pure (decide (found=data))
  else pure false

/-- Both probe result and exact query order are preserved; no Omega query is made on a failed check. -/
theorem both_execution [DecidableEq Check] [DecidableEq Data]
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (target : Check) (data : Data) (seed : Seed) :
    TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (bothProbe target data seed) =
      (decide ((wallet.t seed).1=target ∧ wallet.omega seed=data),
        if (wallet.t seed).1=target then [Sum.inr (.t seed),Sum.inr (.omega seed)] else [Sum.inr (.t seed)]) := by
  by_cases passes : (wallet.t seed).1=target
  all_goals
    simp [bothProbe, checkProbe, TranscriptErasure.execute_bind, WalletPairPort.transcript_map, TranscriptErasure.execute_ask,
      TranscriptErasure.execute_pure, combinedAnswer, SeedWalletModel.answer, passes]

/-- The three predicates in the source proposition. -/
inductive Mode
  | wallet
  | check
  | both
  deriving DecidableEq

/-- Effective verifier values make the same first-match argument cover all predicates.
(Port to Lean 4.35: implicit arguments are checked at `.implicit` transparency, so this answer
type must unfold there, as it did before.) -/
@[implicit_reducible]
def Mode.Value (mode : Mode) (Check Data : Type) : Type :=
  match mode with | .wallet => Data | .check => Check | .both => Check × Data

def Mode.values (mode : Mode) (t : Seed → Check × Tail) (omega : Seed → Data) :
    Seed → mode.Value Check Data :=
  match mode with
  | .wallet => omega
  | .check => fun seed => (t seed).1
  | .both => fun seed => ((t seed).1,omega seed)

def Mode.targetValue (mode : Mode) (target : Check) (data : Data) : mode.Value Check Data :=
  match mode with | .wallet => data | .check => target | .both => (target,data)

instance Mode.valueFintype (mode : Mode) [Fintype Check] [Fintype Data] : Fintype (mode.Value Check Data) := by
  cases mode <;> dsimp [Mode.Value] <;> infer_instance
instance Mode.valueNonempty (mode : Mode) [Nonempty Check] [Nonempty Data] : Nonempty (mode.Value Check Data) := by
  cases mode <;> dsimp [Mode.Value] <;> infer_instance
instance Mode.valueDecidableEq (mode : Mode) [DecidableEq Check] [DecidableEq Data] : DecidableEq (mode.Value Check Data) := by
  cases mode <;> dsimp [Mode.Value] <;> infer_instance

def Mode.probe [DecidableEq Check] [DecidableEq Data] (mode : Mode) (target : Check) (data : Data)
    (seed : Seed) : OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) Bool :=
  match mode with
  | .wallet => walletProbe data seed
  | .check => checkProbe target seed
  | .both => bothProbe target data seed

def Mode.passes [DecidableEq Check] [DecidableEq Data] (mode : Mode)
    (wallet : Wallet Entropy Passphrase Seed Check Tail Data) (target : Check) (data : Data)
    (seed : Seed) : Bool :=
  match mode with
  | .wallet => decide (wallet.omega seed=data)
  | .check => decide ((wallet.t seed).1=target)
  | .both => decide ((wallet.t seed).1=target ∧ wallet.omega seed=data)

def Mode.trace [DecidableEq Check] (mode : Mode)
    (wallet : Wallet Entropy Passphrase Seed Check Tail Data) (target : Check) (seed : Seed) :
    List (Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed) :=
  match mode with
  | .wallet => [.inr (.omega seed)]
  | .check => [.inr (.t seed)]
  | .both => if (wallet.t seed).1=target then [.inr (.t seed),.inr (.omega seed)] else [.inr (.t seed)]

/-- Each mode's actual result and complete transcript agree with its mathematical predicate. -/
theorem Mode.execution [DecidableEq Check] [DecidableEq Data] (mode : Mode)
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (target : Check) (data : Data) (seed : Seed) :
    TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (mode.probe target data seed) = (mode.passes wallet target data seed,mode.trace wallet target seed) := by
  cases mode with
  | wallet => simp [Mode.probe, Mode.passes, Mode.trace, walletProbe, TranscriptErasure.execute_bind, WalletPairPort.transcript_map,
      TranscriptErasure.execute_ask, TranscriptErasure.execute_pure, combinedAnswer, SeedWalletModel.answer]
  | check => simp [Mode.probe, Mode.passes, Mode.trace, checkProbe, TranscriptErasure.execute_bind, WalletPairPort.transcript_map,
      TranscriptErasure.execute_ask, TranscriptErasure.execute_pure, combinedAnswer, SeedWalletModel.answer]
  | both => exact both_execution crypto wallet target data seed

/-- A failed check can only save an Omega query; it never increases any query counter. -/
theorem Mode.count [DecidableEq Check] [DecidableEq Data] (mode : Mode)
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (target : Check) (data : Data) (seed : Seed)
    (tag : Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed → Bool) :
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (mode.probe target data seed)).2.countP tag ≤
      (if mode=.wallet then 0 else if tag (.inr (.t seed)) then 1 else 0)+
      (if mode=.check then 0 else if tag (.inr (.omega seed)) then 1 else 0) := by
  rw [Mode.execution]
  cases mode with
  | wallet => simp [Mode.trace]
  | check => simp [Mode.trace]
  | both =>
    by_cases passes : (wallet.t seed).1=target
    · simp [Mode.trace, passes, List.countP_cons, Nat.add_comm]
    · simp [Mode.trace, passes]

def Mode.tCost : Mode → Nat | .wallet => 0 | _ => 1
def Mode.omegaCost : Mode → Nat | .check => 0 | _ => 1

/-- All modes execute the same cached recovery and pair loop. -/
def Mode.attack [DecidableEq Password] [DecidableEq Check] [DecidableEq Data] (mode : Mode)
    (coordinates : Entropy ≃ State) (rows : List Password) (pairs : List (Password × Passphrase))
    (fallback : Output Password Passphrase Seed) (target : Check) (data : Data) (container : State) :
    OracleComp (FullSpec Password Entropy Passphrase Seed Check Tail Data) (Output Password Passphrase Seed) :=
  attackUsing coordinates rows pairs fallback (mode.probe target data) container

/-- Every mode evaluates the same candidate list with its own predicate. -/
theorem Mode.result [DecidableEq Password] [DecidableEq Check] [DecidableEq Data] (mode : Mode)
    (coordinates : Entropy ≃ State) (rows : List Password) (pairs : List (Password × Passphrase))
    (covered : ∀ pair ∈ pairs, pair.1 ∈ rows) (fallback : Output Password Passphrase Seed)
    (target : Check) (data : Data) (container : State) (crypto : Tables Password Entropy)
    (wallet : Wallet Entropy Passphrase Seed Check Tail Data) :
    (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (mode.attack coordinates rows pairs fallback target data container)).1 =
      FirstPass.choose (fun item : Output Password Passphrase Seed => mode.passes wallet target data item.2)
        fallback (pairs.map fun pair => (pair,wallet.s (entropy coordinates crypto container pair.1,pair.2))) := by
  simpa only [Mode.attack, Mode.execution, entropy] using
    attackUsing_result coordinates rows pairs covered fallback (mode.probe target data) crypto wallet container

/-- Hard budgets include every actual query, with mode-specific T/Omega caps. -/
theorem Mode.counts [DecidableEq Password] [DecidableEq Check] [DecidableEq Data] (mode : Mode)
    (coordinates : Entropy ≃ State) (container : State) (target : Check) (data : Data)
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (rows : List Password) (pairs : List (Password × Passphrase)) (fallback : Output Password Passphrase Seed) :
    let queries := (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (mode.attack coordinates rows pairs fallback target data container)).2
    queries.countP (G10WalletCounts.crypto QueryCounts.isA) ≤ 12*rows.length ∧
      queries.countP (G10WalletCounts.crypto QueryCounts.isB) ≤ 11*rows.length+1 ∧
      queries.countP (G10WalletCounts.crypto QueryCounts.isH) ≤ 12*rows.length ∧
      (SeedWalletModel.seedPairs queries).length ≤ pairs.length ∧
      queries.countP SeedWalletModel.isT ≤ pairs.length*mode.tCost ∧
      queries.countP SeedWalletModel.isOmega ≤ pairs.length*mode.omegaCost := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have estimate := attackUsing_count coordinates container (mode.probe target data) crypto wallet rows pairs fallback
      (G10WalletCounts.crypto QueryCounts.isA) 12 0
      (fun password => by simpa only [List.countP_map, G10WalletCounts.crypto, Function.comp_def] using
        (SharedInverse.counts password crypto container (crypto.b (11,container.1))).1)
      (fun _ _ seed => by
        have bound := Mode.count mode crypto wallet target data seed (G10WalletCounts.crypto QueryCounts.isA)
        simpa [G10WalletCounts.crypto] using bound)
    simpa [Mode.attack, G10WalletCounts.crypto, QueryCounts.isA, Nat.mul_comm] using estimate
  · have estimate := attackUsing_count coordinates container (mode.probe target data) crypto wallet rows pairs fallback
      (G10WalletCounts.crypto QueryCounts.isB) 11 0
      (fun password => by simpa only [List.countP_map, G10WalletCounts.crypto, Function.comp_def] using
        (SharedInverse.counts password crypto container (crypto.b (11,container.1))).2.1)
      (fun _ _ seed => by
        have bound := Mode.count mode crypto wallet target data seed (G10WalletCounts.crypto QueryCounts.isB)
        simpa [G10WalletCounts.crypto] using bound)
    simpa [Mode.attack, G10WalletCounts.crypto, QueryCounts.isB, Nat.mul_comm] using estimate
  · have estimate := attackUsing_count coordinates container (mode.probe target data) crypto wallet rows pairs fallback
      (G10WalletCounts.crypto QueryCounts.isH) 12 0
      (fun password => by simpa only [List.countP_map, G10WalletCounts.crypto, Function.comp_def] using
        (SharedInverse.counts password crypto container (crypto.b (11,container.1))).2.2.1)
      (fun _ _ seed => by
        have bound := Mode.count mode crypto wallet target data seed (G10WalletCounts.crypto QueryCounts.isH)
        simpa [G10WalletCounts.crypto] using bound)
    simpa [Mode.attack, G10WalletCounts.crypto, QueryCounts.isH, Nat.mul_comm] using estimate
  · have estimate := attackUsing_count coordinates container (mode.probe target data) crypto wallet rows pairs fallback isS 0 1
      (by intro password; simp [List.countP_map, isS, SeedQueryMetadata.extract])
      (fun e q seed => by
        have bound := mode.count crypto wallet target data seed (isS (Password := Password) (Entropy := Entropy) (Passphrase := Passphrase))
        have zero : (TranscriptErasure.execute
            (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
            (mode.probe target data seed)).2.countP isS ≤ 0 := by
          simpa [isS, SeedQueryMetadata.extract, SeedWalletModel.seedPair] using bound
        simpa [isS, SeedQueryMetadata.extract, SeedWalletModel.seedPair] using Nat.add_le_add_left zero 1)
    rw [SeedWalletModel.seedPairs, QueryCollector.count]
    (try simp [Mode.attack, isS, SeedQueryMetadata.extract] at estimate ⊢)
    exact estimate
  · have estimate := attackUsing_count coordinates container (mode.probe target data) crypto wallet rows pairs fallback
      SeedWalletModel.isT 0 mode.tCost
      (by intro password; simp [List.countP_map, SeedWalletModel.isT])
      (fun _ _ seed => by
        have bound := mode.count crypto wallet target data seed SeedWalletModel.isT
        cases mode <;> simpa [Mode.tCost, SeedWalletModel.isT] using bound)
    simpa [Mode.attack, SeedWalletModel.isT] using estimate
  · have estimate := attackUsing_count coordinates container (mode.probe target data) crypto wallet rows pairs fallback
      SeedWalletModel.isOmega 0 mode.omegaCost
      (by intro password; simp [List.countP_map, SeedWalletModel.isOmega])
      (fun _ _ seed => by
        have bound := mode.count crypto wallet target data seed SeedWalletModel.isOmega
        cases mode <;> simpa [Mode.omegaCost, SeedWalletModel.isOmega] using bound)
    simpa [Mode.attack, SeedWalletModel.isOmega] using estimate

/-- This counts every actual T query whose prefix passes, including a pass followed by an Omega failure. -/
def passedT [DecidableEq Check] (wallet : Wallet Entropy Passphrase Seed Check Tail Data) (target : Check) :
    Point Password Entropy ⊕ SeedWalletModel.Point Entropy Passphrase Seed → Bool
  | .inr (.t seed) => decide ((wallet.t seed).1=target)
  | _ => false

/-- The check-then-data attack makes exactly one Omega query per actual passing T query. -/
theorem both_omega_count [DecidableEq Password] [DecidableEq Check] [DecidableEq Data]
    (coordinates : Entropy ≃ State) (container : State) (target : Check) (data : Data)
    (crypto : Tables Password Entropy) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (rows : List Password) (pairs : List (Password × Passphrase)) (fallback : Output Password Passphrase Seed) :
    let queries := (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet))
      (Mode.both.attack coordinates rows pairs fallback target data container)).2
    queries.countP SeedWalletModel.isOmega=queries.countP (passedT wallet target) := by
  let answer := combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer wallet)
  let cached := TranscriptErasure.execute answer (recoverRows coordinates container (crypto.b (11,container.1)) rows)
  have omega_zero : cached.2.countP SeedWalletModel.isOmega=0 := by
    have count := recover_count coordinates container crypto wallet rows SeedWalletModel.isOmega 0
      (by intro password; simp [List.countP_map, SeedWalletModel.isOmega])
    simpa only [Nat.mul_zero] using count
  have pass_zero : cached.2.countP (passedT wallet target)=0 := by
    have count := recover_count coordinates container crypto wallet rows (passedT wallet target) 0
      (by intro password; simp [List.countP_map, passedT])
    simpa only [Nat.mul_zero] using count
  have search := runUsing_balance cached.1 (bothProbe target data) fallback crypto wallet pairs
    SeedWalletModel.isOmega (passedT wallet target)
    (by intros; rfl) (fun seed => by
      rw [both_execution]
      by_cases passes : (wallet.t seed).1=target
      all_goals simp [passes, SeedWalletModel.isOmega, passedT])
  simp only [Mode.attack, attackUsing, TranscriptErasure.execute_bind,
    TranscriptErasure.execute_ask, combinedAnswer,
    List.singleton_append, List.countP_cons, List.countP_append, passedT, SeedWalletModel.isOmega,
    Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  change cached.2.countP SeedWalletModel.isOmega+_ = cached.2.countP (passedT wallet target)+_
  rw [omega_zero, pass_zero]
  exact congrArg (fun value : Nat => 0+value) search

variable [Fintype Seed] [Nonempty Seed] [DecidableEq Seed]
  [Fintype Check] [Nonempty Check] [DecidableEq Check]
  [Fintype Tail] [Nonempty Tail] [Fintype Data] [Nonempty Data] [DecidableEq Data]

omit [Fintype Data] [Nonempty Data] [DecidableEq Data] in
/-- A non-target seed passes the programmed check with probability exactly1/cardCheck. -/
theorem check_exact (real candidate : Seed) (target : Check) :
    moment (PMF.uniformOfFintype (Seed → Check × Tail)) (fun t =>
      if (Function.update t real (target,(t real).2) candidate).1=target then 1 else 0) =
      if candidate=real then 1 else (Fintype.card Check:ENNReal)⁻¹ := by
  by_cases same : candidate=real
  · subst candidate
    simp only [Function.update_self, ite_true, constant]
  · have law := VerifierProbability.probability (Equiv.refl (Check × Tail)) candidate target
    simp only [decide_eq_true_eq] at law
    (try simp only [Function.update_of_ne same, if_neg same, Equiv.refl_apply, div_eq_mul_inv, one_mul] at law ⊢)
    exact law

/-- T and Omega are independent ideal functions; their non-target pass rates multiply. -/
theorem both_exact (real candidate : Seed) (target : Check) (data : Data) :
    moment (PMF.uniformOfFintype (Seed → Check × Tail)) (fun t =>
      moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
        if (Function.update t real (target,(t real).2) candidate).1=target ∧
          Function.update omega real data candidate=data then 1 else 0)) =
      if candidate=real then 1 else (Fintype.card Check:ENNReal)⁻¹*(Fintype.card Data:ENNReal)⁻¹ := by
  by_cases same : candidate=real
  · subst candidate
    simp only [Function.update_self, true_and, ite_true, constant]
  · have fixed (t : Seed → Check × Tail) :
        moment (PMF.uniformOfFintype (Seed → Data)) (fun omega =>
          if (Function.update t real (target,(t real).2) candidate).1=target ∧
            Function.update omega real data candidate=data then 1 else 0) =
        (if (Function.update t real (target,(t real).2) candidate).1=target then 1 else 0)*
          (Fintype.card Data:ENNReal)⁻¹ := by
      by_cases passes : (Function.update t real (target,(t real).2) candidate).1=target
      · simp only [passes, true_and, if_true, one_mul]
        simpa only [if_neg same] using W7FalseMatch.exact_match real candidate data
      · simp only [passes, false_and, if_false, constant, zero_mul]
    simp only [fixed]
    rw [mul_const, check_exact, if_neg same]
    simp only [if_neg same]

omit [Nonempty Seed] [DecidableEq Check] [Fintype Data] [Nonempty Data] [DecidableEq Data] in
/-- Projecting a uniform check-and-suffix function gives a uniform complete check-prefix function. -/
theorem prefix_uniform :
    (PMF.uniformOfFintype (Seed → Check × Tail)).map (fun t => fun seed => (t seed).1) =
      PMF.uniformOfFintype (Seed → Check) := by
  let split := Equiv.arrowProdEquivProdArrow Seed (fun _ => Check) (fun _ => Tail)
  have moved := PMF.uniformOfFintype_map_of_bijective split split.bijective
  calc
    _ = ((PMF.uniformOfFintype (Seed → Check × Tail)).map split).map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [moved, uniform_fst]

omit [Nonempty Seed] [DecidableEq Check] [DecidableEq Data] in
/-- The entire effective verifier table is uniform, not only each individual answer. -/
theorem Mode.joint_uniform (mode : Mode) :
    (independentPair (PMF.uniformOfFintype (Seed → Check × Tail))
      (PMF.uniformOfFintype (Seed → Data))).map (fun fields => mode.values fields.1 fields.2) =
      PMF.uniformOfFintype (Seed → mode.Value Check Data) := by
  cases mode with
  | wallet =>
    simp [Mode.values, independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact PMF.map_id _
  | check =>
    calc
      _ = ((independentPair (PMF.uniformOfFintype (Seed → Check × Tail))
          (PMF.uniformOfFintype (Seed → Data))).map Prod.fst).map (fun t => fun seed => (t seed).1) := by
        rw [PMF.map_comp]
        rfl
      _ = (PMF.uniformOfFintype (Seed → Check × Tail)).map (fun t => fun seed => (t seed).1) := by
        rw [← uniform_product, uniform_fst]
      _ = _ := prefix_uniform
  | both =>
    let join := (Equiv.arrowProdEquivProdArrow Seed (fun _ => Check) (fun _ => Data)).symm
    calc
      _ = (independentPair
          ((PMF.uniformOfFintype (Seed → Check × Tail)).map (fun t => fun seed => (t seed).1))
          (PMF.uniformOfFintype (Seed → Data))).map join := by
        simp only [independentPair, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
        rfl
      _ = (independentPair (PMF.uniformOfFintype (Seed → Check))
          (PMF.uniformOfFintype (Seed → Data))).map join := by rw [prefix_uniform]
      _ = (PMF.uniformOfFintype ((Seed → Check) × (Seed → Data))).map join := by rw [← uniform_product]
      _ = _ := PMF.uniformOfFintype_map_of_bijective join join.bijective

omit [Fintype Seed] [Nonempty Seed] [Fintype Check] [Nonempty Check] [Fintype Tail] [Nonempty Tail]
  [Fintype Data] [Nonempty Data] [DecidableEq Check] [DecidableEq Data] in
/-- Programming T/Omega at the true seed programs exactly one effective verifier value. -/
theorem Mode.program_values (mode : Mode) (t : Seed → Check × Tail) (omega : Seed → Data)
    (real : Seed) (target : Check) (data : Data) :
    mode.values (Function.update t real (target,(t real).2)) (Function.update omega real data) =
      Function.update (mode.values t omega) real (mode.targetValue target data) := by
  funext seed
  by_cases same : seed=real
  · subst seed
    cases mode <;> simp [Mode.values, Mode.targetValue]
  · cases mode <;> simp [Mode.values, Mode.targetValue, Function.update_of_ne same]

omit [Nonempty Seed] [DecidableEq Check] [DecidableEq Data] in
/-- The planted table law is the same single-point programming used by the proved wallet-only search. -/
theorem Mode.programmed_uniform (mode : Mode) (real : Seed) (target : Check) (data : Data) :
    (independentPair (PMF.uniformOfFintype (Seed → Check × Tail))
      (PMF.uniformOfFintype (Seed → Data))).map (fun fields =>
        mode.values (Function.update fields.1 real (target,(fields.1 real).2)) (Function.update fields.2 real data)) =
    (PMF.uniformOfFintype (Seed → mode.Value Check Data)).map
      (fun verifier => Function.update verifier real (mode.targetValue target data)) := by
  simp_rw [Mode.program_values]
  calc
    _ = ((independentPair (PMF.uniformOfFintype (Seed → Check × Tail))
        (PMF.uniformOfFintype (Seed → Data))).map (fun fields => mode.values fields.1 fields.2)).map
        (fun verifier => Function.update verifier real (mode.targetValue target data)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [Mode.joint_uniform]

omit [Fintype Seed] [Nonempty Seed] [Fintype Check] [Nonempty Check] [Fintype Tail] [Nonempty Tail]
  [Fintype Data] [Nonempty Data] [DecidableEq Seed] in
/-- Every actual mode uses equality with its effective verifier value. -/
theorem Mode.passes_values (mode : Mode) (wallet : Wallet Entropy Passphrase Seed Check Tail Data)
    (target : Check) (data : Data) (seed : Seed) :
    mode.passes wallet target data seed=decide (mode.values wallet.t wallet.omega seed=mode.targetValue target data) := by
  cases mode with
  | wallet => rfl
  | check => rfl
  | both =>
    apply Bool.eq_iff_iff.mpr
    simp only [Mode.passes, decide_eq_true_eq]
    simp only [Mode.values, Mode.targetValue]
    constructor
    · rintro ⟨left,right⟩
      exact Prod.ext left right
    · intro equal
      exact ⟨congrArg Prod.fst equal,congrArg Prod.snd equal⟩

variable [DecidableEq Password] [DecidableEq Entropy] [DecidableEq Passphrase]

/-- Actual mode output in the planted experiment; only the oracle tables contain hidden inputs. -/
def Mode.output (mode : Mode) (coordinates : Entropy ≃ State) (crypto : Tables Password Entropy)
    (container : State) (rows : List Password) (pairs : List (Password × Passphrase))
    (fallback : Output Password Passphrase Seed) (real : Password × Passphrase) (seed : Seed)
    (s : Entropy × Passphrase → Seed) (t : Seed → Check × Tail) (omega : Seed → Data)
    (target : Check) (data : Data) : Output Password Passphrase Seed :=
  (TranscriptErasure.execute
    (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer
      ⟨Function.update s (entropy coordinates crypto container real.1,real.2) seed,
        Function.update t seed (target,(t seed).2),Function.update omega seed data⟩))
    (mode.attack coordinates rows pairs fallback target data container)).1

omit [Fintype Seed] [Nonempty Seed] [Fintype Check] [Nonempty Check] [Fintype Tail] [Nonempty Tail]
  [Fintype Data] [Nonempty Data] in
/-- Equality of results separates actual T/Omega query costs from the effective verifier used in probability counting. -/
theorem Mode.output_emulates (mode : Mode) (coordinates : Entropy ≃ State)
    (crypto : Tables Password Entropy) (container : State) (rows : List Password)
    (pairs : List (Password × Passphrase)) (covered : ∀ pair ∈ pairs, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (real : Password × Passphrase) (seed : Seed)
    (s : Entropy × Passphrase → Seed) (t : Seed → Check × Tail) (omega : Seed → Data)
    (target : Check) (data : Data) :
    mode.output coordinates crypto container rows pairs fallback real seed s t omega target data =
      W7Conditional.output (Check := Unit) (Tail := Unit) (Data := mode.Value Check Data)
        coordinates crypto container rows pairs fallback real seed s (fun _ => ((),()))
        (mode.values t omega) (mode.targetValue target data) := by
  let actual : Wallet Entropy Passphrase Seed Check Tail Data :=
    ⟨Function.update s (entropy coordinates crypto container real.1,real.2) seed,
      Function.update t seed (target,(t seed).2),Function.update omega seed data⟩
  let virtual : Wallet Entropy Passphrase Seed Unit Unit (mode.Value Check Data) :=
    ⟨actual.s,fun _ => ((),()),Function.update (mode.values t omega) seed (mode.targetValue target data)⟩
  have actual_result := mode.result coordinates rows pairs covered fallback target data container crypto actual
  have virtual_result := W7Attack.result coordinates rows pairs covered fallback crypto virtual
    (mode.targetValue target data) container
  change (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Check Tail Data) crypto (SeedWalletModel.answer actual))
      (mode.attack coordinates rows pairs fallback target data container)).1 = _
  rw [actual_result]
  change _ = (TranscriptErasure.execute
      (combinedAnswer (WalletSpec Entropy Passphrase Seed Unit Unit (mode.Value Check Data)) crypto (SeedWalletModel.answer virtual))
      (W7Attack.attack coordinates rows pairs fallback (mode.targetValue target data) container)).1
  rw [virtual_result]
  congr 1
  funext item
  rw [Mode.passes_values]
  simp only [actual, virtual, Mode.program_values]

omit [Nonempty Seed] in
/-- The whole output law matches the already proved ideal-verifier search. -/
theorem Mode.output_law (mode : Mode) (coordinates : Entropy ≃ State)
    (crypto : Tables Password Entropy) (container : State) (rows : List Password)
    (pairs : List (Password × Passphrase)) (covered : ∀ pair ∈ pairs, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (real : Password × Passphrase) (seed : Seed)
    (s : Entropy × Passphrase → Seed) (target : Check) (data : Data) :
    (independentPair (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype (Seed → Data))).map
      (fun fields => mode.output coordinates crypto container rows pairs fallback real seed s fields.1 fields.2 target data) =
    (PMF.uniformOfFintype (Seed → mode.Value Check Data)).map (fun verifier =>
      W7Conditional.output (Check := Unit) (Tail := Unit) (Data := mode.Value Check Data)
        coordinates crypto container rows pairs fallback real seed s (fun _ => ((),())) verifier (mode.targetValue target data)) := by
  simp_rw [Mode.output_emulates mode coordinates crypto container rows pairs covered]
  calc
    _ = ((independentPair (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype (Seed → Data))).map
        (fun fields => mode.values fields.1 fields.2)).map (fun verifier =>
          W7Conditional.output (Check := Unit) (Tail := Unit) (Data := mode.Value Check Data)
            coordinates crypto container rows pairs fallback real seed s (fun _ => ((),())) verifier (mode.targetValue target data)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [Mode.joint_uniform]

omit [Nonempty Seed] in
/-- Scalar observations use the same exact law without unfolding the internal oracle computation. -/
theorem Mode.expectation (mode : Mode) (coordinates : Entropy ≃ State)
    (crypto : Tables Password Entropy) (container : State) (rows : List Password)
    (pairs : List (Password × Passphrase)) (covered : ∀ pair ∈ pairs, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (real : Password × Passphrase) (seed : Seed)
    (s : Entropy × Passphrase → Seed) (target : Check) (data : Data)
    (value : Output Password Passphrase Seed → ENNReal) :
    moment (independentPair (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype (Seed → Data)))
      (fun fields => value (mode.output coordinates crypto container rows pairs fallback real seed s fields.1 fields.2 target data)) =
    moment (PMF.uniformOfFintype (Seed → mode.Value Check Data)) (fun verifier => value
      (W7Conditional.output (Check := Unit) (Tail := Unit) (Data := mode.Value Check Data)
        coordinates crypto container rows pairs fallback real seed s (fun _ => ((),())) verifier (mode.targetValue target data))) := by
  have law := congrArg (fun distribution => moment distribution value)
    (Mode.output_law (Tail := Tail) mode coordinates crypto container rows pairs covered fallback real seed s target data)
  simpa only [moment_map, Function.comp_def] using law

omit [Nonempty Seed] in
/-- All three actual modes have the same seed bound with their own effective verifier width. -/
theorem Mode.seed_tested (mode : Mode) (coordinates : Entropy ≃ State) (crypto : Tables Password Entropy)
    (container : State) (rows : List Password) (real : Password × Passphrase)
    (earlier later : List (Password × Passphrase)) (covered : ∀ pair ∈ earlier++real::later, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (seed : Seed) (s : Entropy × Passphrase → Seed)
    (target : Check) (data : Data) :
    1-(earlier.length:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹ ≤
    moment (independentPair (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype (Seed → Data)))
      (fun fields => if (mode.output coordinates crypto container rows (earlier++real::later) fallback real seed s
        fields.1 fields.2 target data).2=seed then 1 else 0) := by
  rw [Mode.expectation (Tail := Tail) mode coordinates crypto container rows (earlier++real::later) covered
    fallback real seed s target data (fun result => if result.2=seed then 1 else 0)]
  exact W7Conditional.seed_tested (Check := Unit) (Tail := Unit) (Data := mode.Value Check Data)
    coordinates crypto container rows real earlier later covered fallback seed s (fun _ => ((),())) (mode.targetValue target data)

variable [Fintype Password] [Fintype Entropy] [Fintype Passphrase]

/-- The full pair bound transfers unchanged, including the single m-1 entropy-alias charge. -/
theorem Mode.pair_raw (mode : Mode) (coordinates : Entropy ≃ State) (container : State)
    (rows : List Password) (unique : rows.Nodup) (real : Password × Passphrase)
    (earlier later : List (Password × Passphrase)) (absent : real ∉ earlier)
    (covered : ∀ pair ∈ earlier++real::later, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (seed : Seed) (target : Check) (data : Data) :
    (1-(earlier.length:ENNReal)*((Fintype.card (mode.Value Check Data):ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹))-
      ((rows.length-1:Nat):ENNReal)*W7Alias.delta ≤
    moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun crypto =>
      moment (PMF.uniformOfFintype (Entropy × Passphrase → Seed)) (fun s =>
        moment (independentPair (PMF.uniformOfFintype (Seed → Check × Tail)) (PMF.uniformOfFintype (Seed → Data)))
          (fun fields => if (mode.output coordinates crypto container rows (earlier++real::later) fallback real seed s
            fields.1 fields.2 target data).1=real then 1 else 0))) := by
  simp_rw [Mode.expectation (Tail := Tail) mode coordinates _ container rows (earlier++real::later) covered
    fallback real seed _ target data (fun result => if result.1=real then 1 else 0)]
  have estimate := W7Pair.rows_bound (Check := Unit) (Tail := Unit) (Data := mode.Value Check Data)
    coordinates container rows unique real earlier later absent covered fallback seed (fun _ => ((),())) (mode.targetValue target data)
  simpa only [W7Pair.beta, independentPair, MomentTools.bind, moment_map, Function.comp_def] using estimate

variable [Nonempty Entropy]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] FullSourceCoordinates.cipher

omit [Fintype Password] in
/-- The effective verifier argument retains the actual T-programmed source experiment. -/
theorem Mode.seed_planted (mode : Mode) (coordinates : Entropy ≃ State)
    (crypto : Tables Password Entropy) (rows : List Password) (real : Password × Passphrase)
    (earlier later : List (Password × Passphrase))
    (covered : ∀ pair ∈ earlier++real::later, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (target : Check) :
    1-(earlier.length:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹ ≤
      (FullPlantedResampling.original (Tail := Tail) (Data := Data) coordinates real.1 crypto real.2 target
        (mode.attack coordinates rows (earlier++real::later) fallback target)
        (fun seed result => decide (result.2=seed))) true := by
  let loss : ENNReal := 1-(earlier.length:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹
  have integrate {Value : Type} (law : PMF Value) (value : Value → ENNReal)
      (lower : ∀ item, loss ≤ value item) : loss ≤ moment law value :=
    (constant law loss).symm.le.trans (mono law _ _ lower)
  rw [FullPlantedResampling.resampling]
  unfold FullPlantedResampling.programmed
  rw [MomentTools.probability]
  simp only [W3.programmed, W3.payload, W3.tagProgrammed,
    W3.omegaProgrammed, MomentTools.bind, moment_map, Function.comp_def]
  apply integrate
  intro s
  apply integrate
  intro container
  apply integrate
  intro seed
  rw [G8Transport.comm]
  apply integrate
  intro data
  have source_cache : (FullSourceCoordinates.cipher coordinates real.1 crypto).symm container=
      entropy coordinates crypto (coordinates container) real.1 := by
    unfold entropy
    exact FullSourceCoordinates.inverse coordinates real.1 crypto container
  have estimate := Mode.seed_tested (Tail := Tail) mode coordinates crypto (coordinates container) rows real earlier later
    covered fallback seed s target data
  (try simp only [independentPair, MomentTools.bind, moment_map, Function.comp_def, FullPlantedResampling.score, source_cache, decide_eq_true_eq, Mode.output] at estimate ⊢)
  exact estimate

/-- T and Omega stay inside the alias-counting experiment; only independent Y/seed/data draws move outside it. -/
theorem Mode.pair_planted (mode : Mode) (coordinates : Entropy ≃ State) (rows : List Password)
    (unique : rows.Nodup) (real : Password × Passphrase)
    (earlier later : List (Password × Passphrase)) (absent : real ∉ earlier)
    (covered : ∀ pair ∈ earlier++real::later, pair.1 ∈ rows)
    (fallback : Output Password Passphrase Seed) (target : Check) :
    (1-(earlier.length:ENNReal)*((Fintype.card (mode.Value Check Data):ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹))-
      ((rows.length-1:Nat):ENNReal)*W7Alias.delta ≤
      ((sampleTables (Password := Password) (Entropy := Entropy)).bind fun crypto =>
        FullPlantedResampling.original (Tail := Tail) (Data := Data) coordinates real.1 crypto real.2 target
          (mode.attack coordinates rows (earlier++real::later) fallback target)
          (fun _ result => decide (result.1=real))) true := by
  let loss := (1-(earlier.length:ENNReal)*((Fintype.card (mode.Value Check Data):ENNReal)⁻¹+(Fintype.card Seed:ENNReal)⁻¹))-
    ((rows.length-1:Nat):ENNReal)*W7Alias.delta
  have integrate {Value : Type} (law : PMF Value) (value : Value → ENNReal)
      (lower : ∀ item, loss ≤ value item) : loss ≤ moment law value :=
    (constant law loss).symm.le.trans (mono law _ _ lower)
  change loss ≤ moment (sampleTables (Password := Password) (Entropy := Entropy)) (fun crypto =>
    (FullPlantedResampling.original (Tail := Tail) (Data := Data) coordinates real.1 crypto real.2 target
      (mode.attack coordinates rows (earlier++real::later) fallback target) (fun _ result => decide (result.1=real))) true)
  simp_rw [FullPlantedResampling.resampling]
  simp only [FullPlantedResampling.programmed, MomentTools.probability,
    W3.programmed, W3.payload, W3.tagProgrammed, W3.omegaProgrammed,
    MomentTools.bind, moment_map, Function.comp_def]
  conv_rhs =>
    arg 2
    ext crypto
    rw [G8Transport.comm]
  rw [G8Transport.comm]
  conv_rhs =>
    arg 2
    ext container
    arg 2
    ext crypto
    rw [G8Transport.comm]
  conv_rhs =>
    arg 2
    ext container
    rw [G8Transport.comm]
  conv_rhs =>
    arg 2
    ext container
    arg 2
    ext seed
    arg 2
    ext crypto
    arg 2
    ext s
    rw [G8Transport.comm]
  conv_rhs =>
    arg 2
    ext container
    arg 2
    ext seed
    arg 2
    ext crypto
    rw [G8Transport.comm]
  conv_rhs =>
    arg 2
    ext container
    arg 2
    ext seed
    rw [G8Transport.comm]
  apply integrate
  intro container
  apply integrate
  intro seed
  apply integrate
  intro data
  have source_cache (crypto : Tables Password Entropy) :
      (FullSourceCoordinates.cipher coordinates real.1 crypto).symm container=
        entropy coordinates crypto (coordinates container) real.1 := by
    unfold entropy
    exact FullSourceCoordinates.inverse coordinates real.1 crypto container
  have estimate := Mode.pair_raw (Tail := Tail) mode coordinates (coordinates container) rows unique real earlier later absent
    covered fallback seed target data
  (try simp only [independentPair, MomentTools.bind, moment_map, Function.comp_def, FullPlantedResampling.score, source_cache, decide_eq_true_eq, Mode.output] at estimate ⊢)
  exact estimate

omit [Fintype Password] in
/-- Generation loss uses the actual T budget, zero for Omega-only and at most n for the other modes. -/
theorem Mode.generation_comparison (mode : Mode) (coordinates : Entropy ≃ State)
    (crypto : Tables Password Entropy) (real : Password × Passphrase) (rows : List Password)
    (pairs : List (Password × Passphrase)) (fallback : Output Password Passphrase Seed)
    (target : Check) (test : Seed → Output Password Passphrase Seed → Bool)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16) : (FullPlantedResampling.original (Tail := Tail) (Data := Data) coordinates real.1 crypto real.2 target
      (mode.attack coordinates rows pairs fallback target) test) true ≤
    (FullGenerationResampling.actual (Tail := Tail) (Data := Data) coordinates real.1 crypto real.2 target
      (mode.attack coordinates rows pairs fallback target) test) true+
        W2.delta pairs.length (pairs.length*mode.tCost) := by
  have close := FullGenerationResampling.bound (Tail := Tail) (Data := Data) coordinates real.1 crypto real.2 target
    (mode.attack coordinates rows pairs fallback target) test pairs.length (pairs.length*mode.tCost) entropyWidth seedWidth checkWidth
    (fun wallet data container => (Mode.counts mode coordinates container target data crypto wallet rows pairs fallback).2.2.2.1)
    (fun wallet data container => (Mode.counts mode coordinates container target data crypto wallet rows pairs fallback).2.2.2.2.1)
  simpa only [PMF.map_id] using (close id).2

end W7OtherTests

namespace W7Source
open W7OtherTests
open Gamma2Model W7Attack ProbabilityTools
open GameExpectation MomentTools
private theorem pair_probability {N : Nat} {Passphrase : Type} (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (pair : Fin N × Passphrase) :
    independentPair passwords phrases pair=passwords pair.1*phrases pair.2 := by
  rcases pair with ⟨password,phrase⟩
  exact independentPair_apply passwords phrases password phrase

variable {N n : Nat} {Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] Gamma2Model.execute TranscriptErasure.execute
  Gamma2Model.finalize W7Attack.entropy FullSourceCoordinates.cipher

def conditional (mode : Mode) (coordinates : Entropy ≃ State) (rows : List (Fin N))
    (pairs : List (Fin N × Passphrase)) (fallback : Output (Fin N) Passphrase Seed) (check : Check)
    (real : Fin N × Passphrase) : ENNReal :=
  moment sampleTables (fun crypto =>
    (FullPlantedResampling.original (Tail := Tail) (Data := Data) coordinates real.1 crypto real.2 check
      (mode.attack coordinates rows pairs fallback check) (fun target result => decide (result.2=target))) true)

variable (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
  (phrases : PMF Passphrase) (rows : List (Fin N))

def planted (pairs : List (Fin N × Passphrase)) (fallback : Output (Fin N) Passphrase Seed)
    (check : Check) : PMF Bool :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    FullPlantedResampling.original (Tail := Tail) (Data := Data) coordinates password crypto phrase check
      (mode.attack coordinates rows pairs fallback check) (fun target result => decide (result.2=target))

/-- Pair priors are independent, but the actual attack reuses each recovered row. -/
theorem planted_probability (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (pairs : List (Fin N × Passphrase))
    (fallback : Output (Fin N) Passphrase Seed) (check : Check) : (planted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows pairs fallback check) true=
      moment (independentPair passwords phrases) (conditional (Tail := Tail) (Data := Data) mode coordinates rows pairs fallback check) := by
  simp only [independentPair, MomentTools.bind, moment_map, Function.comp_def]
  rfl

/-- Sum the distinct tested pairs, retaining the exact number of earlier tests at each rank. -/
theorem seed_weighted (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (order : Fin (n+1) → Fin N × Passphrase)
    (injective : Function.Injective order) (covered : ∀ index, (order index).1 ∈ rows)
    (fallback : Output (Fin N) Passphrase Seed) (check : Check) :
    (∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2*
      (1-(index.val:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹)) ≤
      (planted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows (List.ofFn order) fallback check) true := by
  have allCovered : ∀ pair ∈ List.ofFn order, pair.1 ∈ rows := by
    intro pair member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact covered index
  have ranked (index : Fin (n+1)) :
      1-(index.val:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹ ≤
      conditional (Tail := Tail) (Data := Data) mode coordinates rows (List.ofFn order) fallback check (order index) := by
    let pairs := List.ofFn order
    have within : index.val < pairs.length := by simpa only [pairs, List.length_ofFn] using index.isLt
    have split := List.take_append_drop (index.val+1) pairs
    rw [List.take_succ_eq_append_getElem within, List.append_assoc, List.singleton_append] at split
    have decomposition : pairs=pairs.take index.val ++ order index :: pairs.drop (index.val+1) := by
      simpa only [pairs, List.getElem_ofFn, Fin.eta] using split.symm
    have before_length : (pairs.take index.val).length=index.val := by
      rw [List.length_take]
      exact Nat.min_eq_left (by omega)
    calc
      _ = moment (sampleTables (Password := Fin N) (Entropy := Entropy))
          (fun _ => 1-(index.val:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹) := (constant _ _).symm
      _ ≤ _ := by
        apply mono
        intro crypto
        have estimate := Mode.seed_planted (Tail := Tail) (Data := Data) mode coordinates crypto rows (order index)
          (pairs.take index.val) (pairs.drop (index.val+1))
          (by simpa only [← decomposition] using allCovered) fallback check
        simpa only [← decomposition, before_length] using estimate
  rw [planted_probability]
  have estimate := RankedCandidates.weighted_lower (independentPair passwords phrases) order injective
    (Fintype.card (mode.Value Check Data):ENNReal)⁻¹ (conditional (Tail := Tail) (Data := Data) mode coordinates rows (List.ofFn order) fallback check) ranked
  simpa only [pair_probability] using estimate

/-- The whole real-generation output is close to the planted attack; no programming-removal upper bound is used here. -/
theorem generation_transfer (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (pairs : List (Fin N × Passphrase))
    (fallback : Output (Fin N) Passphrase Seed) (check : Check)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16) : (planted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows pairs fallback check) true ≤
      (FullSourceTransfer.original (Tail := Tail) (Data := Data) coordinates passwords phrases check (mode.attack coordinates rows pairs fallback check)
        (fun _ _ target result => decide (result.2=target))) true+W2.delta pairs.length (pairs.length*mode.tCost) := by
  apply FullSourceTransfer.bind_probability
  intro password
  apply FullSourceTransfer.bind_probability
  intro phrase
  apply FullSourceTransfer.bind_probability
  intro crypto
  exact Mode.generation_comparison (Tail := Tail) (Data := Data) mode coordinates crypto (password,phrase) rows pairs fallback check
    (fun target result => decide (result.2=target)) entropyWidth seedWidth checkWidth

/-- The weighted seed bound is retained under actual profile generation before the first creation refusal. -/
theorem actual_seed_weighted (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (order : Fin (n+1) → Fin N × Passphrase)
    (injective : Function.Injective order) (covered : ∀ index, (order index).1 ∈ rows)
    (fallback : Output (Fin N) Passphrase Seed) (check : Check)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16) :
    (∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2*
      (1-(index.val:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹))-W2.delta (n+1) ((n+1)*mode.tCost) ≤
      (FullSourceTransfer.original (Tail := Tail) (Data := Data) coordinates passwords phrases check
        (mode.attack coordinates rows (List.ofFn order) fallback check) (fun _ _ target result => decide (result.2=target))) true := by
  have base := seed_weighted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows order injective covered fallback check
  have comparison := generation_transfer (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows (List.ofFn order) fallback check
    entropyWidth seedWidth checkWidth
  rw [List.length_ofFn] at comparison
  exact tsub_le_iff_right.mpr (base.trans comparison)

/-- Replacing each rank by the last tested rank gives W7's common multiplicative false-match loss. -/
theorem seed_coarse (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (order : Fin (n+1) → Fin N × Passphrase)
    (injective : Function.Injective order) (covered : ∀ index, (order index).1 ∈ rows)
    (fallback : Output (Fin N) Passphrase Seed) (check : Check) :
    (∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2)*
      (1-(n:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹) ≤
      (planted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows (List.ofFn order) fallback check) true := by
  have weighted := seed_weighted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows order injective covered fallback check
  rw [planted_probability] at weighted ⊢
  have coarse := RankedCandidates.coarse_lower (independentPair passwords phrases) order
    (Fintype.card (mode.Value Check Data):ENNReal)⁻¹ (conditional (Tail := Tail) (Data := Data) mode coordinates rows (List.ofFn order) fallback check)
    (by simpa only [pair_probability] using weighted)
  simpa only [pair_probability] using coarse

/-- This is the actual source game with its first-creation refusal and arbitrary later response. -/
def seed_game (pairs : List (Fin N × Passphrase)) (fallback : Output (Fin N) Passphrase Seed)
    (check : Check)
    (later : FullSourceEnvironment.Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool) :
    PMF Bool :=
  FullSourceRefusal.game coordinates passwords phrases check
    (FullSourceEnvironment.score coordinates (mode.attack coordinates rows pairs fallback check)
      (fun _ _ target result => decide (result.2=target))) later

/-- W7's weighted seed estimate includes both actual generation and the first creation refusal. -/
theorem seed_refused (order : Fin (n+1) → Fin N × Passphrase) (injective : Function.Injective order)
    (covered : ∀ index, (order index).1 ∈ rows) (fallback : Output (Fin N) Passphrase Seed)
    (check : Check)
    (later : FullSourceEnvironment.Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16) :
    (∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2*
      (1-(index.val:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹))-W2.delta (n+1) ((n+1)*mode.tCost)-(2^256:ENNReal)⁻¹ ≤
      (seed_game mode coordinates passwords phrases rows (List.ofFn order) fallback check later) true := by
  have base := actual_seed_weighted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows order injective
    covered fallback check entropyWidth seedWidth checkWidth
  rw [FullSourceEnvironment.original] at base
  have result := RefusalResponseLower.bound
    (FullSourceRefusal.initial passwords phrases check) (FullSourceRefusal.refused coordinates)
    (FullSourceEnvironment.score coordinates (mode.attack coordinates rows (List.ofFn order) fallback check)
      (fun _ _ target result => decide (result.2=target))) later _ base
  rw [FullSourceRefusal.probability] at result
  exact result

/-- The common seed loss has the same generation and refusal terms as the weighted form. -/
theorem seed_refused_coarse (order : Fin (n+1) → Fin N × Passphrase)
    (injective : Function.Injective order) (covered : ∀ index, (order index).1 ∈ rows)
    (fallback : Output (Fin N) Passphrase Seed) (check : Check)
    (later : FullSourceEnvironment.Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16) :
    ((∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2)*
      (1-(n:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹))-W2.delta (n+1) ((n+1)*mode.tCost)-(2^256:ENNReal)⁻¹ ≤
      (seed_game mode coordinates passwords phrases rows (List.ofFn order) fallback check later) true := by
  have coarse := seed_coarse (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows order injective covered fallback check
  have comparison := generation_transfer (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows (List.ofFn order) fallback check
    entropyWidth seedWidth checkWidth
  rw [List.length_ofFn] at comparison
  have base := tsub_le_iff_right.mpr (coarse.trans comparison)
  rw [FullSourceEnvironment.original] at base
  have result := RefusalResponseLower.bound
    (FullSourceRefusal.initial passwords phrases check) (FullSourceRefusal.refused coordinates)
    (FullSourceEnvironment.score coordinates (mode.attack coordinates rows (List.ofFn order) fallback check)
      (fun _ _ target result => decide (result.2=target))) later _ base
  rw [FullSourceRefusal.probability] at result
  exact result

/-- Choosing the tested set with mass top2 gives the stated main term; W1.top2_attained supplies such finite sets. -/
theorem seed_top2 (mode : Mode) (m : Nat) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (order : Fin (n+1) → Fin N × Passphrase)
    (injective : Function.Injective order) (covered : ∀ index, (order index).1 ∈ rows)
    (fallback : Output (Fin N) Passphrase Seed) (check : Check)
    (selected_mass : (∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2)= W1.top2 passwords phrases m (n+1))
    (later : FullSourceEnvironment.Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16) :
    (W1.top2 passwords phrases m (n+1)*(1-(n:ENNReal)*(Fintype.card (mode.Value Check Data):ENNReal)⁻¹))-
      W2.delta (n+1) ((n+1)*mode.tCost)-(2^256:ENNReal)⁻¹ ≤
      (seed_game mode coordinates passwords phrases rows (List.ofFn order) fallback check later) true := by
  have estimate := seed_refused_coarse mode coordinates passwords phrases rows order injective covered fallback check later
    entropyWidth seedWidth checkWidth
  simpa only [selected_mass] using estimate

end W7Source

namespace W7PairSource
open W7OtherTests
open Gamma2Model W7Attack ProbabilityTools
open GameExpectation MomentTools
variable {N n : Nat} {Entropy Passphrase Seed Check Tail Data : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Data] [DecidableEq Check]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail] [Fintype Data]
  [Nonempty Entropy] [Nonempty Seed] [Nonempty Check] [Nonempty Tail] [Nonempty Data]
attribute [local instance] FiniteBits.fintype
attribute [local irreducible] Gamma2Model.execute TranscriptErasure.execute
  Gamma2Model.finalize W7Attack.entropy FullSourceCoordinates.cipher

def conditional (mode : Mode) (coordinates : Entropy ≃ State) (rows : List (Fin N))
    (pairs : List (Fin N × Passphrase)) (fallback : Output (Fin N) Passphrase Seed) (check : Check)
    (real : Fin N × Passphrase) : ENNReal :=
  moment sampleTables (fun crypto =>
    (FullPlantedResampling.original (Tail := Tail) (Data := Data) coordinates real.1 crypto real.2 check
      (mode.attack coordinates rows pairs fallback check) (fun _ result => decide (result.1=real))) true)

def planted (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (pairs : List (Fin N × Passphrase))
    (fallback : Output (Fin N) Passphrase Seed) (check : Check) : PMF Bool :=
  passwords.bind fun password => phrases.bind fun phrase => sampleTables.bind fun crypto =>
    FullPlantedResampling.original (Tail := Tail) (Data := Data) coordinates password crypto phrase check
      (mode.attack coordinates rows pairs fallback check) (fun _ result => decide (result.1=(password,phrase)))

/-- The same independent secret prior is used for pair recovery. -/
theorem probability (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (pairs : List (Fin N × Passphrase))
    (fallback : Output (Fin N) Passphrase Seed) (check : Check) : (planted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows pairs fallback check) true=
      moment (independentPair passwords phrases) (conditional (Tail := Tail) (Data := Data) mode coordinates rows pairs fallback check) := by
  simp only [independentPair, MomentTools.bind, moment_map, Function.comp_def]
  rfl

/-- The pair loss pays for preceding S/Omega tests and at most one alias per other password row. -/
theorem coarse (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (unique : rows.Nodup)
    (order : Fin (n+1) → Fin N × Passphrase) (injective : Function.Injective order)
    (covered : ∀ index, (order index).1 ∈ rows) (fallback : Output (Fin N) Passphrase Seed)
    (check : Check) :
    (∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2)*
      ((1-(n:ENNReal)*W7Pair.beta (Seed := Seed) (Data := mode.Value Check Data))-
        ((rows.length-1:Nat):ENNReal)*W7Alias.delta) ≤
      (planted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows (List.ofFn order) fallback check) true := by
  let pairs := List.ofFn order
  let loss := (1-(n:ENNReal)*W7Pair.beta (Seed := Seed) (Data := mode.Value Check Data))-
    ((rows.length-1:Nat):ENNReal)*W7Alias.delta
  have allCovered : ∀ pair ∈ pairs, pair.1 ∈ rows := by
    intro pair member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact covered index
  have ranked (index : Fin (n+1)) : loss ≤
      conditional (Tail := Tail) (Data := Data) mode coordinates rows pairs fallback check (order index) := by
    have within : index.val < pairs.length := by simpa only [pairs, List.length_ofFn] using index.isLt
    have split := List.take_append_drop (index.val+1) pairs
    rw [List.take_succ_eq_append_getElem within, List.append_assoc, List.singleton_append] at split
    have decomposition : pairs=pairs.take index.val ++ order index :: pairs.drop (index.val+1) := by
      simpa only [pairs, List.getElem_ofFn, Fin.eta] using split.symm
    have before_length : (pairs.take index.val).length=index.val := by
      rw [List.length_take]
      exact Nat.min_eq_left (by omega)
    have absent : order index ∉ pairs.take index.val := by
      intro member
      obtain ⟨j,within_j,equal⟩ := List.mem_take_iff_getElem.mp member
      have bound_j : j<n+1 := by
        simpa only [pairs, List.length_ofFn] using lt_of_lt_of_le within_j (Nat.min_le_right _ _)
      have same : order (⟨j,bound_j⟩ : Fin (n+1))=order index := by
        simpa only [pairs, List.getElem_ofFn] using equal
      have positions := congrArg Fin.val (injective same)
      have before := lt_of_lt_of_le within_j (Nat.min_le_left _ _)
      change j=index.val at positions
      omega
    have estimate := Mode.pair_planted (Tail := Tail) (Data := Data) mode coordinates rows unique (order index)
      (pairs.take index.val) (pairs.drop (index.val+1)) absent
      (by simpa only [← decomposition] using allCovered) fallback check
    simp only [← decomposition, before_length] at estimate
    have index_le : (index.val:ENNReal) ≤ (n:ENNReal) := by exact_mod_cast (show index.val≤n by omega)
    have losses := mul_le_mul_left index_le (W7Pair.beta (Seed := Seed) (Data := mode.Value Check Data))
    have smaller := tsub_le_tsub_right (tsub_le_tsub_left losses 1)
      (((rows.length-1:Nat):ENNReal)*W7Alias.delta)
    exact smaller.trans estimate
  rw [probability]
  have point (pair : Fin N × Passphrase) :
      independentPair passwords phrases pair=passwords pair.1*phrases pair.2 := by
    rcases pair with ⟨password,phrase⟩
    exact independentPair_apply passwords phrases password phrase
  calc
    _ = ∑ index : Fin (n+1), independentPair passwords phrases (order index)*loss := by
      rw [Finset.sum_mul]
      simp only [point, loss]
    _ ≤ ∑ index : Fin (n+1), independentPair passwords phrases (order index)*
        conditional (Tail := Tail) (Data := Data) mode coordinates rows pairs fallback check (order index) :=
      Finset.sum_le_sum (fun index _ => mul_le_mul_right (ranked index) _)
    _ ≤ _ := by
      simpa only [moment, tsum_fintype] using ENNReal.tsum_comp_le_tsum_of_injective injective
        (fun real => independentPair passwords phrases real*
          conditional (Tail := Tail) (Data := Data) mode coordinates rows pairs fallback check real)

/-- The response includes every later retry or failure after the first creation refusal. -/
def game (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (pairs : List (Fin N × Passphrase))
    (fallback : Output (Fin N) Passphrase Seed) (check : Check)
    (later : FullSourceEnvironment.Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool) :
    PMF Bool :=
  FullSourceRefusal.game coordinates passwords phrases check
    (FullSourceEnvironment.score coordinates (mode.attack coordinates rows pairs fallback check)
      (fun password phrase _ result => decide (result.1=(password,phrase)))) later

/-- W7's complete pair lower bound under actual profile generation and first creation refusal. -/
theorem refused (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (unique : rows.Nodup)
    (order : Fin (n+1) → Fin N × Passphrase) (injective : Function.Injective order)
    (covered : ∀ index, (order index).1 ∈ rows) (fallback : Output (Fin N) Passphrase Seed)
    (check : Check)
    (later : FullSourceEnvironment.Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16) :
    ((∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2)*
      ((1-(n:ENNReal)*W7Pair.beta (Seed := Seed) (Data := mode.Value Check Data))-
        ((rows.length-1:Nat):ENNReal)*W7Alias.delta))-
      W2.delta (n+1) ((n+1)*mode.tCost)-(2^256:ENNReal)⁻¹ ≤
      (game mode coordinates passwords phrases rows (List.ofFn order) fallback check later) true := by
  have lower := coarse (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows unique order injective covered fallback check
  have transfer : (planted (Tail := Tail) (Data := Data) mode coordinates passwords phrases rows (List.ofFn order) fallback check) true ≤
      (FullSourceTransfer.original (Tail := Tail) (Data := Data) coordinates passwords phrases check
        (mode.attack coordinates rows (List.ofFn order) fallback check) (fun password phrase _ result => decide (result.1=(password,phrase)))) true+
        W2.delta (n+1) ((n+1)*mode.tCost) := by
    apply FullSourceTransfer.bind_probability
    intro password
    apply FullSourceTransfer.bind_probability
    intro phrase
    apply FullSourceTransfer.bind_probability
    intro crypto
    simpa only [List.length_ofFn] using Mode.generation_comparison (Tail := Tail) (Data := Data) mode coordinates crypto (password,phrase)
      rows (List.ofFn order) fallback check (fun _ result => decide (result.1=(password,phrase))) entropyWidth seedWidth checkWidth
  have base := tsub_le_iff_right.mpr (lower.trans transfer)
  rw [FullSourceEnvironment.original] at base
  have result := RefusalResponseLower.bound
    (FullSourceRefusal.initial passwords phrases check) (FullSourceRefusal.refused coordinates)
    (FullSourceEnvironment.score coordinates (mode.attack coordinates rows (List.ofFn order) fallback check)
      (fun password phrase _ result => decide (result.1=(password,phrase)))) later _ base
  rw [FullSourceRefusal.probability] at result
  exact result

/-- The maximizing tested set substitutes top2 into W7's pair estimate. -/
theorem top2 (mode : Mode) (coordinates : Entropy ≃ State) (passwords : PMF (Fin N))
    (phrases : PMF Passphrase) (rows : List (Fin N)) (unique : rows.Nodup)
    (order : Fin (n+1) → Fin N × Passphrase) (injective : Function.Injective order)
    (covered : ∀ index, (order index).1 ∈ rows) (fallback : Output (Fin N) Passphrase Seed)
    (check : Check)
    (selected_mass : (∑ index : Fin (n+1), passwords (order index).1*phrases (order index).2)= W1.top2 passwords phrases rows.length (n+1))
    (later : FullSourceEnvironment.Context N Entropy Passphrase Seed Check Tail Data × TableFactors.HTable → PMF Bool)
    (entropyWidth : Fintype.card Entropy=2^256) (seedWidth : Fintype.card Seed=2^512)
    (checkWidth : Fintype.card Check=2^16) :
    (W1.top2 passwords phrases rows.length (n+1)*
      ((1-(n:ENNReal)*W7Pair.beta (Seed := Seed) (Data := mode.Value Check Data))-
        ((rows.length-1:Nat):ENNReal)*W7Alias.delta))-
      W2.delta (n+1) ((n+1)*mode.tCost)-(2^256:ENNReal)⁻¹ ≤
      (game mode coordinates passwords phrases rows (List.ofFn order) fallback check later) true := by
  have estimate := refused mode coordinates passwords phrases rows unique order injective covered fallback check later
    entropyWidth seedWidth checkWidth
  simpa only [selected_mass] using estimate

end W7PairSource

end
end MhfeLean
