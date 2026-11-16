-- long: The operational model, connected proof and its consequences form one mathematical chapter.
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MhfeLean.Chapters.Feistel
import MhfeLean.Chapters.ShortSources

namespace MhfeLean
noncomputable section

/-! # Sequential profile generation and its selected output
-/

/-! Exact first-success completion law on a fixed nonempty passing set. -/
namespace AcceptedUniform
variable {Entropy : Type} [Fintype Entropy] [Nonempty Entropy] [DecidableEq Entropy]

/-- Replacing a failed uniform trial by an independent uniform passing value preserves that law. -/
theorem renewal (accepted : Finset Entropy) (nonempty : accepted.Nonempty) :
    (PMF.uniformOfFintype Entropy).bind (fun e =>
      if e ∈ accepted then PMF.pure e else PMF.uniformOfFinset accepted nonempty) =
      PMF.uniformOfFinset accepted nonempty := by
  ext point
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (fun _ _ => ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))]
  simp only [ENNReal.toReal_mul, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have cards : accepted.card ≤ Fintype.card Entropy := Finset.card_le_univ _
  have npos : (Fintype.card Entropy : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have mpos : (accepted.card : ℝ) ≠ 0 := by exact_mod_cast nonempty.card_pos.ne'
  by_cases member : point ∈ accepted
  · have outside (e : Entropy) :
      (if e ∈ accepted then PMF.pure e else PMF.uniformOfFinset accepted nonempty) point =
        if e ∈ accepted then (if point = e then 1 else 0) else (accepted.card : ENNReal)⁻¹ := by
      split_ifs <;> simp_all [PMF.pure_apply, PMF.uniformOfFinset_apply]
    simp_rw [outside]
    simp only [apply_ite, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_one, ENNReal.toReal_zero, mul_one, mul_zero]
    rw [Finset.sum_ite]
    have subset : Finset.univ.filter (fun e => e ∈ accepted) = accepted := by ext e; simp
    have rejectedCard : (Finset.univ.filter (fun e => e ∉ accepted)).card = Fintype.card Entropy-accepted.card := by
      calc
        _ = (Finset.univ \ accepted).card := by congr 1; ext e; simp
        _ = _ := by simpa only [Finset.card_univ] using Finset.card_sdiff_of_subset (Finset.subset_univ accepted)
    rw [subset]
    simp only [Finset.sum_ite_eq, member, if_true, Finset.sum_const, nsmul_eq_mul, rejectedCard]
    rw [PMF.uniformOfFinset_apply_of_mem nonempty member, ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_sub cards]
    field_simp
    ring
  · have allZero (e : Entropy) :
      (if e ∈ accepted then PMF.pure e else PMF.uniformOfFinset accepted nonempty) point = 0 := by
      split_ifs with acceptedE
      · have different : point ≠ e := by intro same; subst point; exact member acceptedE
        simp only [PMF.pure_apply, different, if_false]
      · exact PMF.uniformOfFinset_apply_of_notMem nonempty member
    simp_rw [allZero]
    simp only [ENNReal.toReal_zero, mul_zero, Finset.sum_const_zero,
      PMF.uniformOfFinset_apply_of_notMem nonempty member]

end AcceptedUniform

/-! Exact independent uniform trial-list laws and their consistent prefixes. -/
namespace RandomTrialLists
open ProbabilityTools
variable {Entropy : Type} [Fintype Entropy] [Nonempty Entropy]

def law (count : Nat) : PMF (List Entropy) :=
  (PMF.uniformOfFintype (Fin count → Entropy)).map List.ofFn

def appendOne (count : Nat) : ((Fin count → Entropy) × Entropy) ≃ (Fin (count+1) → Entropy) where
  toFun := fun pair => Fin.snoc pair.1 pair.2
  invFun := fun trials => (Fin.init trials, trials (Fin.last count))
  left_inv := by intro pair; simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv := by intro trials; exact Fin.snoc_init_self trials

omit [Fintype Entropy] [Nonempty Entropy] in
theorem list_append (count : Nat) (savedPrefix : Fin count → Entropy) (last : Entropy) :
    List.ofFn (appendOne count (savedPrefix,last)) = List.ofFn savedPrefix ++ [last] := by
  rw [List.ofFn_succ_last]
  simp only [appendOne, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last]

/-- One more trial is an independent draw appended after the existing prefix. -/
theorem step (count : Nat) : law (Entropy := Entropy) (count+1) =
      (law count).bind fun trials => (PMF.uniformOfFintype Entropy).map fun e => trials ++ [e] := by
  have transported := PMF.uniformOfFintype_map_of_bijective (appendOne (Entropy := Entropy) count)
    (appendOne count).bijective
  unfold law
  calc
    _ = ((PMF.uniformOfFintype ((Fin count → Entropy) × Entropy)).map (appendOne count)).map List.ofFn := by rw [transported]
    _ = (PMF.uniformOfFintype ((Fin count → Entropy) × Entropy)).map (fun pair => List.ofFn pair.1 ++ [pair.2]) := by
      rw [PMF.map_comp]
      congr 1
      funext pair
      exact list_append count pair.1 pair.2
    _ = _ := by
      rw [uniform_product]
      simp only [independentPair, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]

/-- A prefix of a uniformly sampled full vector is itself an independent uniform prefix. -/
theorem prefix_law (count extra : Nat) :
    (PMF.uniformOfFintype (Fin (count+extra) → Entropy)).map
      (fun trials => fun index : Fin count => trials (Fin.castAdd extra index)) =
      PMF.uniformOfFintype (Fin count → Entropy) := by
  have transported := PMF.uniformOfFintype_map_of_bijective
    (Fin.appendEquiv (α := Entropy) count extra).symm (Fin.appendEquiv count extra).symm.bijective
  calc
    _ = ((PMF.uniformOfFintype (Fin (count+extra) → Entropy)).map
        (Fin.appendEquiv count extra).symm).map Prod.fst := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [transported, uniform_fst]

/-- The trial count is exact on the support, without enumerating any trial vector. -/
theorem support_length (count : Nat) (trials : List Entropy) (member : trials ∈ (law count).support) :
    trials.length = count := by
  obtain ⟨vector, _, equal⟩ := (PMF.mem_support_map_iff _ _ trials).mp member
  rw [← equal, List.length_ofFn]

end RandomTrialLists

/-! Uniform trial prefixes and exact completion by a stationary first-success law. -/
namespace FirstSuccess
open ProbabilityTools
variable {Entropy Result : Type} [Fintype Entropy] [Nonempty Entropy] [DecidableEq Entropy]

def prependOne (count : Nat) : (Entropy × (Fin count → Entropy)) ≃ (Fin (count+1) → Entropy) where
  toFun := fun pair => Fin.cons pair.1 pair.2
  invFun := fun vector => (vector 0,Fin.tail vector)
  left_inv := by intro pair; simp only [Fin.cons_zero, Fin.tail_cons]
  right_inv := by intro vector; exact Fin.cons_self_tail vector

omit [Fintype Entropy] [Nonempty Entropy] [DecidableEq Entropy] in
theorem cons_list (count : Nat) (head : Entropy) (rest : Fin count → Entropy) :
    List.ofFn (prependOne count (head,rest)) = head :: List.ofFn rest := by
  rw [List.ofFn_succ]
  simp only [prependOne, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]

omit [DecidableEq Entropy] in
theorem front_law (count : Nat) : RandomTrialLists.law (Entropy := Entropy) (count+1) =
      (PMF.uniformOfFintype Entropy).bind fun head =>
        (RandomTrialLists.law count).map (fun rest => head :: rest) := by
  have transported := PMF.uniformOfFintype_map_of_bijective (prependOne (Entropy := Entropy) count) (prependOne count).bijective
  unfold RandomTrialLists.law
  calc
    _ = ((PMF.uniformOfFintype (Entropy × (Fin count → Entropy))).map (prependOne count)).map List.ofFn := by rw [transported]
    _ = (PMF.uniformOfFintype (Entropy × (Fin count → Entropy))).map (fun pair => pair.1 :: List.ofFn pair.2) := by
      rw [PMF.map_comp]
      congr 1
      funext pair
      exact cons_list count pair.1 pair.2
    _ = _ := by
      rw [uniform_product]
      simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- A failure uses a continuation distribution without resampling the fixed oracle functions. -/
def finish (accepted : Finset Entropy) (make : Entropy → Result) (fallback : PMF Result) : List Entropy → PMF Result
  | [] => fallback
  | e :: rest => if e ∈ accepted then PMF.pure (make e) else finish accepted make fallback rest

def completed (count : Nat) (accepted : Finset Entropy) (make : Entropy → Result)
    (fallback : PMF Result) : PMF Result :=
  (RandomTrialLists.law (Entropy := Entropy) count).bind (finish accepted make fallback)

/-- A stationary first-success law remains exact after every finite prefix, not just in a limit. -/
theorem completion (count : Nat) (accepted : Finset Entropy) (make : Entropy → Result) (fallback : PMF Result)
    (stationary : (PMF.uniformOfFintype Entropy).bind
      (fun e => if e ∈ accepted then PMF.pure (make e) else fallback) = fallback) :
    completed count accepted make fallback = fallback := by
  induction count with
  | zero =>
    simp only [completed, RandomTrialLists.law, PMF.bind_map, Function.comp_def, List.ofFn_zero, finish, PMF.bind_const]
  | succ count ih =>
    rw [completed, front_law]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, finish]
    have reduced (e : Entropy) :
        ((RandomTrialLists.law (Entropy := Entropy) count).bind
          (fun rest => if e ∈ accepted then PMF.pure (make e) else finish accepted make fallback rest)) =
            if e ∈ accepted then PMF.pure (make e) else fallback := by
      split_ifs
      · exact PMF.bind_const _ _
      · exact ih
    simp_rw [reduced]
    exact stationary

end FirstSuccess

/-! Concrete sequential first-pass generation and transcript erasure for W2. -/
namespace WalletGeneration
open TranscriptErasure
variable {Entropy Passphrase Seed Check Tail Output : Type}

inductive Point (Entropy Passphrase Seed : Type)
  | s (entropy : Entropy) (passphrase : Passphrase)
  | t (seed : Seed)
  deriving DecidableEq

@[reducible] def spec (Entropy Passphrase Seed Check Tail : Type) : OracleSpec (Point Entropy Passphrase Seed)
  | .s _ _ => Seed
  | .t _ => Check × Tail

structure Selected (Entropy Seed Tail : Type) where
  entropy : Entropy
  seed : Seed
  tail : Tail

variable [DecidableEq Check]

/-- Trials are supplied independently of the tables, and only the first passing one is selected. -/
def loop (passphrase : Passphrase) (target : Check) : List Entropy →
    OracleComp (spec Entropy Passphrase Seed Check Tail) (Option (Selected Entropy Seed Tail))
  | [] => pure none
  | entropy :: trials => do
    let seed : Seed ← ask (spec := spec Entropy Passphrase Seed Check Tail) (Point.s entropy passphrase)
    let digest : Check × Tail ← ask (spec := spec Entropy Passphrase Seed Check Tail) (Point.t seed)
    if digest.1 = target then pure (some ⟨entropy, seed, digest.2⟩)
    else loop passphrase target trials

theorem execution_cons (table : Table (spec Entropy Passphrase Seed Check Tail))
    (passphrase : Passphrase) (target : Check) (entropy : Entropy) (trials : List Entropy) :
    execute table (loop passphrase target (entropy :: trials)) =
      let seed : Seed := table (Point.s entropy passphrase)
      let digest : Check × Tail := table (Point.t seed)
      if digest.1 = target then (some ⟨entropy, seed, digest.2⟩, [Point.s entropy passphrase, Point.t seed])
      else let rest := execute table (loop passphrase target trials)
        (rest.1, [Point.s entropy passphrase, Point.t seed] ++ rest.2) := by
  conv_lhs => unfold loop
  rw [execute_bind, execute_ask]
  dsimp only
  rw [execute_bind, execute_ask]
  dsimp only
  split_ifs <;> simp only [execute_pure, List.append_nil, List.singleton_append]
  rfl

theorem selected_values (table : Table (spec Entropy Passphrase Seed Check Tail))
    (passphrase : Passphrase) (target : Check) (trials : List Entropy)
    (chosen : Selected Entropy Seed Tail)
    (success : (execute table (loop passphrase target trials)).1 = some chosen) :
    table (Point.s chosen.entropy passphrase) = chosen.seed ∧
      table (Point.t chosen.seed) = (target, chosen.tail) := by
  induction trials with
  | nil => cases success
  | cons entropy trials ih =>
    rw [execution_cons] at success
    dsimp only at success
    split_ifs at success with passing
    · have same := Option.some.inj success
      subst chosen
      refine ⟨rfl, ?_⟩
      exact Prod.ext passing rfl
    · exact ih success

def restore [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
    (passphrase : Passphrase) (target : Check) (chosen : Option (Selected Entropy Seed Tail))
    (fresh : Table (spec Entropy Passphrase Seed Check Tail)) :
    Table (spec Entropy Passphrase Seed Check Tail) :=
  match chosen with
  | none => fresh
  | some selected => fun point => match point with
    | .s entropy candidate => if entropy = selected.entropy ∧ candidate = passphrase then selected.seed else fresh (Point.s entropy candidate)
    | .t seed => if seed = selected.seed then (target, selected.tail) else fresh (Point.t seed)

noncomputable section
variable [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] [Fintype Check] [Fintype Tail]
  [Nonempty Seed] [Nonempty Check] [Nonempty Tail]
local instance (point : Point Entropy Passphrase Seed) : Fintype (spec Entropy Passphrase Seed Check Tail point) := by
  cases point <;> dsimp only [spec] <;> infer_instance
local instance (point : Point Entropy Passphrase Seed) : Nonempty (spec Entropy Passphrase Seed Check Tail point) := by
  cases point <;> dsimp only [spec] <;> infer_instance
local instance : Fintype (Point Entropy Passphrase Seed) :=
  Fintype.ofEquiv ((Entropy × Passphrase) ⊕ Seed)
    { toFun := fun point => match point with | .inl pair => .s pair.1 pair.2 | .inr seed => .t seed
      invFun := fun point => match point with | .s e q => .inl (e,q) | .t d => .inr d
      left_inv := by intro point; cases point <;> rfl
      right_inv := by intro point; cases point <;> rfl }

/-- Erasing rejected reads and restoring the selected pair has exactly a fresh-table representation. -/
theorem erasure_law (passphrase : Passphrase) (target : Check) (trials : List Entropy)
    (view : Option (Selected Entropy Seed Tail) → Table (spec Entropy Passphrase Seed Check Tail) → Output) :
    (PMF.uniformOfFintype (Table (spec Entropy Passphrase Seed Check Tail) × Table (spec Entropy Passphrase Seed Check Tail))).map
      (fun tables => let trace := execute tables.1 (loop passphrase target trials)
        view trace.1 (restore passphrase target trace.1 (exchanged (loop passphrase target trials) tables).2)) =
    (PMF.uniformOfFintype (Table (spec Entropy Passphrase Seed Check Tail) × Table (spec Entropy Passphrase Seed Check Tail))).map
      (fun tables => let trace := execute tables.1 (loop passphrase target trials)
        view trace.1 (restore passphrase target trace.1 tables.2)) :=
  erased_distribution (loop passphrase target trials)
    (fun trace fresh => view trace.1 (restore passphrase target trace.1 fresh))

end
end WalletGeneration

/-! Exact equivariance of first-pass generation under entropy, seed and tail relabelling. -/
namespace WalletSymmetry
open TranscriptErasure WalletGeneration
variable {Entropy Passphrase Seed Check Tail : Type}

def selected (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail)
    (value : Selected Entropy Seed Tail) : Selected Entropy Seed Tail :=
  ⟨entropy value.entropy, seed value.seed, tail value.tail⟩

def point (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) :
    Point Entropy Passphrase Seed → Point Entropy Passphrase Seed
  | .s e q => .s (entropy e) q
  | .t d => .t (seed d)

variable (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail)
  (table : Table (spec Entropy Passphrase Seed Check Tail))

def relabel : Table (spec Entropy Passphrase Seed Check Tail) :=
  fun p => match p with
  | .s e q => seed (table (Point.s (entropy.symm e) q))
  | .t d => let digest : Check × Tail := table (Point.t (seed.symm d))
    (digest.1, tail digest.2)

theorem relabel_inverse :
    relabel entropy.symm seed.symm tail.symm (relabel entropy seed tail table) = table := by
  funext p
  cases p with
  | s e q =>
    change seed.symm (seed (table (Point.s (entropy.symm (entropy e)) q))) = _
    rw [entropy.symm_apply_apply, seed.symm_apply_apply]
  | t d =>
    change ((table (Point.t (seed.symm (seed d)))).1,
      tail.symm (tail (table (Point.t (seed.symm (seed d)))).2)) = _
    rw [seed.symm_apply_apply, tail.symm_apply_apply]
    try exact Prod.eta _

def tableEquiv (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail) :
    Equiv.Perm (Table (spec Entropy Passphrase Seed Check Tail)) where
  toFun := relabel entropy seed tail
  invFun := relabel entropy.symm seed.symm tail.symm
  left_inv := relabel_inverse entropy seed tail
  right_inv := by
    intro table
    simpa only [Equiv.symm_symm] using relabel_inverse entropy.symm seed.symm tail.symm table

theorem relabel_s (e : Entropy) (q : Passphrase) :
    relabel entropy seed tail table (Point.s (entropy e) q) = seed (table (Point.s e q)) := by
  change seed (table (Point.s (entropy.symm (entropy e)) q)) = _
  rw [entropy.symm_apply_apply]

theorem relabel_t (d : Seed) :
    relabel entropy seed tail table (Point.t (seed d)) = ((table (Point.t d)).1, tail (table (Point.t d)).2) := by
  change ((table (Point.t (seed.symm (seed d)))).1, tail (table (Point.t (seed.symm (seed d)))).2) = _
  rw [seed.symm_apply_apply]

variable [DecidableEq Check]

/-- Both the chosen triple and the complete read log transform exactly; the stopping index is preserved. -/
theorem loop_natural (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed)
    (tail : Equiv.Perm Tail) (table : Table (spec Entropy Passphrase Seed Check Tail))
    (q : Passphrase) (target : Check) (trials : List Entropy) :
    execute (relabel entropy seed tail table) (loop q target (trials.map entropy)) =
      ((execute table (loop q target trials)).1.map (selected entropy seed tail),
        (execute table (loop q target trials)).2.map (point entropy seed)) := by
  induction trials with
  | nil => rfl
  | cons e trials ih =>
    rw [List.map_cons, execution_cons, execution_cons]
    rw [relabel_s entropy seed tail table e q]
    dsimp only
    rw [relabel_t entropy seed tail table]
    dsimp only
    split_ifs
    · rfl
    · rw [ih]
      rfl

end WalletSymmetry

/-! Finite ideal domains used in the wallet-generation probability experiments. -/
namespace WalletFinite
open WalletGeneration
variable {Entropy Passphrase Seed Check Tail : Type}

def pointEquiv : ((Entropy × Passphrase) ⊕ Seed) ≃ Point Entropy Passphrase Seed where
  toFun := fun point => match point with | .inl pair => .s pair.1 pair.2 | .inr seed => .t seed
  invFun := fun point => match point with | .s e q => .inl (e,q) | .t d => .inr d
  left_inv := by intro point; cases point <;> rfl
  right_inv := by intro point; cases point <;> rfl

instance [Fintype Entropy] [Fintype Passphrase] [Fintype Seed] : Fintype (Point Entropy Passphrase Seed) :=
  Fintype.ofEquiv _ pointEquiv

instance (point : Point Entropy Passphrase Seed) [Fintype Seed] [Fintype Check] [Fintype Tail] :
    Fintype (spec Entropy Passphrase Seed Check Tail point) := by
  cases point <;> dsimp only [spec] <;> infer_instance

instance (point : Point Entropy Passphrase Seed) [Nonempty Seed] [Nonempty Check] [Nonempty Tail] :
    Nonempty (spec Entropy Passphrase Seed Check Tail point) := by
  cases point <;> dsimp only [spec] <;> infer_instance

def selectedEquiv : Selected Entropy Seed Tail ≃ Entropy × Seed × Tail where
  toFun := fun value => (value.entropy, value.seed, value.tail)
  invFun := fun value => ⟨value.1, value.2.1, value.2.2⟩
  left_inv := by intro value; cases value; rfl
  right_inv := by intro value; cases value; rfl

instance [Fintype Entropy] [Fintype Seed] [Fintype Tail] : Fintype (Selected Entropy Seed Tail) :=
  Fintype.ofEquiv _ selectedEquiv.symm
instance [Nonempty Entropy] [Nonempty Seed] [Nonempty Tail] : Nonempty (Selected Entropy Seed Tail) :=
  by
    obtain ⟨value⟩ := (inferInstance : Nonempty (Entropy × Seed × Tail))
    exact ⟨selectedEquiv.symm value⟩

def selectedAction (entropy : Equiv.Perm Entropy) (seed : Equiv.Perm Seed) (tail : Equiv.Perm Tail) :
    Equiv.Perm (Selected Entropy Seed Tail) :=
  (selectedEquiv.trans (Equiv.prodCongr entropy (Equiv.prodCongr seed tail))).trans selectedEquiv.symm

def trialAction {count : Nat} (entropy : Equiv.Perm Entropy) : Equiv.Perm (Fin count → Entropy) where
  toFun := fun trials index => entropy (trials index)
  invFun := fun trials index => entropy.symm (trials index)
  left_inv := by intro trials; funext index; exact entropy.symm_apply_apply _
  right_inv := by intro trials; funext index; exact entropy.apply_symm_apply _

end WalletFinite

/-! Exact fixed-table first-success law; empty passing sets keep the original table prior. -/
namespace WalletCompletion
open WalletGeneration WalletFinite TranscriptErasure
variable {Entropy Passphrase Seed Check Tail : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed] [DecidableEq Check]
  [Fintype Entropy] [Nonempty Entropy] [Fintype Seed] [Fintype Tail] [Nonempty Seed] [Nonempty Tail]

abbrev Tables := Table (spec Entropy Passphrase Seed Check Tail)

local notation "WalletTables" => Tables (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)

def passing (table : WalletTables)
    (q : Passphrase) (target : Check) : Finset Entropy :=
  Finset.univ.filter fun e => (table (Point.t (table (Point.s e q)))).1 = target

def make (table : WalletTables)
    (q : Passphrase) (e : Entropy) : Selected Entropy Seed Tail :=
  ⟨e,table (Point.s e q),(table (Point.t (table (Point.s e q)))).2⟩

/-- If no value passes, define an arbitrary fallback without rejecting or redrawing the table. -/
def real (table : WalletTables)
    (q : Passphrase) (target : Check) : PMF (Selected Entropy Seed Tail) :=
  if nonempty : (passing table q target).Nonempty then
    (PMF.uniformOfFinset (passing table q target) nonempty).map (make table q)
  else PMF.uniformOfFintype (Selected Entropy Seed Tail)

omit [DecidableEq Passphrase] [DecidableEq Seed] in
/-- The continuation law is explicitly derived from uniform sampling on the passing set. -/
theorem stationary (table : WalletTables)
    (q : Passphrase) (target : Check) :
    (PMF.uniformOfFintype Entropy).bind (fun e => if e ∈ passing table q target then PMF.pure (make table q e) else real table q target) =
      real table q target := by
  unfold real
  split_ifs with nonempty
  · have transported := congrArg (fun distribution : PMF Entropy => distribution.map (make table q))
      (AcceptedUniform.renewal (passing table q target) nonempty)
    simpa only [PMF.map_bind, apply_ite, PMF.pure_map] using transported
  · have absent (e : Entropy) : e ∉ passing table q target := by
      intro member
      exact nonempty ⟨e,member⟩
    simp only [absent, if_false, PMF.bind_const]

omit [DecidableEq Passphrase] [DecidableEq Seed] [Nonempty Entropy]
  [Fintype Seed] [Fintype Tail] [Nonempty Seed] [Nonempty Tail] in
/-- The recursive PMF completion is exactly the actual stopping-loop result with the stated continuation. -/
theorem finish_loop (table : WalletTables)
    (q : Passphrase) (target : Check) (continuation : PMF (Selected Entropy Seed Tail)) (trials : List Entropy) :
    FirstSuccess.finish (passing table q target) (make table q) continuation trials =
      match (execute table (loop q target trials)).1 with | none => continuation | some chosen => PMF.pure chosen := by
  induction trials with
  | nil => rfl
  | cons e rest ih =>
    rw [FirstSuccess.finish, execution_cons]
    dsimp only
    have member : e ∈ passing table q target ↔ (table (Point.t (table (Point.s e q)))).1 = target := by simp only [passing, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [member]
    split_ifs
    · rfl
    · exact ih

omit [DecidableEq Passphrase] [DecidableEq Seed] in
/-- A finite prefix followed by fresh uniform-on-passing continuation has exactly the real selected-triple law. -/
theorem completed_loop (count : Nat)
    (table : WalletTables)
    (q : Passphrase) (target : Check) :
    (RandomTrialLists.law (Entropy := Entropy) count).bind (fun trials =>
      match (execute table (loop q target trials)).1 with | none => real table q target | some chosen => PMF.pure chosen) =
      real table q target := by
  have completed := FirstSuccess.completion count (passing table q target) (make table q) (real table q target)
    (stationary table q target)
  unfold FirstSuccess.completed at completed
  have same : FirstSuccess.finish (passing table q target) (make table q) (real table q target) =
      fun trials => match (execute table (loop q target trials)).1 with | none => real table q target | some chosen => PMF.pure chosen := by
    funext trials
    exact finish_loop table q target (real table q target) trials
  rw [same] at completed
  exact completed

end WalletCompletion

/-!
A finite-branching oracle program has a finite set of potential query points,
even when the ambient normalized-passphrase domain is infinite. Restriction to
that finite set preserves all results and the complete projected transcript.
-/
namespace FiniteQuerySpace
open TranscriptErasure
variable {Point Result : Type} [DecidableEq Point] {spec : OracleSpec Point}
  [∀ point, Fintype (spec point)]

def space (program : OracleComp spec Result) : Finset Point :=
  OracleComp.construct (fun _ => ∅) (fun point _ recurse =>
    insert point (Finset.univ.biUnion recurse)) program

variable (point : Point) (next : spec point → OracleComp spec Result)

theorem query_shape :
    space (ask point >>= next) = insert point (Finset.univ.biUnion fun answer => space (next answer)) := rfl

theorem head_member : point ∈ space (ask point >>= next) := by
  rw [query_shape]
  exact Finset.mem_insert_self _ _

theorem branch_subset (answer : spec point) : space (next answer) ⊆ space (ask point >>= next) := by
  intro q member
  rw [query_shape]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨answer, Finset.mem_univ _, member⟩)

theorem coverage (table : Table spec) (program : OracleComp spec Result) :
    ∀ point ∈ (execute table program).2, point ∈ space program := by
  induction program using OracleComp.inductionOn with
  | pure result => intro point member; cases member
  | query_bind point next ih =>
    change ∀ q ∈ (execute table (ask point >>= next)).2, q ∈ space (ask point >>= next)
    rw [execute_bind, execute_ask, query_shape]
    simp only [List.singleton_append]
    intro q member
    rcases List.mem_cons.mp member with same | later
    · subst q
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨table point, Finset.mem_univ _, ih (table point) q later⟩)

end FiniteQuerySpace

/-! Distinct S and T query points extracted from an actual adversary log. -/
namespace WalletQuerySets
open WalletGeneration
variable {Entropy Passphrase Seed : Type} [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]

def sList (q : Passphrase) (queries : List (Point Entropy Passphrase Seed)) : List Entropy :=
  queries.filterMap fun point => match point with
    | .s e v => if v = q then some e else none
    | .t _ => none

def tList (queries : List (Point Entropy Passphrase Seed)) : List Seed :=
  queries.filterMap fun point => match point with
    | .s _ _ => none
    | .t seed => some seed

def sSet (q : Passphrase) (queries : List (Point Entropy Passphrase Seed)) : Finset Entropy :=
  (sList q queries).toFinset

def tSet (queries : List (Point Entropy Passphrase Seed)) : Finset Seed := (tList queries).toFinset

omit [DecidableEq Seed] in
@[simp] theorem s_mem (q : Passphrase) (queries : List (Point Entropy Passphrase Seed)) (e : Entropy) :
    e ∈ sSet q queries ↔ Point.s e q ∈ queries := by
  induction queries with
  | nil => simp [sSet, sList]
  | cons point queries ih =>
    cases point with
    | s candidate v =>
      by_cases same : v = q
      · simp_all [sSet, sList]
      · have opposite : q ≠ v := Ne.symm same
        simp_all [sSet, sList]
    | t seed => simp_all [sSet, sList]

omit [DecidableEq Entropy] [DecidableEq Passphrase] in
@[simp] theorem t_mem (queries : List (Point Entropy Passphrase Seed)) (seed : Seed) :
    seed ∈ tSet queries ↔ Point.t seed ∈ queries := by
  induction queries with
  | nil => simp [tSet, tList]
  | cons point queries ih =>
    cases point <;> simp_all [tSet, tList]

/-- Each extracted set is bounded by the actual number of queries of its kind, even with repeats. -/
theorem sizes (q : Passphrase) (queries : List (Point Entropy Passphrase Seed)) :
    (sSet q queries).card ≤ (sList q queries).length ∧ (tSet queries).card ≤ (tList queries).length :=
  ⟨List.toFinset_card_le _, List.toFinset_card_le _⟩

end WalletQuerySets

/-! Finite passphrase windows are derived from every potential branch, never from a realized table-dependent trace. -/
namespace WalletWindow
open WalletGeneration WalletFinite TranscriptErasure
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail]

abbrev Ambient := spec Entropy Passphrase Seed Check Tail

def points (adversary : Selected Entropy Seed Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result) :
    Finset (Point Entropy Passphrase Seed) :=
  Finset.univ.biUnion (fun chosen => FiniteQuerySpace.space (adversary chosen))

def passphrases (q : Passphrase)
    (adversary : Selected Entropy Seed Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result) : Finset Passphrase :=
  insert q ((points adversary).biUnion fun point => match point with | .s _ v => {v} | .t _ => ∅)

/-- The actual secret q is retained independently of whether the adversary ever guesses it. -/
theorem real_member (q : Passphrase)
    (adversary : Selected Entropy Seed Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result) :
    q ∈ passphrases q adversary := Finset.mem_insert_self _ _

/-- Every S passphrase on every potential answer branch and every selected triple is in the window. -/
theorem potential_member (q : Passphrase)
    (adversary : Selected Entropy Seed Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result)
    (chosen : Selected Entropy Seed Tail) (e : Entropy) (v : Passphrase)
    (member : Point.s e v ∈ FiniteQuerySpace.space (adversary chosen)) : v ∈ passphrases q adversary := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨Point.s e v,?_,?_⟩
  · exact Finset.mem_biUnion.mpr ⟨chosen,Finset.mem_univ _,member⟩
  · exact Finset.mem_singleton_self _

abbrev Small (window : Finset Passphrase) := spec Entropy {q // q ∈ window} Seed Check Tail

def embed (window : Finset Passphrase) : Point Entropy {q // q ∈ window} Seed → Point Entropy Passphrase Seed
  | .s e q => .s e q.val
  | .t seed => .t seed

/-- Outside-window queries abort only in the compiler; coverage proves that branch unreachable. -/
def narrow (window : Finset Passphrase)
    (program : OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result) :
    OracleComp (Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window) (Option Result) :=
  OracleComp.construct (fun result => pure (some result))
    (fun point _ recurse => match point with
      | .s e q => if member : q ∈ window then do
        let answer ← ask (spec := Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window) (.s e ⟨q,member⟩)
        recurse answer
        else pure none
      | .t seed => do
        let answer ← ask (spec := Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window) (.t seed)
        recurse answer) program

omit [DecidableEq Entropy] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] in
theorem narrow_s (window : Finset Passphrase) (e : Entropy) (v : Passphrase)
    (next : Seed → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result) :
    narrow window (ask (.s e v) >>= next) =
      if member : v ∈ window then ask (spec := Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window) (.s e ⟨v,member⟩) >>= fun answer => narrow window (next answer) else pure none := rfl

omit [DecidableEq Entropy] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] in
theorem narrow_t (window : Finset Passphrase) (seed : Seed)
    (next : Check × Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result) :
    narrow window (ask (.t seed) >>= next) = ask (spec := Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window) (.t seed) >>= fun answer => narrow window (next answer) := rfl

omit [DecidableEq Entropy] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] in
theorem narrow_pure (window : Finset Passphrase) (value : Result) : narrow (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window (pure value) = pure (some value) := rfl

attribute [local irreducible] narrow

/-- Restrict an arbitrary ambient table to the full rectangular S-window and all T points. -/
def restrictTable (window : Finset Passphrase)
    (table : Table (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))) :
    Table (Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)
  | .s e q => table (.s e q.val)
  | .t seed => table (.t seed)

omit [Fintype Entropy] in
/-- Projecting the narrowed execution recovers the exact result and full ambient query log. -/
theorem faithful (window : Finset Passphrase)
    (table : Table (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)))
    (program : OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result)
    (contained : ∀ e v, Point.s e v ∈ FiniteQuerySpace.space program → v ∈ window) :
    let run := execute (restrictTable window table) (narrow window program)
    (run.1,run.2.map (embed window)) = (some (execute table program).1,(execute table program).2) := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [narrow_pure, execute_pure, List.map_nil]
  | query_bind point next ih =>
    have later (answer : Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail) point) :
        ∀ e v, Point.s e v ∈ FiniteQuerySpace.space (next answer) → v ∈ window := by
      intro e v member
      exact contained e v (FiniteQuerySpace.branch_subset (spec := Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) point next answer member)
    cases point with
    | s e v =>
      have member := contained e v (FiniteQuerySpace.head_member (spec := Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) (.s e v) next)
      change ((execute (restrictTable window table) (narrow window (ask (.s e v) >>= next))).1,
        (execute (restrictTable window table) (narrow window (ask (.s e v) >>= next))).2.map (embed window)) = _
      rw [narrow_s, dif_pos member]
      simp only [execute_bind, execute_ask, restrictTable, List.singleton_append, List.map_cons, embed]
      have rest := ih (table (.s e v)) (later (table (.s e v)))
      change ((execute (restrictTable window table) (narrow window (next (table (.s e v))))).1,
        Point.s e v :: (execute (restrictTable window table) (narrow window (next (table (.s e v))))).2.map (embed window)) = _
      change _ = (some (execute table (next (table (.s e v)))).1,
        Point.s e v :: (execute table (next (table (.s e v)))).2)
      exact congrArg (fun observation : Option Result × List (Point Entropy Passphrase Seed) =>
        (observation.1,Point.s e v :: observation.2)) rest
    | t seed =>
      change ((execute (restrictTable window table) (narrow window (ask (.t seed) >>= next))).1,
        (execute (restrictTable window table) (narrow window (ask (.t seed) >>= next))).2.map (embed window)) = _
      rw [narrow_t]
      simp only [execute_bind, execute_ask, restrictTable, List.singleton_append, List.map_cons, embed]
      have rest := ih (table (.t seed)) (later (table (.t seed)))
      change _ = (some (execute table (next (table (.t seed)))).1,
        Point.t seed :: (execute table (next (table (.t seed)))).2)
      exact congrArg (fun observation : Option Result × List (Point Entropy Passphrase Seed) =>
        (observation.1,Point.t seed :: observation.2)) rest

/-- The derived window works uniformly for every table, including programmed tables. -/
theorem adversary_faithful (q : Passphrase)
    (adversary : Selected Entropy Seed Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result)
    (table : Table (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)))
    (chosen : Selected Entropy Seed Tail) :
    let window := passphrases q adversary
    let run := execute (restrictTable window table) (narrow window (adversary chosen))
    (run.1,run.2.map (embed window)) = (some (execute table (adversary chosen)).1,(execute table (adversary chosen)).2) :=
  faithful _ table (adversary chosen) (potential_member q adversary chosen)

end WalletWindow

/-! Finite-window compilation preserves the real passphrase's S queries and every T query. -/
namespace WalletWindowBudgets
open WalletGeneration WalletFinite TranscriptErasure WalletWindow
variable {Entropy Passphrase Seed Check Tail Result : Type}
  [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Nonempty Seed]

/-- Arbitrary values outside the predetermined window are never used by the compiled program. -/
def extendTable (window : Finset Passphrase)
    (table : Table (Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)) :
    Table (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail))
  | .s e q => if member : q ∈ window then table (.s e ⟨q,member⟩) else Classical.choice (inferInstance : Nonempty Seed)
  | .t seed => table (.t seed)

omit [DecidableEq Entropy] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] in
theorem restrict_extend (window : Finset Passphrase)
    (table : Table (Small (Entropy := Entropy) (Seed := Seed) (Check := Check) (Tail := Tail) window)) :
    restrictTable window (extendTable window table) = table := by
  funext point
  cases point with
  | s e q => simp only [restrictTable, extendTable, dif_pos q.property]
  | t seed => rfl

omit [DecidableEq Entropy] [DecidableEq Passphrase] [DecidableEq Seed]
  [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Nonempty Seed] in
theorem embed_injective (window : Finset Passphrase) : Function.Injective (embed (Entropy := Entropy) (Seed := Seed) window) := by
  intro first second equal
  cases first with
  | s e q =>
    cases second with
    | s e' q' =>
      change Point.s e q.val = Point.s e' q'.val at equal
      have values := Point.s.inj equal
      exact congrArg₂ Point.s values.1 (Subtype.ext values.2)
    | t seed => cases equal
  | t seed =>
    cases second with
    | s e q => cases equal
    | t other =>
      change Point.t seed = Point.t other at equal
      exact congrArg Point.t (Point.t.inj equal)

omit [DecidableEq Seed] [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Nonempty Seed] in
theorem s_projection (window : Finset Passphrase) (q : {q // q ∈ window})
    (queries : List (Point Entropy {q // q ∈ window} Seed)) :
    WalletQuerySets.sSet q queries = WalletQuerySets.sSet q.val (queries.map (embed window)) := by
  ext e
  rw [WalletQuerySets.s_mem, WalletQuerySets.s_mem, List.mem_map]
  constructor
  · intro queried
    exact ⟨Point.s e q,queried,rfl⟩
  · rintro ⟨point,queried,same⟩
    have equal : point = Point.s e q := embed_injective window same
    simpa only [equal] using queried

omit [DecidableEq Entropy] [DecidableEq Passphrase] [Fintype Entropy] [Fintype Seed] [Fintype Check] [Fintype Tail] [Nonempty Seed] in
theorem t_projection (window : Finset Passphrase)
    (queries : List (Point Entropy {q // q ∈ window} Seed)) :
    WalletQuerySets.tSet queries = WalletQuerySets.tSet (queries.map (embed window)) := by
  ext seed
  rw [WalletQuerySets.t_mem, WalletQuerySets.t_mem, List.mem_map]
  constructor
  · intro queried
    exact ⟨Point.t seed,queried,rfl⟩
  · rintro ⟨point,queried,same⟩
    have equal : point = Point.t seed := embed_injective window same
    simpa only [equal] using queried

/-- Both finite-view query budgets are consequences of the ambient adversary budgets. -/
theorem budgets (q : Passphrase)
    (adversary : Selected Entropy Seed Tail → OracleComp (Ambient (Entropy := Entropy) (Passphrase := Passphrase) (Seed := Seed) (Check := Check) (Tail := Tail)) Result)
    (kS qT : Nat)
    (sBudget : ∀ chosen table, (WalletQuerySets.sSet q (execute table (adversary chosen)).2).card ≤ kS)
    (tBudget : ∀ chosen table, (WalletQuerySets.tSet (execute table (adversary chosen)).2).card ≤ qT) :
    let window := passphrases q adversary
    let narrowQ : {q // q ∈ window} := ⟨q,real_member q adversary⟩
    (∀ chosen table, (WalletQuerySets.sSet narrowQ (execute table (narrow window (adversary chosen))).2).card ≤ kS) ∧
    (∀ chosen table, (WalletQuerySets.tSet (execute table (narrow window (adversary chosen))).2).card ≤ qT) := by
  dsimp only
  constructor
  · intro chosen table
    have faithful := adversary_faithful q adversary (extendTable (passphrases q adversary) table) chosen
    dsimp only at faithful
    rw [restrict_extend] at faithful
    have logs := congrArg Prod.snd faithful
    dsimp only at logs
    rw [s_projection, logs]
    exact sBudget chosen _
  · intro chosen table
    have faithful := adversary_faithful q adversary (extendTable (passphrases q adversary) table) chosen
    dsimp only at faithful
    rw [restrict_extend] at faithful
    have logs := congrArg Prod.snd faithful
    dsimp only at logs
    rw [t_projection, logs]
    exact tBudget chosen _

end WalletWindowBudgets

end
end MhfeLean
