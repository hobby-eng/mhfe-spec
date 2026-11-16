-- long: The width-parametric oracle model, its actual forward/inverse paths and their probability laws form one proof foundation.
import MhfeLean.Chapters.WalletSource

namespace MhfeLean
noncomputable section

/-! # Deniability's common model for suites 3 and 4

Only the Feistel branch width varies. Salts stay128bits and Argon2 keys256bits.
This is a deliberate parameterization of Gamma2Model's basic oracle executor:
the remaining suite3 guessing proofs retain their original fixed-width model.
-/

namespace DeniabilityModel
open ProbabilityTools
variable {width : Nat} {Password Entropy Result Output : Type}

abbrev Branch (width : Nat) := BitVec width
abbrev State (width : Nat) := Lemma1.State width
abbrev Salt := BitVec 128
abbrev Key := BitVec 256
abbrev Hash := BitVec 256

inductive Point (width : Nat) (Password Entropy : Type)
  | a (password : Password) (salt : Salt)
  | b (round : Fin 12) (right : Branch width)
  | h (key : Key) (round : Fin 12) (right : Branch width)
  | g (entropy : Entropy)
  deriving DecidableEq

@[reducible] def spec (width : Nat) (Password Entropy : Type) : OracleSpec (Point width Password Entropy)
  | .a _ _ => Key
  | .b _ _ => Salt
  | .h _ _ _ => Branch width
  | .g _ => Hash

abbrev ATable (Password : Type) := Password × Salt → Key
abbrev BTable (width : Nat) := Fin 12 × Branch width → Salt
abbrev HInput (width : Nat) := Key × Fin 12 × Branch width
abbrev HTable (width : Nat) := HInput width → Branch width
abbrev GTable (Entropy : Type) := Entropy → Hash

structure Tables (width : Nat) (Password Entropy : Type) where
  a : ATable Password
  b : BTable width
  h : HTable width
  g : GTable Entropy

def answer (tables : Tables width Password Entropy) : (point : Point width Password Entropy) → spec width Password Entropy point
  | .a password salt => tables.a (password,salt)
  | .b round right => tables.b (round,right)
  | .h key round right => tables.h (key,round,right)
  | .g entropy => tables.g entropy

def execute (tables : Tables width Password Entropy) (program : OracleComp (spec width Password Entropy) Result) :=
  TranscriptErasure.execute (answer tables) program

def ask (point : Point width Password Entropy) :
    OracleComp (spec width Password Entropy) (spec width Password Entropy point) :=
  TranscriptErasure.ask point

@[simp] theorem execute_pure (tables : Tables width Password Entropy) (result : Result) :
    execute tables (pure result)=(result,[]) := rfl

@[simp] theorem execute_ask (tables : Tables width Password Entropy) (point : Point width Password Entropy) :
    execute tables (ask point)=(answer tables point,[point]) := rfl

/-! Port to Lean 4.35: a typed `do` binding instantiates `execute` at the reduced answer type, which the
general law above does not match; these four instances state the same law at those types. -/
@[simp] theorem execute_ask_a (tables : Tables width Password Entropy) (password : Password) (salt : Salt) :
    @execute width Password Entropy Key tables (ask (.a password salt))=
      (tables.a (password,salt),[.a password salt]) := rfl

@[simp] theorem execute_ask_b (tables : Tables width Password Entropy) (round : Fin 12) (right : Branch width) :
    @execute width Password Entropy Salt tables (ask (.b round right))=
      (tables.b (round,right),[.b round right]) := rfl

@[simp] theorem execute_ask_h (tables : Tables width Password Entropy) (key : Key) (round : Fin 12)
    (right : Branch width) :
    @execute width Password Entropy (Branch width) tables (ask (.h key round right))=
      (tables.h (key,round,right),[.h key round right]) := rfl

@[simp] theorem execute_ask_g (tables : Tables width Password Entropy) (entropy : Entropy) :
    @execute width Password Entropy Hash tables (ask (.g entropy))=
      (tables.g entropy,[.g entropy]) := rfl

@[simp] theorem execute_bind (tables : Tables width Password Entropy)
    (program : OracleComp (spec width Password Entropy) Result)
    (next : Result → OracleComp (spec width Password Entropy) Output) :
    execute tables (program >>= next)=
      let first := execute tables program
      let second := execute tables (next first.1)
      (second.1,first.2++second.2) := TranscriptErasure.execute_bind _ _ _

/-- Forward and inverse keep both the source chain and the actual lookup transcript. -/
def forward (password : Password) : (fuel start : Nat) → State width → (start+fuel≤12) →
    OracleComp (spec width Password Entropy) (State width × List (Point width Password Entropy))
  | 0,_,state,_ => pure (state,[])
  | fuel+1,start,state,bound => do
    let index : Fin 12 := ⟨start,by omega⟩
    let salt : Salt ← ask (.b index state.2)
    let key : Key ← ask (.a password salt)
    let mask : Branch width ← ask (.h key index state.2)
    let rest ← forward password fuel (start+1) (state.2,state.1 ^^^ mask) (by omega)
    pure (rest.1,[.b index state.2,.a password salt,.h key index state.2]++rest.2)

def finalize (password : Password) : (fuel : Nat) → State width → (fuel≤12) →
    OracleComp (spec width Password Entropy) (State width × List (Point width Password Entropy))
  | 0,state,_ => pure (state,[])
  | fuel+1,state,bound => do
    let index : Fin 12 := ⟨fuel,by omega⟩
    let salt : Salt ← ask (.b index state.1)
    let key : Key ← ask (.a password salt)
    let mask : Branch width ← ask (.h key index state.1)
    let rest ← finalize password fuel (state.2 ^^^ mask,state.1) (by omega)
    pure (rest.1,[.b index state.1,.a password salt,.h key index state.1]++rest.2)

attribute [local irreducible] execute

variable (password : Password) (tables : Tables width Password Entropy)

/-- Expanding one forward round exposes its genuine B/A/H points and answers. -/
theorem forward_step (fuel start : Nat)
    (source : State width) (bound : start+(fuel+1)≤12) :
    execute tables (forward password (fuel+1) start source bound)=
      let index : Fin 12 := ⟨start,by omega⟩
      let salt := tables.b (index,source.2)
      let key := tables.a (password,salt)
      let mask := tables.h (key,index,source.2)
      let rest := execute tables (forward password fuel (start+1) (source.2,source.1 ^^^ mask) (by omega))
      ((rest.1.1,[.b index source.2,.a password salt,.h key index source.2]++rest.1.2),
        [.b index source.2,.a password salt,.h key index source.2]++rest.2) := by
  simp only [forward,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer,execute_pure,List.append_nil,List.cons_append,List.nil_append]

theorem finalize_step (fuel : Nat)
    (bound : fuel+1≤12) (container : State width) :
    execute tables (finalize password (fuel+1) container bound)=
      let index : Fin 12 := ⟨fuel,by omega⟩
      let salt := tables.b (index,container.1)
      let key := tables.a (password,salt)
      let mask := tables.h (key,index,container.1)
      let rest := execute tables (finalize password fuel (container.2 ^^^ mask,container.1) (by omega))
      ((rest.1.1,[.b index container.1,.a password salt,.h key index container.1]++rest.1.2),
        [.b index container.1,.a password salt,.h key index container.1]++rest.2) := by
  simp only [finalize,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,answer,execute_pure,List.append_nil,List.cons_append,List.nil_append]

def mask (password : Password) (a : ATable Password) (b : BTable width) (h : HTable width)
    (round : Fin 12) (right : Branch width) : Branch width := h (a (password,b (round,right)),round,right)

def masks (fuel start : Nat) (bound : start+fuel≤12) : List (Branch width → Branch width) :=
  List.ofFn (fun index : Fin fuel => mask password tables.a tables.b tables.h ⟨start+index.val,by omega⟩)

def cipher (password : Password) (a : ATable Password) (b : BTable width) (h : HTable width) :
    Equiv.Perm (State width) :=
  Theorem1Feistel.cipher (mask password a b h)

/-- The executor's increasing round indices give exactly the generic Feistel mask list. -/
theorem masks_step (fuel start : Nat)
    (bound : start+(fuel+1)≤12) :
    masks password tables (fuel+1) start bound=mask password tables.a tables.b tables.h ⟨start,by omega⟩ ::
      masks password tables fuel (start+1) (by omega) := by
  unfold masks
  rw [List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext index
  apply congrArg (mask password tables.a tables.b tables.h)
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

attribute [local irreducible] forward finalize Lemma1.encrypt Lemma1.decrypt

theorem forward_result (password : Password) (tables : Tables width Password Entropy)
    (fuel start : Nat) (source : State width) (bound : start+fuel≤12) :
    (execute tables (forward password fuel start source bound)).1.1=
      Lemma1.encrypt (masks password tables fuel start bound) source := by
  induction fuel generalizing start source with
  | zero => simp only [forward,execute_pure,masks,List.ofFn_zero,Lemma1.encrypt]
  | succ fuel ih =>
    rw [forward_step,masks_step]
    dsimp only
    rw [ih]
    simp only [Lemma1.encrypt]
    rfl

/-- The source ciphertext is the actual twelve-round balanced Feistel at branch width h. -/
theorem forward_cipher (password : Password) (tables : Tables width Password Entropy) (source : State width) :
    (execute tables (forward password 12 0 source (by omega))).1.1=
      cipher password tables.a tables.b tables.h source := by
  rw [forward_result]
  rfl

/-- Each source H coordinate has a fixed round/right suffix, so restricting the uniform H table is injective. -/
def input (keyAt : Fin 12 → Branch width → Key) (point : Fin 12 × Branch width) : HInput width :=
  (keyAt point.1 point.2,point.1,point.2)

theorem input_injective (keyAt : Fin 12 → Branch width → Key) : Function.Injective (input keyAt) := by
  intro first second equal
  exact congrArg Prod.snd equal

attribute [local instance] FiniteBits.fintype
abbrev Mask (width : Nat) := Branch width → Branch width
abbrev Rounds (width : Nat) := Fin 12 → Mask width

def curry : (Fin 12 × Branch width → Branch width) ≃ Rounds width where
  toFun table round right := table (round,right)
  invFun masks point := masks point.1 point.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem masks_uniform (keyAt : Fin 12 → Branch width → Key) :
    (PMF.uniformOfFintype (HTable width)).map (fun h round right => h (keyAt round right,round,right))=
      PMF.uniformOfFintype (Rounds width) := by
  calc
    _ = ((PMF.uniformOfFintype (HTable width)).map (fun table point => table (input keyAt point))).map curry :=
      (PMF.map_comp _ _ _).symm
    _ = (PMF.uniformOfFintype (Fin 12 × Branch width → Branch width)).map curry := by
      rw [UniformInjection.restriction _ (input_injective keyAt)]
    _ = _ := PMF.uniformOfFintype_map_of_bijective curry curry.bijective

/-- Two fresh rounds make the output uniform; the independent suffix preserves it. -/
theorem network_uniform (source : State width) :
    (PMF.uniformOfFintype (Rounds width)).map (fun masks => Lemma1.encrypt (List.ofFn masks) source)=
      PMF.uniformOfFintype (State width) :=
  Lemma3.rounds_uniform 10 source

/-- Uniformity is for the real A/B-derived round functions, even with repeated salts or keys. -/
theorem cipher_uniform (password : Password) (a : ATable Password) (b : BTable width)
    (source : State width) :
    (PMF.uniformOfFintype (HTable width)).map (fun h => cipher password a b h source)=
      PMF.uniformOfFintype (State width) := by
  have law := masks_uniform (fun round right => a (password,b (round,right)))
  calc
    _ = ((PMF.uniformOfFintype (HTable width)).map
        (fun h round right => h (a (password,b (round,right)),round,right))).map
        (fun masks => Lemma1.encrypt (List.ofFn masks) source) := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [law,network_uniform]

/-- The first-refusal mass depends on the actual state width, not on the salt width. -/
theorem state_card : Fintype.card (State width)=2^(2*width) := by
  have branch : Fintype.card (Branch width)=2^width := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Lemma3.bitEquivFin width)
  rw [Fintype.card_prod,branch,← Nat.pow_add,← two_mul]

variable (password : Password) (tables : Tables width Password Entropy)

/-- A final round appends at the high end of the source's increasing mask list. -/
theorem masks_back (fuel : Nat)
    (bound : fuel+1≤12) :
    masks password tables (fuel+1) 0 (by omega)=masks password tables fuel 0 (by omega)++
      [mask password tables.a tables.b tables.h ⟨fuel,by omega⟩] := by
  unfold masks
  rw [List.ofFn_succ_last]
  simp only [Fin.val_castSucc,Fin.val_last,Nat.zero_add]

theorem decrypt_append (first last : List (Branch width → Branch width)) (source : State width) :
    Lemma1.decrypt (first++last) source=
      Lemma1.decrypt first (Lemma1.decrypt last source) := by
  induction first generalizing source with
  | nil => simp only [List.nil_append,Lemma1.decrypt]
  | cons mask rest ih => simp only [List.cons_append,Lemma1.decrypt,ih]

/-- The actual inverse executor undoes exactly the source mask list. -/
theorem inverse_result (fuel : Nat)
    (container : State width) (bound : fuel≤12) :
    (execute tables (finalize password fuel container bound)).1.1=
      Lemma1.decrypt (masks password tables fuel 0 (by omega)) container := by
  induction fuel generalizing container with
  | zero => simp only [finalize,execute_pure,masks,List.ofFn_zero,Lemma1.decrypt]
  | succ fuel ih =>
    rw [finalize_step,masks_back password tables fuel bound, decrypt_append]
    dsimp only
    rw [ih]
    simp only [Lemma1.decrypt]
    rfl

theorem inverse_cipher (container : State width) :
    (execute tables (finalize password 12 container (by omega))).1.1=
      (cipher password tables.a tables.b tables.h).symm container := by
  rw [inverse_result]
  rfl

def isH : Point width Password Entropy → Bool | .h _ _ _ => true | _ => false

def hFor (round : Fin 12) : Point width Password Entropy → Bool
  | .h _ index _ => decide (round=index)
  | _ => false

def fallbackPoint : Point width Password Entropy := .b 0 0

/-- Every source round contributes exactly one H query, including repeated keys or salts. -/
theorem forward_h_total (fuel start : Nat) (source : State width) (bound : start+fuel≤12) :
    (execute tables (forward password fuel start source bound)).2.countP isH=fuel := by
  induction fuel generalizing start source with
  | zero => simp only [forward,execute_pure,List.countP_nil]
  | succ fuel ih =>
    rw [forward_step]
    simp only [List.countP_append,List.countP_cons,List.countP_nil,isH,Bool.false_eq_true,↓reduceIte,ih]
    omega

/-- The owner inverse performs exactly twelve H calls, independent of the branch width. -/
theorem inverse_h_total (fuel : Nat) (container : State width) (bound : fuel≤12) :
    (execute tables (finalize password fuel container bound)).2.countP isH=fuel := by
  induction fuel generalizing container with
  | zero => simp only [finalize,execute_pure,List.countP_nil]
  | succ fuel ih =>
    rw [finalize_step]
    simp only [List.countP_append,List.countP_cons,List.countP_nil,isH,Bool.false_eq_true,↓reduceIte,ih]
    omega

/-- A specified source round appears exactly once if it lies in the executed interval. -/
theorem forward_h_count (fuel start : Nat)
    (source : State width) (bound : start+fuel≤12) (round : Fin 12) :
    (execute tables (forward password fuel start source bound)).2.countP (hFor round)=
      if start≤round.val ∧ round.val<start+fuel then 1 else 0 := by
  induction fuel generalizing start source with
  | zero => simp only [forward,execute_pure,List.countP_nil,Nat.add_zero]; split_ifs <;> omega
  | succ fuel ih =>
    rw [forward_step]
    simp only [List.countP_append,List.countP_cons,List.countP_nil,hFor,Bool.false_eq_true,↓reduceIte,ih]
    simp only [Fin.ext_iff,decide_eq_true_eq]
    split_ifs <;> omega

/-- All A calls of recovery carry the one disclosed password. -/
theorem inverse_password (password other : Password) (tables : Tables width Password Entropy)
    (fuel : Nat) (container : State width) (bound : fuel≤12) (salt : Salt)
    (member : Point.a other salt ∈ (execute tables (finalize password fuel container bound)).2) :
    other=password := by
  induction fuel generalizing container with
  | zero => simp only [finalize,execute_pure,List.not_mem_nil] at member
  | succ fuel ih =>
    rw [finalize_step] at member
    dsimp only at member
    simp only [List.cons_append,List.nil_append,List.mem_cons] at member
    rcases member with impossible | same | impossible | rest
    · cases impossible
    · exact Point.a.inj same |>.1
    · cases impossible
    · exact ih _ (by omega) rest

abbrev HSpec (width : Nat) : OracleSpec (HInput width) := fun _ => Branch width

def hInput : Point width Password Entropy → Option (HInput width)
  | .h key round right => some (key,round,right)
  | _ => none

/-- Freeze private A/B/G values and delegate only real H inputs. -/
def focusQuery (row : Salt → Key) (b : BTable width) (g : GTable Entropy) :
    (point : Point width Unit Entropy) → OracleComp (HSpec width) (spec width Unit Entropy point)
  | .a _ salt => pure (row salt)
  | .b round right => pure (b (round,right))
  | .h key round right => TranscriptErasure.ask (key,round,right)
  | .g entropy => pure (g entropy)

def focusH (row : Salt → Key) (b : BTable width) (g : GTable Entropy)
    (program : OracleComp (spec width Unit Entropy) Result) :
    OracleComp (HSpec width) (Result × List (Point width Unit Entropy)) :=
  OracleComp.construct (fun result => pure (result,[])) (fun point _ recurse => do
    let answer ← focusQuery row b g point
    let rest ← recurse answer
    pure (rest.1,point::rest.2)) program

theorem focusQuery_execution (row : Salt → Key) (b : BTable width) (g : GTable Entropy)
    (h : HTable width) (point : Point width Unit Entropy) :
    TranscriptErasure.execute h (focusQuery row b g point)=
      (answer (⟨fun input => row input.2,b,h,g⟩ : Tables width Unit Entropy) point,(hInput point).toList) := by
  cases point <;> rfl

/-- Both the complete source trace and the selected-table H trace are preserved. -/
theorem focusH_execution (row : Salt → Key) (b : BTable width) (g : GTable Entropy)
    (h : HTable width) (program : OracleComp (spec width Unit Entropy) Result) :
    TranscriptErasure.execute h (focusH row b g program)=
      let actual := execute (⟨fun input => row input.2,b,h,g⟩ : Tables width Unit Entropy) program
      (actual,actual.2.filterMap hInput) := by
  induction program using OracleComp.inductionOn with
  | pure result => simp only [focusH,OracleComp.construct_pure,TranscriptErasure.execute_pure,execute_pure,List.filterMap_nil]
  | query_bind point next ih =>
    change TranscriptErasure.execute h (do
        let value ← focusQuery row b g point
        let rest ← focusH row b g (next value)
        pure (rest.1,point::rest.2))=
      let actual := execute (⟨fun input => row input.2,b,h,g⟩ : Tables width Unit Entropy) (ask point >>= next)
      (actual,actual.2.filterMap hInput)
    simp only [TranscriptErasure.execute_bind,TranscriptErasure.execute_pure,
      focusQuery_execution,ih,execute_bind,execute_ask, execute_ask_a, execute_ask_b, execute_ask_h, execute_ask_g,List.singleton_append,List.filterMap_cons]
    cases point <;> simp only [hInput,Option.toList_some,Option.toList_none,List.cons_append,List.nil_append,List.append_nil]

/-- Record and other public oracles remain separate from the parameterized crypto query space. -/
@[reducible] def combinedSpec {Domain : Type} (extra : OracleSpec Domain) : OracleSpec (Point width Password Entropy ⊕ Domain)
  | .inl point => spec width Password Entropy point
  | .inr point => extra point

def combinedAnswer {Domain : Type} (extra : OracleSpec Domain) (crypto : Tables width Password Entropy)
    (other : (point : Domain) → extra point) :
    (point : Point width Password Entropy ⊕ Domain) → combinedSpec extra point
  | .inl point => answer crypto point
  | .inr point => other point

inductive Resource | a | b | h | g deriving DecidableEq

def resource (target : Resource) : Point width Password Entropy → Bool
  | .a _ _ => decide (target=.a)
  | .b _ _ => decide (target=.b)
  | .h _ _ _ => decide (target=.h)
  | .g _ => decide (target=.g)

/-- The prepared-disclosure inverse has exactly12A,12B,12H and zero G calls at every width. -/
theorem inverse_resources (fuel : Nat)
    (container : State width) (bound : fuel≤12) (target : Resource) :
    (execute tables (finalize password fuel container bound)).2.countP (resource target)=
      if target=.g then 0 else fuel := by
  induction fuel generalizing container with
  | zero => simp only [finalize,execute_pure,List.countP_nil]; split_ifs <;> rfl
  | succ fuel ih =>
    rw [finalize_step]
    cases target <;> simp [resource,ih]

end DeniabilityModel

namespace DeniabilityPrivate
set_option maxRecDepth 2048
open DeniabilityModel ProbabilityTools
variable {width : Nat}
attribute [local instance] FiniteBits.fintype

attribute [local irreducible] Lemma1.encrypt

abbrev World (width : Nat) := (Salt → Key) × HTable width

def masks (b : (BTable width)) (world : (World width)) : Fin 12 → Branch width → Branch width :=
  fun round right => world.2 (world.1 (b (round, right)), round, right)

def cipher (b : (BTable width)) (source : (State width)) (world : (World width)) : (State width) :=
  Lemma1.encrypt (List.ofFn (masks b world)) source

/-- Private A values and H answers use the same forward executor as the known-pair model. -/
def crypto (b : (BTable width)) (world : (World width)) : (Tables width) Unit Unit :=
  ⟨fun point => world.1 point.2, b, world.2, fun _ => 0⟩

def chain (b : (BTable width)) (source : (State width)) (world : (World width)) :
    List ((Point width) Unit Unit) :=
  (execute (crypto b world) (DeniabilityModel.forward () 12 0 source (by omega))).2

/-- A round key is read from the real forward H query, not supplied independently. -/
def key (b : (BTable width)) (source : (State width)) (world : (World width)) (round : Fin 12) : Key :=
  match (chain b source world).getD (3*round.val+2) fallbackPoint with
  | .h key _ _ => key
  | _ => 0

/-- Relabeling private keys and undoing that label at H leaves the encryption path unchanged. -/
def relabel (label : Equiv.Perm Key) : Equiv.Perm (World width) where
  toFun world := (fun salt => label (world.1 salt), fun point => world.2 (label.symm point.1, point.2))
  invFun world := (fun salt => label.symm (world.1 salt), fun point => world.2 (label point.1, point.2))
  left_inv := by
    intro world
    apply Prod.ext
    · funext salt
      exact label.symm_apply_apply _
    · funext point
      simp only [Equiv.symm_apply_apply]
  right_inv := by
    intro world
    apply Prod.ext
    · funext salt
      exact label.apply_symm_apply _
    · funext point
      simp only [Equiv.apply_symm_apply]

theorem masks_relabel (label : Equiv.Perm Key) (b : (BTable width)) (world : (World width)) :
    masks b (relabel label world) = masks b world := by
  funext round right
  simp only [masks, relabel, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

theorem cipher_relabel (label : Equiv.Perm Key) (b : (BTable width)) (source : (State width))
    (world : (World width)) : cipher b source (relabel label world) = cipher b source world := by
  simp only [cipher, masks_relabel]

def relabelPoint (label : Equiv.Perm Key) : (Point width) Unit Unit → (Point width) Unit Unit
  | .h key round right => .h (label key) round right
  | point => point

attribute [local irreducible] DeniabilityModel.forward

/-- Every forward state is preserved and every H query carries its relabeled key. -/
theorem forward_relabel (label : Equiv.Perm Key) (b : (BTable width)) (world : (World width))
    (fuel start : Nat) (source : (State width)) (bound : start+fuel ≤ 12) :
    execute (crypto b (relabel label world)) (DeniabilityModel.forward () fuel start source bound) =
      let old := execute (crypto b world) (DeniabilityModel.forward () fuel start source bound)
      ((old.1.1, old.1.2.map (relabelPoint label)), old.2.map (relabelPoint label)) := by
  induction fuel generalizing start source with
  | zero => simp only [DeniabilityModel.forward, execute_pure, List.map_nil]
  | succ fuel ih =>
    rw [DeniabilityModel.forward_step, DeniabilityModel.forward_step]
    simp only [crypto, relabel, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
    simp only [crypto, relabel, Equiv.coe_fn_mk] at ih
    rw [ih]
    simp only [List.map_append, List.map_cons, List.map_nil, relabelPoint]

/-- The H position of every real round exists even if salts or keys repeat. -/
theorem h_block (b : (BTable width)) (world : (World width)) (fuel start : Nat)
    (source : (State width)) (bound : start+fuel ≤ 12) (index : Nat) (inside : index < fuel) :
    ∃ right : Branch width,
      (execute (crypto b world) (DeniabilityModel.forward () fuel start source bound)).2.getD
        (3*index+2) fallbackPoint =
          .h (world.1 (b (⟨start+index, by omega⟩,right))) ⟨start+index, by omega⟩ right := by
  induction fuel generalizing start source index with
  | zero => omega
  | succ fuel ih =>
    cases index with
    | zero =>
      refine ⟨source.2, ?_⟩
      rw [DeniabilityModel.forward_step]
      rfl
    | succ index =>
      let round : Fin 12 := ⟨start, by omega⟩
      let nextState : (State width) := (source.2, source.1 ^^^ world.2 (world.1 (b (round,source.2)),round,source.2))
      obtain ⟨right, atH⟩ := ih (start+1) nextState (by omega) index (by omega)
      have sameRound : start+1+index = start+(index+1) := by omega
      refine ⟨right, ?_⟩
      rw [DeniabilityModel.forward_step]
      have position : 3*(index+1)+2 = (3*index+2)+3 := by omega
      rw [position]
      simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
      (try simp only [sameRound] at atH ⊢)
      exact atH

theorem key_relabel (label : Equiv.Perm Key) (b : (BTable width)) (source : (State width))
    (world : (World width)) (round : Fin 12) :
    key b source (relabel label world) round = label (key b source world round) := by
  have path : chain b source (relabel label world) = (chain b source world).map (relabelPoint label) :=
    congrArg Prod.snd (forward_relabel label b world 12 0 source (by omega))
  obtain ⟨right, atH⟩ := h_block b world 12 0 source (by omega) round.val round.isLt
  change (chain b source world).getD (3*round.val+2) fallbackPoint = _ at atH
  have moved := List.getD_map (l := chain b source world) (d := fallbackPoint)
    (n := 3*round.val+2) (relabelPoint label)
  change ((chain b source world).map (relabelPoint label)).getD (3*round.val+2) fallbackPoint = _ at moved
  unfold key
  rw [path, moved, atH]
  rfl

/-- The private source program outputs exactly the cipher used in the security experiment. -/
theorem forward_cipher (b : (BTable width)) (source : (State width)) (world : (World width)) :
    (execute (crypto b world) (DeniabilityModel.forward () 12 0 source (by omega))).1.1 =
      cipher b source world := DeniabilityModel.forward_cipher () (crypto b world) source

-- Later probability arguments use the proved key identities, not expansion of twelve rounds.
attribute [local irreducible] key

/-- A private encryption hides even a fixed packed source; no uniform-source assumption is used here. -/
theorem cipher_uniform (b : (BTable width)) (source : (State width)) :
    (PMF.uniformOfFintype (World width)).map (cipher b source) = PMF.uniformOfFintype (State width) := by
  have fixed (row : Salt → Key) :
      (PMF.uniformOfFintype (HTable width)).map (fun h => cipher b source (row, h)) =
        PMF.uniformOfFintype (State width) := by
    have actual := DeniabilityModel.cipher_uniform () (fun point => row point.2) b source
    exact actual
  calc
    _ = (PMF.uniformOfFintype (Salt → Key)).bind fun row =>
        (PMF.uniformOfFintype (HTable width)).map (fun h => cipher b source (row, h)) := by
      rw [uniform_product]
      simp only [independentPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
    _ = (PMF.uniformOfFintype (Salt → Key)).bind (fun _ => PMF.uniformOfFintype (State width)) := by
      apply congrArg (fun next => (PMF.uniformOfFintype (Salt → Key)).bind next)
      funext row
      exact fixed row
    _ = _ := PMF.bind_const _ _

/-- Each real round key is uniform independently of the public ciphertext. Repeated salts are allowed. -/
theorem hidden_key (b : (BTable width)) (source : (State width)) (round : Fin 12) :
    (PMF.uniformOfFintype (World width)).map (fun world => (cipher b source world, key b source world round)) =
      independentPair (PMF.uniformOfFintype (State width)) (PMF.uniformOfFintype Key) := by
  classical
  let observe : (World width) → (State width) × Key := fun world => (cipher b source world, key b source world round)
  let distribution := (PMF.uniformOfFintype (World width)).map observe
  have natural (label : Equiv.Perm Key) (world : (World width)) :
      observe (relabel label world) =
        Equiv.prodCongr (Equiv.refl (State width)) label (observe world) := by
    apply Prod.ext
    · exact cipher_relabel label b source world
    · exact key_relabel label b source world round
  have invariant (label : Equiv.Perm Key) :
      distribution.map (Equiv.prodCongr (Equiv.refl (State width)) label) = distribution := by
    exact UniformSymmetry.equivariant_uniform observe (relabel label)
      (Equiv.prodCongr (Equiv.refl (State width)) label) (natural label)
  have transitive : ∀ first second : Key, ∃ label : Equiv.Perm Key, label first = second := by
    intro first second
    exact ⟨Equiv.swap first second, Equiv.swap_apply_left first second⟩
  have joint := FiberSymmetry.independent_uniform distribution
    (fun label : Equiv.Perm Key => label) transitive invariant
  have marginal : distribution.map Prod.fst = PMF.uniformOfFintype (State width) := by
    simpa only [distribution, PMF.map_comp, Function.comp_def, observe] using cipher_uniform b source
  rw [marginal] at joint
  exact joint

end DeniabilityPrivate

namespace DeniabilityPrivateOracle
open DeniabilityModel DeniabilityPrivate
variable {width : Nat}
attribute [local instance] FiniteBits.fintype

abbrev SourceResult (width : Nat) :=
  (State width × List (Point width Unit Unit)) × List (Point width Unit Unit)

/-- This is the actual forward program with its private row frozen and only H delegated. -/
def sourceProgram (row : Salt → Key) (b : BTable width) (source : State width) :
    OracleComp (HSpec width) (SourceResult width) :=
  focusH row b (fun _ : Unit => 0) (forward () 12 0 source (by omega))

attribute [local irreducible] DeniabilityModel.forward DeniabilityModel.execute
  TranscriptErasure.execute

variable (row : Salt → Key) (b : BTable width) (source : State width) (h : HTable width)

theorem source_result :
    (TranscriptErasure.execute h (sourceProgram row b source)).1=
      execute (crypto b (row,h)) (forward () 12 0 source (by omega)) :=
  congrArg Prod.fst (focusH_execution row b (fun _ : Unit => 0) h (forward () 12 0 source (by omega)))

theorem source_trace :
    (TranscriptErasure.execute h (sourceProgram row b source)).2=
      (chain b source (row,h)).filterMap hInput :=
  congrArg Prod.snd (focusH_execution row b (fun _ : Unit => 0) h (forward () 12 0 source (by omega)))

/-- Exactly twelve genuine H inputs are touched, independently of all width choices. -/
theorem source_calls : (TranscriptErasure.execute h (sourceProgram row b source)).2.length=12 := by
  have count (points : List (Point width Unit Unit)) :
      (points.filterMap hInput).length=points.countP isH := by
    rw [List.length_filterMap_eq_countP]
    congr 1
    funext point
    cases point <;> rfl
  rw [source_trace,count]
  exact forward_h_total () (crypto b (row,h)) 12 0 source (by omega)

/-- Exact selective erasure preserves the source transcript and gives a fresh independent public H. -/
theorem erase_source {Output : Type} (row : Salt → Key) (b : BTable width) (source : State width)
    (observe : (SourceResult width × List (HInput width)) → HTable width → PMF Output) :
    (PMF.uniformOfFintype (HTable width × HTable width)).bind (fun seed =>
      observe (TranscriptErasure.execute seed.1 (sourceProgram row b source))
        (TranscriptErasure.exchanged (sourceProgram row b source) seed).2)=
    (PMF.uniformOfFintype (HTable width × HTable width)).bind (fun seed =>
      observe (TranscriptErasure.execute seed.1 (sourceProgram row b source)) seed.2) := by
  have exactLaw := TranscriptErasure.erased_distribution (sourceProgram row b source) observe
  have integrated := congrArg (fun law : PMF (PMF Output) => law.bind id) exactLaw
  (try simp only [PMF.bind_map,Function.comp_def] at integrated ⊢)
  exact integrated

end DeniabilityPrivateOracle

end
end MhfeLean
