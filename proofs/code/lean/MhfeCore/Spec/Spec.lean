import Aeneas

/-!
# The MHFE algorithm at the level of bytes

This file restates, from the text of the specification (`mhfe_spec` `98620cc`, README.md, sections
"Suite parameters", "Permutation", "Work factor" and "Suite 4"), the computation that the code of
`mhfe_core` must perform. It is written from the text, not from the code: the theorems about the
extracted code compare the code with these definitions.

Hash functions and Argon2id are parameters: every statement holds for every choice of them.
-/

open Aeneas Aeneas.Std

namespace MhfeSpec

abbrev Bytes := List U8

/-- The byte with value `n mod 256`. -/
def byte (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩

/-- `BE32(n)`: the 32-bit big-endian encoding of `n mod 2^32`. -/
def be32 (n : Nat) : Bytes := [byte (n / 2 ^ 24), byte (n / 2 ^ 16), byte (n / 2 ^ 8), byte n]

/-- The bytes of an ASCII string. -/
def ascii (s : String) : Bytes := s.toUTF8.toList.map fun b => ⟨b.toBitVec⟩

/-! ## Suite parameters -/

/-- The two suites. -/
inductive Suite
  | three
  | four
  deriving DecidableEq

def Suite.id : Suite → Bytes
  | .three => ascii "MHFE-BIP39-256-EXPERIMENTAL-3"
  | .four => ascii "MHFE-BIP39-LP-EXPERIMENTAL-4"

/-- `DS_SALT = SUITE_ID || ASCII("/ROUND-SALT")`, without a terminating NUL. -/
def Suite.dsSalt (s : Suite) : Bytes := s.id ++ ascii "/ROUND-SALT"

/-- `DS_MASK = SUITE_ID || ASCII("/ROUND-MASK")`. -/
def Suite.dsMask (s : Suite) : Bytes := s.id ++ ascii "/ROUND-MASK"

/-- Twelve rounds in each direction. -/
def rounds : Nat := 12

/-- The phrase lengths, and the entropy bytes `ENT/8` of a phrase of `words` words. -/
def wordCounts : List Nat := [12, 15, 18, 21, 24]
def shortWordCounts : List Nat := [12, 15, 18, 21]
def entropyBytes (words : Nat) : Nat := words / 3 * 4

/-- The bytes of one half: 16 in suite 3; `h/8 = ENT/16` in suite 4. -/
def Suite.halfBytes : Suite → Nat → Nat
  | .three, _ => 16
  | .four, words => entropyBytes words / 2

/-- `ENT` in the round message of suite 4; suite 3 has none. -/
def Suite.ent : Suite → Nat → Option Nat
  | .three, _ => none
  | .four, words => some (8 * entropyBytes words)

/-- The suite of a container of `words` words in the recovery workflow (S4-6). -/
def suiteOfContainer (words : Nat) : Option Suite :=
  if words = 24 then some .three
  else if words ∈ shortWordCounts then some .four
  else none

/-! ## Work factor -/

def maxPim : Nat := 1023
def maxMemoryLevel : Nat := 21

/-- `t(PIM) = 12 (PIM + 1)`. -/
def passes (pim : Nat) : Nat := 12 * (pim + 1)

/-- `m(MEM) = (2 + MEM mod 2) 2^(20 + floor(MEM / 2))` KiB. -/
def memoryKiB (mem : Nat) : Nat := (2 + mem % 2) * 2 ^ (20 + mem / 2)

/-! ## Round function -/

/-- The message that follows the domain string in `D_i` and `D'_i`:
`BE32(MEM) || BE32(PIM) || [BE32(ENT)] || BE32(i) || R`. -/
def message (mem pim : Nat) (ent : Option Nat) (i : Nat) (r : Bytes) : Bytes :=
  be32 mem ++ be32 pim ++ (match ent with | some e => be32 e | none => []) ++ be32 i ++ r

/-- The primitives the round function calls. `argon2id password salt memoryKiB passes` is the
32-byte tag of Argon2id version 0x13 with four lanes, an empty secret and empty associated data. -/
structure Primitives where
  blake2b256 : Bytes → Bytes
  hmacSha256 : (key : Bytes) → (message : Bytes) → Bytes
  argon2id : (password salt : Bytes) → (memoryKiB passes : Nat) → Bytes

/-- `S_i = Trunc_128(BLAKE2b-256(DS_SALT || message))`. -/
def roundSalt (F : Primitives) (s : Suite) (msg : Bytes) : Bytes :=
  (F.blake2b256 (s.dsSalt ++ msg)).take 16

/-- `M_i = Trunc_h(HMAC-SHA-256(K_i, DS_MASK || message))`. -/
def roundMaskOfKey (F : Primitives) (s : Suite) (h : Nat) (key msg : Bytes) : Bytes :=
  (F.hmacSha256 key (s.dsMask ++ msg)).take h

/-- The settings of one permutation. -/
structure Setting where
  suite : Suite
  words : Nat
  pim : Nat
  mem : Nat
  password : Bytes

def Setting.half (c : Setting) : Nat := c.suite.halfBytes c.words

/-- `RoundMask(i, R)`, with the Argon2id of the setting's work factor. -/
def roundMask (F : Primitives) (c : Setting) (i : Nat) (r : Bytes) : Bytes :=
  let msg := message c.mem c.pim (c.suite.ent c.words) i r
  let key := F.argon2id c.password (roundSalt F c.suite msg) (memoryKiB c.mem) (passes c.pim)
  roundMaskOfKey F c.suite c.half key msg

/-! ## The permutation -/

def xorBytes (a b : Bytes) : Bytes := List.zipWith (· ^^^ ·) a b

/-- One forward round: `L_{i+1} = R_i`, `R_{i+1} = L_i XOR M_i(R_i)`. -/
def forwardRound (m : Bytes → Bytes) (st : Bytes × Bytes) : Bytes × Bytes :=
  (st.2, xorBytes st.1 (m st.2))

/-- One inverse round: `R_i = L_{i+1}`, `L_i = R_{i+1} XOR M_i(R_i)`. -/
def backwardRound (m : Bytes → Bytes) (st : Bytes × Bytes) : Bytes × Bytes :=
  (xorBytes st.2 (m st.1), st.1)

/-- Rounds `0, ..., n-1` forward. -/
def forwardRounds (m : Nat → Bytes → Bytes) : Nat → Bytes × Bytes → Bytes × Bytes
  | 0, st => st
  | n + 1, st => forwardRound (m n) (forwardRounds m n st)

/-- Rounds `n-1, ..., 0` backward. -/
def backwardRounds (m : Nat → Bytes → Bytes) : Nat → Bytes × Bytes → Bytes × Bytes
  | 0, st => st
  | n + 1, st => backwardRounds m n (backwardRound (m n) st)

/-- `Y = Perm(X)`: `L_0 = X[0:h]`, `R_0 = X[h:2h]`, twelve rounds, `Y = L_12 || R_12`. -/
def perm (F : Primitives) (c : Setting) (x : Bytes) : Bytes :=
  let st := forwardRounds (roundMask F c) rounds (x.take c.half, x.drop c.half)
  st.1 ++ st.2

/-- `X = Perm^-1(Y)`. -/
def permInv (F : Primitives) (c : Setting) (y : Bytes) : Bytes :=
  let st := backwardRounds (roundMask F c) rounds (y.take c.half, y.drop c.half)
  st.1 ++ st.2

/-! ## Packing (suite 3) -/

/-- The 32-byte state of suite 3. -/
def stateBytes : Nat := 32

/-- Packing step 2: `X = E || Trunc_r(SHA-256(E))` with `r = 256 - ENT`, or `X = E` when
`r = 0`. -/
def pack (sha256 : Bytes → Bytes) (e : Bytes) : Bytes :=
  if e.length < stateBytes then e ++ (sha256 e).take (stateBytes - e.length) else e

/-- Recovering step 3 for one layout: `X` parsed as `E || V_r` matches when all `r` verifier bits
are those of `E`. A 24-word layout has no verifier and always parses. Meant for states of
`stateBytes` bytes, the only ones it is applied to. -/
def layoutMatches (sha256 : Bytes → Bytes) (x : Bytes) (words : Nat) : Bool :=
  x.drop (entropyBytes words) == (sha256 (x.take (entropyBytes words))).take
    (stateBytes - entropyBytes words)

/-- The detected lengths: the short layouts that match, in ascending order. -/
def detected (sha256 : Bytes → Bytes) (x : Bytes) : List Nat :=
  shortWordCounts.filter fun w => layoutMatches sha256 x w

/-! ## The length rules of suite 3 ("Recovering a mnemonic")

Written bullet by bullet from the text. `none` is "give no reading". -/

/-- With no stated length: one match gives its reading; several give each reading and then the
24-word reading; none gives the 24-word reading. -/
def readingsWithoutLength (d : List Nat) : List Nat :=
  match d with
  | [] => [24]
  | [w] => [w]
  | _ => d ++ [24]

/-- With a stated length `n`: a matching `n` is used alone; 24 stated words give the short readings
first and then the 24-word reading (only the latter when nothing matches); a short `n` that does
not match continues as with no stated length when other lengths match, and gives no reading when
nothing matches. -/
def lengthRules (stated : Option Nat) (d : List Nat) : Option (List Nat) :=
  match stated with
  | none => some (readingsWithoutLength d)
  | some n =>
    if n ∈ d then some [n]
    else if n = 24 then some (d ++ [24])
    else if d = [] then none
    else some (readingsWithoutLength d)

/-! ## Admission of a stated length and suite (S4-7) -/

/-- A stated length admits a container of `containerWords` words: it must be a phrase length, and
a short container admits only its own length. -/
def admitsLength (containerWords : Nat) (stated : Option Nat) : Prop :=
  match stated with
  | none => True
  | some n => n ∈ wordCounts ∧ (containerWords = 24 ∨ n = containerWords)

/-! ## The wallet check (MHFE-WALLET-CHECK-SEED-1) -/

/-- `T = SHA-256(ASCII("MHFE-WALLET-CHECK-SEED-1") || BE32(256) || seed)`; the phrase passes when
the first 16 bits of `T` are zero. -/
def walletCheckPasses (sha256 : Bytes → Bytes) (seed : Bytes) : Prop :=
  (sha256 (ascii "MHFE-WALLET-CHECK-SEED-1" ++ be32 256 ++ seed)).take 2 = [byte 0, byte 0]

end MhfeSpec
