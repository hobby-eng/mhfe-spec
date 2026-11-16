import MhfeCore.Proofs.Feistel

/-!
# The geometry of a permutation and the settings of the specification

`Geometry::of` gives the domain strings, the half size and the `ENT` of the specification's suite;
`Mhfe::permutation` makes a permutation with those settings.
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- The suite of the specification that a suite of the code stands for. -/
def specSuite : suite.Suite → MhfeSpec.Suite
  | .TwentyFourWords => .three
  | .SameLength => .four

theorem ds3_salt : suite.SUITE_3_DS_SALT.val = MhfeSpec.Suite.three.dsSalt := by
  unfold suite.SUITE_3_DS_SALT; decide +kernel

theorem ds3_mask : suite.SUITE_3_DS_MASK.val = MhfeSpec.Suite.three.dsMask := by
  unfold suite.SUITE_3_DS_MASK; decide +kernel

theorem ds4_salt : suite.SUITE_4_DS_SALT.val = MhfeSpec.Suite.four.dsSalt := by
  unfold suite.SUITE_4_DS_SALT; decide +kernel

theorem ds4_mask : suite.SUITE_4_DS_MASK.val = MhfeSpec.Suite.four.dsMask := by
  unfold suite.SUITE_4_DS_MASK; decide +kernel

/-- A geometry with the settings that the specification's suite `s` has for `words` words. -/
structure GeoSpec (g : feistel.Geometry) (s : MhfeSpec.Suite) (words : Nat) : Prop where
  ds_salt : g.ds_salt.val = s.dsSalt
  ds_mask : g.ds_mask.val = s.dsMask
  half : g.half_bytes.val = s.halfBytes words
  ent : g.entropy_bits.map (·.val) = s.ent words
  geo : GeoOk g

/-- `Geometry::of` gives the specification's settings for each phrase length. -/
theorem geometry_of_spec (s : suite.Suite) (words : Std.Usize)
    (hw : words.val ∈ MhfeSpec.wordCounts) :
    feistel.Geometry.of s words ⦃ g => GeoSpec g (specSuite s) words.val ⦄ := by
  have hw' : words.val = 12 ∨ words.val = 15 ∨ words.val = 18 ∨ words.val = 21 ∨
      words.val = 24 := by simpa [MhfeSpec.wordCounts] using hw
  cases s
  · unfold feistel.Geometry.of
    simp only [packing.STATE_BYTES]
    step*
    refine ⟨ds3_salt, ds3_mask, ?_, rfl, ?_⟩
    · simp [specSuite, MhfeSpec.Suite.halfBytes, *]
    · simp [GeoOk, *]
  · unfold feistel.Geometry.of packing.entropy_of_words
    have hcast : ∀ b : Std.Usize, b.val ≤ 32 → (UScalar.cast .U32 b).val = b.val := by
      intro b hb
      rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simp; omega)]
    step*
    · scalar_tac
    · rw [i1_post, hcast _ (by omega)]; scalar_tac
    · have hb : bytes.val ≤ 32 := by omega
      refine ⟨ds4_salt, ds4_mask, ?_, ?_, ?_⟩
      · simp only [specSuite, MhfeSpec.Suite.halfBytes, MhfeSpec.entropyBytes]; omega
      · simp only [specSuite, MhfeSpec.Suite.ent, MhfeSpec.entropyBytes, Option.map_some,
          Option.some.injEq]
        rw [i2_post, i1_post, hcast _ hb]; omega
      · simp only [GeoOk]; omega

/-- A work factor that `WorkFactor::new` accepts. -/
def WorkOk (w : suite.WorkFactor) : Prop :=
  w.memory_level.val ≤ MhfeSpec.maxMemoryLevel ∧ w.pim.val ≤ MhfeSpec.maxPim

/-- The settings of the specification for a permutation of the code. -/
def settingOf (s : suite.Suite) (words : Nat) (w : suite.WorkFactor) (pw : password.Password) :
    MhfeSpec.Setting where
  suite := specSuite s
  words := words
  pim := w.pim.val
  mem := w.memory_level.val
  password := secretBytes pw.encoded

/-- `Mhfe::permutation` makes a permutation with the specification's settings: the suite and the
phrase length it is given, the cipher's work factor and the password's bytes. -/
theorem permutation_spec {E : Type} (inst : engine.Argon2Engine E) (self : cipher.Mhfe E)
    (pw : password.Password) (s : suite.Suite) (words : Std.Usize)
    (hw : words.val ∈ MhfeSpec.wordCounts) (hwork : WorkOk self.work) (hpw : SecretOk pw.encoded) :
    cipher.Mhfe.permutation inst self pw s words ⦃ p back =>
      Matches p (settingOf s words.val self.work pw) ∧ p.engine = self.engine ∧
      ∀ p', back p' = { self with engine := p'.engine } ⦄ := by
  unfold cipher.Mhfe.permutation
  let* ⟨ g, hg ⟩ ← geometry_of_spec
  obtain ⟨h1, h2, h3, h4, h5⟩ := hg
  constructor
  · exact ⟨h1, h2, h3, h4, h5, rfl, rfl, hwork.1, hwork.2, hpw, rfl⟩
  · simp

end MhfeProofs
