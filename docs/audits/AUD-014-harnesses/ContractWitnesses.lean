import MhfeCore

open Aeneas Aeneas.Std RustM mhfe_core MhfeProofs

namespace MhfeCodeAudit

/-- The intentionally always-error native placeholder meets the weaker generic correctness contract. -/
theorem native_placeholder_computes_any
    (A : List Std.U8 → List Std.U8 → Nat → Nat → Array Std.U8 32#usize) :
    EngineComputes engine.native.NativeArgon2.Insts.Mhfe_coreEngineArgon2Engine A := by
  intro st pw salt m t key
  simp [engine.native.NativeArgon2.Insts.Mhfe_coreEngineArgon2Engine,
    engine.native.NativeArgon2.Insts.Mhfe_coreEngineArgon2Engine.argon2id]

/-- Successful-return theorems cannot be specialized to that placeholder. -/
theorem native_placeholder_not_ok (pw : Slice Std.U8) (salt : Array Std.U8 16#usize)
    (key : Array Std.U8 32#usize) :
    ¬ EngineOk engine.native.NativeArgon2.Insts.Mhfe_coreEngineArgon2Engine := by
  intro hypothesis
  have impossible := hypothesis ⟨⟩ pw salt 0#u32 0#u32 key
  simpa [engine.native.NativeArgon2.Insts.Mhfe_coreEngineArgon2Engine,
    engine.native.NativeArgon2.Insts.Mhfe_coreEngineArgon2Engine.argon2id] using impossible

end MhfeCodeAudit
