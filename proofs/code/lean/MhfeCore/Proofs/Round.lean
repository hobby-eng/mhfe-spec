import MhfeCore.Code
import MhfeCore.Spec.Spec
import MhfeCore.Proofs.Models

/-!
# The round salt and the round mask in the code
-/

open Aeneas Aeneas.Std RustM mhfe_core

namespace MhfeProofs

/-- `round_salt` writes `Trunc_128(BLAKE2b-256(DS_SALT || message))` into the salt. -/
theorem round_salt_spec (g : feistel.Geometry) (msg : Slice Std.U8) (salt : Array Std.U8 16#usize) :
    feistel.round_salt g msg salt ⦃ s =>
      s.val = (MhfeModel.blake2b256 (g.ds_salt.val ++ msg.val)).val.take 16 ⦄ := by
  unfold feistel.round_salt
  simp only [blake2_1.Blake2b.new, blake2_1.Blake2b.chain_update, blake2_1.Blake2b.finalize,
    Shared0T.Insts.CoreConvertAsRef.as_ref, Slice.Insts.CoreConvertAsRefSlice.as_ref, bind_tc_ok]
  step*
  all_goals simp_all [engine.SALT_BYTES, List.slice, Array.from_slice_val]

/-- The HMAC key block of `round_mask`: the 32-byte key in a block of 64 zero bytes. -/
theorem key_block (k : List Std.U8) (hk : k.length = 32) :
    (List.replicate 64 (0#u8)).setSlice! 0 k = k ++ List.replicate 32 (0#u8) := by
  simp [List.setSlice!, hk, List.drop_replicate]

/-- `round_mask` writes `Trunc_h(HMAC-SHA-256(K, DS_MASK || message))` into the mask, `h` being
the mask's length (at most 32 bytes). The key enters HMAC as `K` padded with zeros to the 64-byte
block, which RFC 2104 defines to be the same key. -/
theorem round_mask_spec (g : feistel.Geometry) (key : Array Std.U8 32#usize) (msg mask : Slice Std.U8)
    (h : mask.length ≤ 32) :
    feistel.round_mask g key msg mask ⦃ m =>
      m.val = (MhfeModel.hmacSha256 (key.val ++ List.replicate 32 0#u8)
        (g.ds_mask.val ++ msg.val)).val.take mask.length ⦄ := by
  unfold feistel.round_mask
  simp only [hmac.Hmac.Insts.HmacKeyInit.new, hmac.Hmac.update, hmac.Hmac.finalize,
    hmac.CtOutput.into_bytes]
  have e := key_block key.val (by simp)
  step*
  all_goals simp_all [engine.KEY_BYTES, List.slice]

end MhfeProofs
