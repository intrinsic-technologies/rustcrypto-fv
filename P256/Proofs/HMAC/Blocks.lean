import P256.Proofs.HMAC.Mathematics
import P256.Proofs.SHA256.Mathematics.Padding

set_option autoImplicit false

namespace P256.Proofs.HMAC

open P256.Spec

theorem compressBlocks_keyPad (key : ByteArray) (pad : UInt8) (hash : Array UInt32) :
    SHA256.compressBlocks hash (keyPad key pad) =
      SHA256.Reference.compress hash (Standards.NIST.SHA2.bytesToBits (keyPad key pad)) :=
  SHA256.compressBlocks_single hash _ (keyPad_size key pad)

theorem compressBlocks_keyPad_append (key input : ByteArray) (pad : UInt8)
    (hash : Array UInt32) :
    SHA256.compressBlocks hash (keyPad key pad ++ input) =
      SHA256.compressBlocks
        (SHA256.Reference.compress hash (Standards.NIST.SHA2.bytesToBits (keyPad key pad))) input := by
  rw [SHA256.compressBlocks_append _ _ _ (by rw [keyPad_size]), compressBlocks_keyPad]

theorem compressBlocks_short (hash : Array UInt32) (input : ByteArray) (hi : input.size < 64) :
    SHA256.compressBlocks hash input = hash := by
  simp only [SHA256.compressBlocks, Nat.div_eq_of_lt hi, SHA256.compressBlocksFrom]

theorem remainderBytes_append_aligned (preludeBytes input : ByteArray) (hp : preludeBytes.size % 64 = 0) :
    SHA256.remainderBytes (preludeBytes ++ input) = SHA256.remainderBytes input := by
  have he : 64 * ((preludeBytes ++ input).size / 64) = preludeBytes.size + 64 * (input.size / 64) := by
    rw [ByteArray.size_append]
    omega
  unfold SHA256.remainderBytes
  rw [he, ByteArray.size_append, ByteArray.extract_append_size_add]

theorem remainderBytes_short (input : ByteArray) (hi : input.size < 64) :
    SHA256.remainderBytes input = input := by
  simp only [SHA256.remainderBytes, Nat.div_eq_of_lt hi, Nat.mul_zero, ByteArray.extract_zero_size]

theorem remainderBytes_keyPad_append (key input : ByteArray) (pad : UInt8) :
    SHA256.remainderBytes (keyPad key pad ++ input) = SHA256.remainderBytes input :=
  remainderBytes_append_aligned _ _ (by rw [keyPad_size])

theorem serializeHash_inner_tail (key input : ByteArray)
    (hi : input.size = 32 ∨ input.size = 33 ∨ input.size = 97) :
    SHA256.serializeHash
      (SHA256.Reference.compress (SHA256.compressBlocks SHA256.initialHash (keyPad key 0x36 ++ input))
        (Standards.NIST.SHA2.bytesToBits (SHA256.tailFirst (keyPad key 0x36 ++ input)))) =
      Operations.hash (keyPad key 0x36 ++ input) := by
  have h := SHA256.serializeHash_tail_compressions (keyPad key 0x36 ++ input)
  simpa only [inner_remainder_lt key input hi, ↓reduceIte] using h

theorem compressBlocksFrom_size (hash : Array UInt32) (input : ByteArray)
    (start count : Nat) (hh : hash.size = 8) :
    (SHA256.compressBlocksFrom hash input start count).size = 8 := by
  induction count generalizing hash start with
  | zero => exact hh
  | succ count ih =>
    exact ih _ _ (by
      simp only [SHA256.Reference.compress, Array.size_map, Vector.size_toArray])

end P256.Proofs.HMAC
