import P256.Proofs.HMAC.Blocks
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec
open P256.Proofs.Program

theorem compressBlocks_append_buffer (hash : Array UInt32) (input added : ByteArray) :
    SHA256.compressBlocks hash (input ++ added) =
      SHA256.compressBlocks (SHA256.compressBlocks hash input)
        (SHA256.remainderBytes input ++ added) := by
  conv => lhs; rw [← SHA256.fullBlocks_append_remainderBytes input, ByteArray.append_assoc]
  rw [SHA256.compressBlocks_append _ _ _ (by rw [SHA256.fullBlocks_size]; omega),
    SHA256.compressBlocks_fullBlocks]

theorem remainderBytes_append_buffer (input added : ByteArray) :
    SHA256.remainderBytes (input ++ added) =
      SHA256.remainderBytes (SHA256.remainderBytes input ++ added) := by
  conv => lhs; rw [← SHA256.fullBlocks_append_remainderBytes input, ByteArray.append_assoc]
  exact HMAC.remainderBytes_append_aligned _ _ (by rw [SHA256.fullBlocks_size]; omega)

theorem compressBlocks_append_small (hash : Array UInt32) (input added : ByteArray)
    (fits : input.size % 64 + added.size < 64) :
    SHA256.compressBlocks hash (input ++ added) = SHA256.compressBlocks hash input := by
  rw [compressBlocks_append_buffer, HMAC.compressBlocks_short]
  rw [ByteArray.size_append, SHA256.remainderBytes_size]
  exact fits

theorem remainderBytes_append_small (input added : ByteArray)
    (fits : input.size % 64 + added.size < 64) :
    SHA256.remainderBytes (input ++ added) = SHA256.remainderBytes input ++ added := by
  rw [remainderBytes_append_buffer, HMAC.remainderBytes_short]
  rw [ByteArray.size_append, SHA256.remainderBytes_size]
  exact fits

theorem append_split_block (buffer added : ByteArray) (bufferBound : buffer.size ≤ 64)
    (crosses : 64 ≤ buffer.size + added.size) :
    buffer ++ added =
      (buffer ++ added.extract 0 (64 - buffer.size)) ++
        added.extract (64 - buffer.size) added.size := by
  rw [ByteArray.append_assoc, ByteArray.extract_append_extract,
    Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right (by omega),
    ByteArray.extract_zero_size]

theorem compressBlocks_append_crossing (hash : Array UInt32) (buffer added : ByteArray)
    (bufferBound : buffer.size ≤ 64) (crosses : 64 ≤ buffer.size + added.size)
    (oneBlock : buffer.size + added.size < 128) :
    SHA256.compressBlocks hash (buffer ++ added) =
      P256.Proofs.SHA256.Reference.compress hash
        (Standards.NIST.SHA2.bytesToBits (buffer ++ added.extract 0 (64 - buffer.size))) := by
  have blockSize : (buffer ++ added.extract 0 (64 - buffer.size)).size = 64 := by
    rw [ByteArray.size_append, ByteArray.size_extract, Nat.sub_zero,
      Nat.min_eq_left (by omega)]
    omega
  have tailSize : (added.extract (64 - buffer.size) added.size).size < 64 := by
    rw [ByteArray.size_extract, Nat.min_self]
    omega
  rw [append_split_block buffer added bufferBound crosses,
    SHA256.compressBlocks_append _ _ _ (by rw [blockSize]),
    HMAC.compressBlocks_short _ _ tailSize, SHA256.compressBlocks_single _ _ blockSize]

theorem remainderBytes_append_crossing (buffer added : ByteArray)
    (bufferBound : buffer.size ≤ 64) (crosses : 64 ≤ buffer.size + added.size)
    (oneBlock : buffer.size + added.size < 128) :
    SHA256.remainderBytes (buffer ++ added) =
      added.extract (64 - buffer.size) added.size := by
  have blockSize : (buffer ++ added.extract 0 (64 - buffer.size)).size = 64 := by
    rw [ByteArray.size_append, ByteArray.size_extract, Nat.sub_zero,
      Nat.min_eq_left (by omega)]
    omega
  have tailSize : (added.extract (64 - buffer.size) added.size).size < 64 := by
    rw [ByteArray.size_extract, Nat.min_self]
    omega
  rw [append_split_block buffer added bufferBound crosses,
    HMAC.remainderBytes_append_aligned _ _ (by rw [blockSize]),
    HMAC.remainderBytes_short _ tailSize]

end P256.Proofs.Nonce.Update.Absorb
