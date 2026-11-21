import Sha2.Proofs.Wrapper512.State
import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Tail

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

open Sha2.Spec Sha2.Proofs.NIST
open Sha2.Proofs.Common.SHA512

def finalHashFull (v : Variant) (input : ByteArray) : Array UInt64 :=
  let hash := compressBlocks v.initialHash input
  let first := SHA512.compress hash (Encoding.octetsToBits (tailFirst input))
  if input.size % 128 < 112 then first
  else SHA512.compress first (Encoding.octetsToBits (tailLast input))

def finalHash (v : Variant) (input : ByteArray) : Array UInt64 :=
  match v with
  | .sha384 => (finalHashFull .sha384 input).extract 0 6
  | v => finalHashFull v input

theorem finalHashFull_size (v : Variant) (input : ByteArray) :
    (finalHashFull v input).size = 8 := by
  simp only [finalHashFull]
  split <;> rfl

theorem finalHash_size (v : Variant) (input : ByteArray) :
    (finalHash v input).size = if v = .sha384 then 6 else 8 := by
  cases v <;> simp [finalHash, finalHashFull_size]

theorem finalHash_sha384 (input : ByteArray) :
    serializeHash (finalHash .sha384 input) = NIST.SHA512.sha384 input := by
  simpa [finalHash, finalHashFull, Variant.initialHash] using
    (serializeHash_tail_compressions384 input)

theorem finalHash_sha512 (input : ByteArray) :
    serializeHash (finalHash .sha512 input) = NIST.SHA512.sha512 input := by
  simpa [finalHash, finalHashFull, Variant.initialHash] using
    (serializeHash_tail_compressions input)

theorem truncatedBits_compressBlocks_bytePadding (initial : Array UInt64) (n : Nat)
    (input : ByteArray) :
    (serializeHash (compressBlocks initial (bytePadding input))).extract 0 n =
      SHA512.truncatedBits initial n (Encoding.octetsToBits input) := by
  unfold SHA512.truncatedBits
  rw [← octetsToBits_bytePadding]
  simp only [octetsToBits_size, ← blockBits_eq_extract]
  have hsize : 8 * (bytePadding input).size / 1024 = (bytePadding input).size / 128 :=
    Nat.mul_div_mul_left (bytePadding input).size 128 (by decide : 0 < 8)
  simp only [hsize, compressBlocks, compressBlocksFrom_eq_foldl, List.range_eq_range']
  rfl

theorem finalHash_hash (v : Variant) (input : ByteArray) :
    v.serialize (finalHashFull v input) = v.hash input := by
  cases v with
  | sha384 => exact finalHash_sha384 input
  | sha512 => exact finalHash_sha512 input
  | sha512_224 =>
    change (serializeHash (finalHashFull .sha512_224 input)).extract 0 28 = _
    rw [finalHashFull, ← compressBlocks_bytePadding_eq]
    exact truncatedBits_compressBlocks_bytePadding _ _ _
  | sha512_256 =>
    change (serializeHash (finalHashFull .sha512_256 input)).extract 0 32 = _
    rw [finalHashFull, ← compressBlocks_bytePadding_eq]
    exact truncatedBits_compressBlocks_bytePadding _ _ _

theorem finalHashFull_sha512 (input : ByteArray) :
    serializeHash (finalHashFull .sha512 input) = NIST.SHA512.sha512 input := by
  simpa [finalHashFull, Variant.initialHash] using (serializeHash_tail_compressions input)

theorem compressBlocks_prefix (v : Variant) (a b : ByteArray)
    (ha : a.size % 128 = 0) :
    compressBlocks v.initialHash (a ++ b) =
      compressBlocks (compressBlocks v.initialHash a) b := by
  exact compressBlocks_append _ _ _ ha

theorem tailData_eq_remainder (input : ByteArray) :
    tailData input = remainderBytes input := by
  rfl

theorem finalHash_full_prefix (v : Variant) (input : ByteArray) :
    compressBlocks v.initialHash (fullBlocks input) = compressBlocks v.initialHash input := by
  exact compressBlocks_fullBlocks _ _

end Sha2.Proofs.Wrapper512
