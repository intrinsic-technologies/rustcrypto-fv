import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Split

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256
open Sha2.Proofs.NIST

def fullBlocks (input : ByteArray) : ByteArray := input.extract 0 (64 * (input.size / 64))

def remainderBytes (input : ByteArray) : ByteArray := input.extract (64 * (input.size / 64)) input.size

def paddingTail (input : ByteArray) : ByteArray :=
  remainderBytes input ++ ⟨#[128]⟩ ++ ⟨Array.replicate (paddingZeroBytes input) 0⟩ ++
    Encoding.natToOctets 8 (8 * input.size)

def tailFirst (input : ByteArray) : ByteArray :=
  if input.size % 64 < 56 then
    remainderBytes input ++ ⟨#[128]⟩ ++ ⟨Array.replicate (55 - input.size % 64) 0⟩ ++
      Encoding.natToOctets 8 (8 * input.size)
  else
    remainderBytes input ++ ⟨#[128]⟩ ++ ⟨Array.replicate (63 - input.size % 64) 0⟩

def tailLast (input : ByteArray) : ByteArray :=
  ⟨Array.replicate 56 0⟩ ++ Encoding.natToOctets 8 (8 * input.size)

theorem fullBlocks_size (input : ByteArray) : (fullBlocks input).size = 64 * (input.size / 64) := by
  simp only [fullBlocks, ByteArray.size_extract, Nat.sub_zero]
  exact Nat.min_eq_left (by omega)

theorem remainderBytes_size (input : ByteArray) : (remainderBytes input).size = input.size % 64 := by
  simp only [remainderBytes, ByteArray.size_extract, Nat.min_self]
  omega

theorem fullBlocks_append_remainderBytes (input : ByteArray) :
    fullBlocks input ++ remainderBytes input = input := by
  rw [fullBlocks, remainderBytes, ByteArray.extract_append_extract,
    Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right (show 64 * (input.size / 64) ≤ input.size by omega),
    ByteArray.extract_zero_size]

theorem bytePadding_eq_fullBlocks_append_tail (input : ByteArray) :
    bytePadding input = fullBlocks input ++ paddingTail input := by
  simp only [bytePadding, paddingTail, ← ByteArray.append_assoc]
  rw [fullBlocks_append_remainderBytes]

theorem paddingTail_eq (input : ByteArray) :
    paddingTail input = if input.size % 64 < 56 then tailFirst input else tailFirst input ++ tailLast input := by
  by_cases h : input.size % 64 < 56
  · have hz : paddingZeroBytes input = 55 - input.size % 64 := by unfold paddingZeroBytes; omega
    simp only [paddingTail, tailFirst, h, ↓reduceIte, hz]
  · have hz : paddingZeroBytes input = (63 - input.size % 64) + 56 := by unfold paddingZeroBytes; omega
    simp only [paddingTail, tailFirst, tailLast, h, ↓reduceIte, hz]
    have hzero : (⟨Array.replicate ((63 - input.size % 64) + 56) 0⟩ : ByteArray) =
        ⟨Array.replicate (63 - input.size % 64) 0⟩ ++ ⟨Array.replicate 56 0⟩ := by
      apply ByteArray.ext
      simp only [ByteArray.data_append, Array.replicate_append_replicate]
    rw [hzero]
    simp only [ByteArray.append_assoc]

theorem tailFirst_size (input : ByteArray) : (tailFirst input).size = 64 := by
  unfold tailFirst
  split
  · simp only [ByteArray.size_append, remainderBytes_size]
    simp only [ByteArray.size, Array.size_replicate, Encoding.natToOctets, Array.size_map, Array.size_range]
    change input.size % 64 + 1 + (55 - input.size % 64) + 8 = 64
    omega
  · simp only [ByteArray.size_append, remainderBytes_size]
    simp only [ByteArray.size, Array.size_replicate]
    change input.size % 64 + 1 + (63 - input.size % 64) = 64
    omega

theorem tailLast_size (input : ByteArray) : (tailLast input).size = 64 := by
  simp only [tailLast, ByteArray.size_append]
  simp only [ByteArray.size, Array.size_replicate, Encoding.natToOctets, Array.size_map, Array.size_range]

theorem compressBlocks_fullBlocks (hash : Array UInt32) (input : ByteArray) :
    compressBlocks hash (fullBlocks input) = compressBlocks hash input := by
  have hsize : (fullBlocks input).size / 64 = input.size / 64 := by
    rw [fullBlocks_size]
    omega
  have h := compressBlocksFrom_append_left hash (fullBlocks input) (remainderBytes input)
    0 (input.size / 64) (by rw [hsize]; omega)
  rw [fullBlocks_append_remainderBytes] at h
  unfold compressBlocks
  rw [hsize]
  exact h.symm

theorem compressBlocks_single (hash : Array UInt32) (input : ByteArray) (hsize : input.size = 64) :
    compressBlocks hash input = SHA256.compress hash (Encoding.octetsToBits input) := by
  unfold compressBlocks
  rw [hsize]
  change SHA256.compress hash (Encoding.octetsToBits (input.extract 0 64)) = _
  rw [← hsize, ByteArray.extract_zero_size]

theorem compressBlocks_bytePadding_eq (hash : Array UInt32) (input : ByteArray) :
    compressBlocks hash (bytePadding input) =
      let first := SHA256.compress (compressBlocks hash input) (Encoding.octetsToBits (tailFirst input))
      if input.size % 64 < 56 then first
      else SHA256.compress first (Encoding.octetsToBits (tailLast input)) := by
  rw [bytePadding_eq_fullBlocks_append_tail,
    compressBlocks_append hash (fullBlocks input) (paddingTail input)
      (by rw [fullBlocks_size]; omega), compressBlocks_fullBlocks, paddingTail_eq]
  split
  · rw [compressBlocks_single _ _ (tailFirst_size input)]
  · rw [compressBlocks_append _ _ _ (by rw [tailFirst_size]),
      compressBlocks_single _ _ (tailFirst_size input),
      compressBlocks_single _ _ (tailLast_size input)]

theorem serializeHash_tail_compressions (input : ByteArray) :
    serializeHash (if input.size % 64 < 56 then
      SHA256.compress (compressBlocks SHA256.initialHash input) (Encoding.octetsToBits (tailFirst input))
    else
      SHA256.compress
        (SHA256.compress (compressBlocks SHA256.initialHash input) (Encoding.octetsToBits (tailFirst input)))
        (Encoding.octetsToBits (tailLast input))) = SHA256.sha256 input := by
  rw [← compressBlocks_bytePadding_eq]
  exact serializeHash_compressBlocks_bytePadding input

theorem serializeHash_tail_compressions_truncated
    (initial : Array UInt32) (bytes : Nat) (input : ByteArray) :
    (serializeHash (if input.size % 64 < 56 then
      SHA256.compress (compressBlocks initial input) (Encoding.octetsToBits (tailFirst input))
    else
      SHA256.compress
        (SHA256.compress (compressBlocks initial input) (Encoding.octetsToBits (tailFirst input)))
        (Encoding.octetsToBits (tailLast input)))).extract 0 bytes =
      SHA256.truncatedBits initial bytes (Encoding.octetsToBits input) := by
  rw [← compressBlocks_bytePadding_eq]
  exact serializeHash_compressBlocks_bytePadding_truncated initial bytes input

end Sha2.Proofs.Common.SHA256
