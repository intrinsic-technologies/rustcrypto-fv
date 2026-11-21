import Sha2.Proofs.Common.SHA512.Mathematics.Padding.Split

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512
open Sha2.Proofs.NIST

def fullBlocks (input : ByteArray) : ByteArray := input.extract 0 (128 * (input.size / 128))

def remainderBytes (input : ByteArray) : ByteArray := input.extract (128 * (input.size / 128)) input.size

def paddingTail (input : ByteArray) : ByteArray :=
  remainderBytes input ++ ⟨#[128]⟩ ++ ⟨Array.replicate (paddingZeroBytes input) 0⟩ ++
    Encoding.natToOctets 16 (8 * input.size)

def tailFirst (input : ByteArray) : ByteArray :=
  if input.size % 128 < 112 then
    remainderBytes input ++ ⟨#[128]⟩ ++ ⟨Array.replicate (111 - input.size % 128) 0⟩ ++
      Encoding.natToOctets 16 (8 * input.size)
  else
    remainderBytes input ++ ⟨#[128]⟩ ++ ⟨Array.replicate (127 - input.size % 128) 0⟩

def tailLast (input : ByteArray) : ByteArray :=
  ⟨Array.replicate 112 0⟩ ++ Encoding.natToOctets 16 (8 * input.size)

theorem fullBlocks_size (input : ByteArray) : (fullBlocks input).size = 128 * (input.size / 128) := by
  simp only [fullBlocks, ByteArray.size_extract, Nat.sub_zero]
  exact Nat.min_eq_left (by omega)

theorem remainderBytes_size (input : ByteArray) : (remainderBytes input).size = input.size % 128 := by
  simp only [remainderBytes, ByteArray.size_extract, Nat.min_self]
  omega

theorem fullBlocks_append_remainderBytes (input : ByteArray) :
    fullBlocks input ++ remainderBytes input = input := by
  rw [fullBlocks, remainderBytes, ByteArray.extract_append_extract,
    Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right (show 128 * (input.size / 128) ≤ input.size by omega),
    ByteArray.extract_zero_size]

theorem bytePadding_eq_fullBlocks_append_tail (input : ByteArray) :
    bytePadding input = fullBlocks input ++ paddingTail input := by
  simp only [bytePadding, paddingTail, ← ByteArray.append_assoc]
  rw [fullBlocks_append_remainderBytes]

theorem paddingTail_eq (input : ByteArray) :
    paddingTail input = if input.size % 128 < 112 then tailFirst input else tailFirst input ++ tailLast input := by
  by_cases h : input.size % 128 < 112
  · have hz : paddingZeroBytes input = 111 - input.size % 128 := by unfold paddingZeroBytes; omega
    simp only [paddingTail, tailFirst, h, ↓reduceIte, hz]
  · have hz : paddingZeroBytes input = (127 - input.size % 128) + 112 := by unfold paddingZeroBytes; omega
    simp only [paddingTail, tailFirst, tailLast, h, ↓reduceIte, hz]
    have hzero : (⟨Array.replicate ((127 - input.size % 128) + 112) 0⟩ : ByteArray) =
        ⟨Array.replicate (127 - input.size % 128) 0⟩ ++ ⟨Array.replicate 112 0⟩ := by
      apply ByteArray.ext
      simp only [ByteArray.data_append, Array.replicate_append_replicate]
    rw [hzero]
    simp only [ByteArray.append_assoc]

theorem tailFirst_size (input : ByteArray) : (tailFirst input).size = 128 := by
  unfold tailFirst
  split
  · simp only [ByteArray.size_append, remainderBytes_size]
    simp only [ByteArray.size, Array.size_replicate, Encoding.natToOctets, Array.size_map, Array.size_range]
    change input.size % 128 + 1 + (111 - input.size % 128) + 16 = 128
    omega
  · simp only [ByteArray.size_append, remainderBytes_size]
    simp only [ByteArray.size, Array.size_replicate]
    change input.size % 128 + 1 + (127 - input.size % 128) = 128
    omega

theorem tailLast_size (input : ByteArray) : (tailLast input).size = 128 := by
  simp only [tailLast, ByteArray.size_append]
  simp only [ByteArray.size, Array.size_replicate, Encoding.natToOctets, Array.size_map, Array.size_range]

theorem compressBlocks_fullBlocks (hash : Array UInt64) (input : ByteArray) :
    compressBlocks hash (fullBlocks input) = compressBlocks hash input := by
  have hsize : (fullBlocks input).size / 128 = input.size / 128 := by
    rw [fullBlocks_size]
    omega
  have h := compressBlocksFrom_append_left hash (fullBlocks input) (remainderBytes input)
    0 (input.size / 128) (by rw [hsize]; omega)
  rw [fullBlocks_append_remainderBytes] at h
  unfold compressBlocks
  rw [hsize]
  exact h.symm

theorem compressBlocks_single (hash : Array UInt64) (input : ByteArray) (hsize : input.size = 128) :
    compressBlocks hash input = SHA512.compress hash (Encoding.octetsToBits input) := by
  unfold compressBlocks
  rw [hsize]
  change SHA512.compress hash (Encoding.octetsToBits (input.extract 0 128)) = _
  rw [← hsize, ByteArray.extract_zero_size]

theorem compressBlocks_bytePadding_eq (hash : Array UInt64) (input : ByteArray) :
    compressBlocks hash (bytePadding input) =
      let first := SHA512.compress (compressBlocks hash input) (Encoding.octetsToBits (tailFirst input))
      if input.size % 128 < 112 then first
      else SHA512.compress first (Encoding.octetsToBits (tailLast input)) := by
  rw [bytePadding_eq_fullBlocks_append_tail,
    compressBlocks_append hash (fullBlocks input) (paddingTail input)
      (by rw [fullBlocks_size]; omega), compressBlocks_fullBlocks, paddingTail_eq]
  split
  · rw [compressBlocks_single _ _ (tailFirst_size input)]
  · rw [compressBlocks_append _ _ _ (by rw [tailFirst_size]),
      compressBlocks_single _ _ (tailFirst_size input),
      compressBlocks_single _ _ (tailLast_size input)]

theorem serializeHash_tail_compressions (input : ByteArray) :
    serializeHash (if input.size % 128 < 112 then
      SHA512.compress (compressBlocks SHA512.initialHash input) (Encoding.octetsToBits (tailFirst input))
    else
      SHA512.compress
        (SHA512.compress (compressBlocks SHA512.initialHash input) (Encoding.octetsToBits (tailFirst input)))
        (Encoding.octetsToBits (tailLast input))) = SHA512.sha512 input := by
  rw [← compressBlocks_bytePadding_eq]
  exact serializeHash_compressBlocks_bytePadding input

theorem serializeHash_tail_compressions384 (input : ByteArray) :
    serializeHash ((if input.size % 128 < 112 then
      SHA512.compress (compressBlocks SHA512.initialHash384 input) (Encoding.octetsToBits (tailFirst input))
    else
      SHA512.compress
        (SHA512.compress (compressBlocks SHA512.initialHash384 input) (Encoding.octetsToBits (tailFirst input)))
        (Encoding.octetsToBits (tailLast input))).extract 0 6) = SHA512.sha384 input := by
  rw [← compressBlocks_bytePadding_eq]
  exact serializeHash_compressBlocks_bytePadding384 input

end Sha2.Proofs.Common.SHA512
