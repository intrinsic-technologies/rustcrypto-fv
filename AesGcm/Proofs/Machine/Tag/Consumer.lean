import AesGcm.Proofs.Machine.Tag.Hash
import AesGcm.Proofs.Machine.Tag.Padding
import AesGcm.Proofs.Machine.Tag.Model
import X86Proofs.Program.ReadWrite.Bytes

namespace AesGcm.Proofs.Machine.Tag

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.GHASH AesGcm.Proofs.Machine.GHASHInterface

theorem sourceBlockBits_getElem (mem : Ram) (src : BitVec 64) (j i : Nat) (hi : i < 128) :
    (sourceBlockBits mem src j)[i] =
      (memByte mem (src + BitVec.ofNat 64 (16 * j + i / 8))).toNat.testBit (7 - i % 8) := by
  have hload (base : BitVec 64) (k : Nat) (hk : k < 64) :
      (memLoad mem base 64).getLsbD k =
        (memByte mem (base + BitVec.ofNat 64 (k / 8))).toNat.testBit (k % 8) := by
    have hb := congrArg (fun b : UInt8 ↦ b.toNat.testBit (k % 8))
      (storedByte_memLoad mem base (n := 64) (k / 8) (by omega))
    simpa only [storedByte_eq_extract, UInt8.toNat, BitVec.testBit_toNat, BitVec.getLsbD_extractLsb',
      show k % 8 < 8 by omega, decide_true, Bool.true_and,
      show 8 * (k / 8) + k % 8 = k by omega] using hb
  simp only [sourceBlockBits, stateBits, toGcmBits, Vector.getElem_ofFn,
    BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : i < 64
  · rw [ite_eq_right (by omega)]
    rw [bswapSpec, getLsbD_ofLanes _ _ (by omega)]
    simp only [lane, Nat.reduceDiv, Nat.reduceSub, BitVec.getLsbD_extractLsb',
      show (128 - 1 - i - 64) % 8 < 8 by omega, decide_true, Bool.true_and,
      show 128 - 1 - i - 64 < 8 * 8 by omega, ite_true]
    rw [hload _ _ (by omega)]
    have hd : ((7 - (128 - 1 - i - 64) / 8) * 8 + (128 - 1 - i - 64) % 8) / 8 = i / 8 := by omega
    have hm : ((7 - (128 - 1 - i - 64) / 8) * 8 + (128 - 1 - i - 64) % 8) % 8 = 7 - i % 8 := by omega
    simp only [hd, hm, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [ite_eq_left (by omega)]
    rw [bswapSpec, getLsbD_ofLanes _ _ (by omega)]
    simp only [lane, Nat.reduceDiv, Nat.reduceSub, BitVec.getLsbD_extractLsb',
      show (128 - 1 - i) % 8 < 8 by omega, decide_true, Bool.true_and,
      show 128 - 1 - i < 8 * 8 by omega, ite_true]
    rw [hload _ _ (by omega)]
    have hd : ((7 - (128 - 1 - i) / 8) * 8 + (128 - 1 - i) % 8) / 8 + 8 = i / 8 := by omega
    have hm : ((7 - (128 - 1 - i) / 8) * 8 + (128 - 1 - i) % 8) % 8 = 7 - i % 8 := by omega
    simp only [hm, BitVec.add_assoc, ← BitVec.ofNat_add]
    have ha : 16 * j + 8 + ((7 - (128 - 1 - i) / 8) * 8 +
        (128 - 1 - i) % 8) / 8 = 16 * j + i / 8 := by omega
    rw [ha]

theorem sourceBlockBits_eq_paddedBlock (mem : Ram) (src : BitVec 64)
    (bytes : ByteArray) (j : Nat) (hj : j < bytes.size / 16)
    (hbytes : (Runtime.span src bytes.size).HasBytes mem bytes) :
    sourceBlockBits mem src j = paddedBlock bytes j := by
  apply Vector.ext
  intro i hi
  rw [sourceBlockBits_getElem]
  have hindex : 16 * j + i / 8 < bytes.size := by omega
  have hb := hbytes.2 ⟨16 * j + i / 8, hindex⟩
  simp only [Runtime.span, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
  simp only [paddedBlock, Vector.getElem_ofFn, hindex, dite_true, memByte,
    PhysicalMemory.read, BitVec.ofNat_add, hb, Option.getD_some]

def hashPadded (h : Vector UInt8 16) (bytes : ByteArray) (initial : Vector Bool 128) :
    Vector Bool 128 :=
  (paddedBlocks bytes).toList.foldl (fun acc x ↦ Standards.NIST.GCM.mul
    (Standards.NIST.GCM.xor acc x) (Standards.NIST.GCM.bitsOfBytes h)) initial

theorem authenticationTagFromMask_eq_hashPadded (h mask : Vector UInt8 16)
    (associatedData ciphertext : ByteArray) :
    authenticationTagFromMask h mask associatedData ciphertext =
      Standards.NIST.GCM.bytesOfBits (Standards.NIST.GCM.xor
        (Standards.NIST.GCM.mul (Standards.NIST.GCM.xor
          (hashPadded h ciphertext (hashPadded h associatedData (Standards.NIST.GCM.zeros 128)))
          (Standards.NIST.GCM.integerToString 64 (8 * associatedData.size) ++
            Standards.NIST.GCM.integerToString 64 (8 * ciphertext.size)))
          (Standards.NIST.GCM.bitsOfBytes h)) (Standards.NIST.GCM.bitsOfBytes mask)) := by
  dsimp only [authenticationTagFromMask]
  rw [blocks_authentication_input, ghash_eq_foldl]
  simp only [Array.toList_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, hashPadded, paddedBlocks]

theorem fullBlocks_toList (mem : Ram) (src : BitVec 64) (bytes : ByteArray)
    (hbytes : (Runtime.span src bytes.size).HasBytes mem bytes) :
    (Standards.NIST.GCM.blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes)).toList =
      (List.range (bytes.size / 16)).map (sourceBlockBits mem src) := by
  apply List.ext_getElem
  · simp only [Array.length_toList, fullBlocks_size, List.length_map, List.length_range]
  · intro i hi hi'
    have hib : i < bytes.size / 16 := by
      simpa only [Array.length_toList, fullBlocks_size] using hi
    simp only [Array.getElem_toList, List.getElem_map, List.getElem_range,
      fullBlocks_getElem, sourceBlockBits_eq_paddedBlock mem src bytes i hib hbytes]

theorem updateBlocks_full_bits (mem : Ram) (src : BitVec 64) (bytes : ByteArray)
    (h : Vector UInt8 16) (s : BitVec 64 × BitVec 64)
    (hbytes : (Runtime.span src bytes.size).HasBytes mem bytes) :
    let k := polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)
    stateBits (updateBlocks mem src (bytes.size / 16) k.1 k.2 s) =
      (Standards.NIST.GCM.blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes)).toList.foldl
        (fun acc x ↦ Standards.NIST.GCM.mul (Standards.NIST.GCM.xor acc x)
          (Standards.NIST.GCM.bitsOfBytes h)) (stateBits s) := by
  dsimp only
  rw [updateBlocks_bits, fullBlocks_toList mem src bytes hbytes, List.foldl_map]

theorem hashPadded_eq_full_tail (h : Vector UInt8 16) (bytes : ByteArray)
    (initial : Vector Bool 128) :
    hashPadded h bytes initial =
      let full := (Standards.NIST.GCM.blocks (AesGcm.Spec.GCM.bitsOfByteArray bytes)).toList.foldl
        (fun acc x ↦ Standards.NIST.GCM.mul (Standards.NIST.GCM.xor acc x)
          (Standards.NIST.GCM.bitsOfBytes h)) initial
      if bytes.size % 16 = 0 then full else
        Standards.NIST.GCM.mul (Standards.NIST.GCM.xor full
          (paddedBlock bytes (bytes.size / 16))) (Standards.NIST.GCM.bitsOfBytes h) := by
  unfold hashPadded
  rw [paddedBlocks_eq_full_tail, Array.toList_append, List.foldl_append]
  split <;> simp only [List.foldl_nil,
    List.foldl_cons]

theorem stateBits_lengthBlock (a c : Nat) :
    stateBits (BitVec.ofNat 64 c, BitVec.ofNat 64 a) =
      Standards.NIST.GCM.integerToString 64 a ++ Standards.NIST.GCM.integerToString 64 c := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_append]
  simp only [stateBits, toGcmBits, Vector.getElem_ofFn, BitVec.getLsbD_reverse,
    BitVec.getMsbD_eq_getLsbD, hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp only [show ¬ 128 - 1 - i < 64 by omega, ite_false, h, dite_true,
      Standards.NIST.GCM.integerToString, Vector.getElem_ofFn, BitVec.getLsbD_ofNat,
      show 128 - 1 - i - 64 < 64 by omega, decide_true, Bool.true_and]
    congr 1
    omega
  · simp only [ite_true, h, dite_false,
      Standards.NIST.GCM.integerToString, Vector.getElem_ofFn, BitVec.getLsbD_ofNat,
      show 128 - 1 - i < 64 by omega, decide_true, Bool.true_and]
    congr 1
    omega

theorem sourceBlockBits_eq_paddedBlock_of_memByte (mem : Ram) (src : BitVec 64)
    (bytes : ByteArray) (j : Nat)
    (hbytes : ∀ i < 16, memByte mem (src + BitVec.ofNat 64 i) =
      if h : 16 * j + i < bytes.size then bytes[16 * j + i] else 0) :
    sourceBlockBits mem src 0 = paddedBlock bytes j := by
  apply Vector.ext
  intro i hi
  rw [sourceBlockBits_getElem]
  simp only [Nat.mul_zero, Nat.zero_add, hbytes (i / 8) (by omega),
    paddedBlock, Vector.getElem_ofFn]
  split
  · rfl
  · simp

theorem hashPadded_eq_updateBlocks (mem : Ram) (src : BitVec 64) (bytes : ByteArray)
    (h : Vector UInt8 16) (s tail : BitVec 64 × BitVec 64)
    (hbytes : (Runtime.span src bytes.size).HasBytes mem bytes)
    (htail : bytes.size % 16 ≠ 0 → stateBits tail = paddedBlock bytes (bytes.size / 16)) :
    let k := polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)
    let full := updateBlocks mem src (bytes.size / 16) k.1 k.2 s
    hashPadded h bytes (stateBits s) =
      stateBits (if bytes.size % 16 = 0 then full else
        polyvalMultiplyWords (full.1 ^^^ tail.1) (full.2 ^^^ tail.2) k.1 k.2) := by
  dsimp only
  rw [hashPadded_eq_full_tail, ← updateBlocks_full_bits mem src bytes h s hbytes]
  split
  · rfl
  · rename_i hmod
    rw [stateBits_multiply, htail hmod]

theorem authenticationTagFromMask_eq_state (h mask : Vector UInt8 16)
    (associatedData ciphertext : ByteArray) (s : BitVec 64 × BitVec 64)
    (hs : stateBits s = hashPadded h ciphertext
      (hashPadded h associatedData (Standards.NIST.GCM.zeros 128))) :
    let k := polyvalKeyWords (GcmContext.blockWord h 1) (GcmContext.blockWord h 0)
    authenticationTagFromMask h mask associatedData ciphertext =
      Standards.NIST.GCM.bytesOfBits (Standards.NIST.GCM.xor
        (stateBits (polyvalMultiplyWords (s.1 ^^^ BitVec.ofNat 64 (8 * ciphertext.size))
          (s.2 ^^^ BitVec.ofNat 64 (8 * associatedData.size)) k.1 k.2))
        (Standards.NIST.GCM.bitsOfBytes mask)) := by
  dsimp only
  rw [authenticationTagFromMask_eq_hashPadded,
    stateBits_multiply h s (BitVec.ofNat 64 (8 * ciphertext.size),
      BitVec.ofNat 64 (8 * associatedData.size)), stateBits_lengthBlock, hs]


theorem bytesOfBits_stateBits (s : BitVec 64 × BitVec 64) :
    Standards.NIST.GCM.bytesOfBits (stateBits s) = toBigEndianBytes (s.2 ++ s.1) := by
  rw [stateBits, toGcmBits_reverse_eq_bitsOfBytes, AesGcm.Proofs.bytesOfBits_bitsOfBytes]

theorem stateBits_blockWords (block : Vector UInt8 16) :
    stateBits (GcmContext.blockWord block 1, GcmContext.blockWord block 0) =
      Standards.NIST.GCM.bitsOfBytes block := by
  rw [stateBits, toGcmBits_reverse_eq_bitsOfBytes, GcmContext.blockWords_bytes]

theorem bytesOfBits_xor_stateBits (s : BitVec 64 × BitVec 64) (mask : Vector UInt8 16) :
    Standards.NIST.GCM.bytesOfBits
      (Standards.NIST.GCM.xor (stateBits s) (Standards.NIST.GCM.bitsOfBytes mask)) =
      toBigEndianBytes ((s.2 ^^^ GcmContext.blockWord mask 0) ++
        (s.1 ^^^ GcmContext.blockWord mask 1)) := by
  rw [← stateBits_blockWords mask, ← stateBits_xor, bytesOfBits_stateBits]

theorem bytesOfBits_xor_stateBits_getElem (s : BitVec 64 × BitVec 64)
    (mask : Vector UInt8 16) (i : Nat) (hi : i < 16) :
    (Standards.NIST.GCM.bytesOfBits
      (Standards.NIST.GCM.xor (stateBits s) (Standards.NIST.GCM.bitsOfBytes mask)))[i] =
      (if i < 8 then storedByte s.2 (7 - i) else storedByte s.1 (15 - i)) ^^^ mask[i] := by
  rw [bytesOfBits_xor_stateBits, ← BitVec.xor_append]
  have hm := congrArg (fun b : Vector UInt8 16 ↦ b[i]) (GcmContext.blockWords_bytes mask)
  simp only [toBigEndianBytes, Vector.getElem_ofFn] at hm ⊢
  rw [BitVec.extractLsb'_xor]
  change UInt8.ofBitVec ((s.2 ++ s.1).extractLsb' (8 * (15 - i)) 8) ^^^
    UInt8.ofBitVec ((GcmContext.blockWord mask 0 ++ GcmContext.blockWord mask 1).extractLsb'
      (8 * (15 - i)) 8) = _
  rw [hm]
  apply congrArg (fun x : UInt8 ↦ x ^^^ mask[i])
  by_cases h : i < 8
  · rw [ite_eq_left h, BitVec.extractLsb'_append_eq_of_le (by omega), storedByte_eq_extract]
    rw [show 8 * (15 - i) - 64 = 8 * (7 - i) by omega]
  · rw [ite_eq_right h, BitVec.extractLsb'_append_eq_of_add_le (by omega), storedByte_eq_extract]

end AesGcm.Proofs.Machine.Tag
