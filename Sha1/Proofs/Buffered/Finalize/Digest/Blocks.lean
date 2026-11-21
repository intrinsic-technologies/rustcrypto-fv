import Sha1.Proofs.Buffered.Invariant
import Sha1.Proofs.Buffered.Finalize.Contracts

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86Proofs
open Standards.NIST Standards.NIST.SHA1 Standards.NIST.SHA2
open Sha1.Proofs.Wrapper.Absorb

def padZeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

def lengthWord (message : ByteArray) : BitVec 64 := BitVec.ofNat 64 (8 * message.size)

def lengthBlockBytes (message : ByteArray) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 8 ↦
    UInt8.ofBitVec ((lengthWord message >>> (8 * (7 - i.val))).setWidth 8)⟩

def firstBlock (message : ByteArray) : ByteArray :=
  tailBytes message ++ ⟨#[128]⟩ ++ padZeros (63 - message.size % 64)

def lastBlock (message : ByteArray) : ByteArray :=
  (if message.size % 64 < 56 then (firstBlock message).extract 0 56 else padZeros 56) ++
    lengthBlockBytes message

@[simp] theorem size_padZeros (n : Nat) : (padZeros n).size = n := by
  simp only [padZeros, ByteArray.size, Array.size_replicate]

@[simp] theorem size_lengthBlockBytes (message : ByteArray) :
    (lengthBlockBytes message).size = 8 := by
  simp only [lengthBlockBytes, ByteArray.size, Array.size_ofFn]

@[simp] theorem size_firstBlock (message : ByteArray) : (firstBlock message).size = 64 := by
  unfold firstBlock
  rw [ByteArray.size_append, ByteArray.size_append, size_tailBytes, size_padZeros]
  change message.size % 64 + 1 + (63 - message.size % 64) = 64
  omega

@[simp] theorem size_lastBlock (message : ByteArray) : (lastBlock message).size = 64 := by
  unfold lastBlock
  rw [ByteArray.size_append, size_lengthBlockBytes]
  split
  · rw [ByteArray.size_extract, size_firstBlock]; rfl
  · rw [size_padZeros]

theorem getElem_firstBlock_tail (message : ByteArray) (i : Nat)
    (hi : i < message.size % 64) :
    (firstBlock message)[i]'(by rw [size_firstBlock]; omega) =
      (tailBytes message)[i]'(by rw [size_tailBytes]; exact hi) := by
  unfold firstBlock
  rw [ByteArray.getElem_append_left (by
      rw [ByteArray.size_append, size_tailBytes]
      change i < message.size % 64 + 1
      omega),
    ByteArray.getElem_append_left (by rw [size_tailBytes]; exact hi)]

theorem getElem_firstBlock_padding (message : ByteArray) :
    (firstBlock message)[message.size % 64]'(by rw [size_firstBlock]; omega) = 128 := by
  unfold firstBlock
  rw [ByteArray.getElem_append_left (by
      rw [ByteArray.size_append, size_tailBytes]
      change message.size % 64 < message.size % 64 + 1
      omega),
    ByteArray.getElem_append_right (by rw [size_tailBytes]; exact Nat.le_refl _)]
  simp only [size_tailBytes, Nat.sub_self]
  rfl

theorem getElem_firstBlock_zero (message : ByteArray) (i : Nat)
    (hp : message.size % 64 < i) (hi : i < 64) :
    (firstBlock message)[i]'(by rw [size_firstBlock]; exact hi) = 0 := by
  unfold firstBlock
  rw [ByteArray.getElem_append_right (by
      rw [ByteArray.size_append, size_tailBytes]
      change message.size % 64 + 1 ≤ i
      omega)]
  simp only [padZeros, ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]

theorem bytes_of_hasBytes {m : Ram} {region : MemoryRegion} {bytes : ByteArray}
    (h : region.HasBytes m bytes) :
    Bytes m (BitVec.ofNat 64 region.start) bytes.size (fun i ↦ bytes[i]!) := by
  intro i hi
  rw [← BitVec.ofNat_add]
  simpa only [getElem!_pos bytes i hi] using h.2 ⟨i, hi⟩

theorem hasBytes_of_bytes {m : Ram} {base : BitVec 64} {bytes : ByteArray}
    (h : Bytes m base bytes.size (fun i ↦ bytes[i]!)) :
    (⟨base.toNat, bytes.size⟩ : Prelude.MemoryRegion).HasBytes m bytes := by
  refine ⟨rfl, ?_⟩
  intro i
  have hb := h i.val i.isLt
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    getElem!_pos bytes i.val i.isLt] using hb

theorem firstBlock_bytes {m : Ram} {base : BitVec 64} (message : ByteArray)
    (hTail : Bytes m base (message.size % 64) (fun i ↦ (tailBytes message)[i]!))
    (hPadding : m[base + BitVec.ofNat 64 (message.size % 64)]? = some 128)
    (hZero : ∀ i, message.size % 64 < i → i < 64 →
      m[base + BitVec.ofNat 64 i]? = some 0) :
    Bytes m base 64 (fun i ↦ (firstBlock message)[i]!) := by
  intro i hi
  dsimp only
  rw [getElem!_pos (firstBlock message) i (by rw [size_firstBlock]; exact hi)]
  by_cases ht : i < message.size % 64
  · rw [getElem_firstBlock_tail _ _ ht]
    simpa only [getElem!_pos (tailBytes message) i (by rw [size_tailBytes]; exact ht)] using
      hTail i ht
  · by_cases he : i = message.size % 64
    · subst i
      rw [getElem_firstBlock_padding]
      exact hPadding
    · rw [getElem_firstBlock_zero _ _ (by omega) hi]
      exact hZero i (by omega) hi

theorem remaining_xor (p : Nat) (hp : p < 64) :
    BitVec.ofNat 64 p ^^^ 63 = BitVec.ofNat 64 (63 - p) := by
  revert p
  decide

end Sha1.Proofs.Buffered.Finalize.Digest
