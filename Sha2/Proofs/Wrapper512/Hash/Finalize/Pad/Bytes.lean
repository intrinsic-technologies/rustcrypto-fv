import Sha2.Proofs.Wrapper512.Hash.Finalize.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512

theorem padded_bytes {s : RamState} {message : ByteArray} {base : BitVec 64}
    (tail : (⟨base.toNat, message.size % 128⟩ : MemoryRegion).HasBytes
      s.external (remainderBytes message))
    (marker : s.external[base + BitVec.ofNat 64 (message.size % 128)]? = some 128)
    (zero : ∀ i < 127 - message.size % 128,
      s.external[base + BitVec.ofNat 64 (message.size % 128 + 1 + i)]? = some 0) :
    (⟨base.toNat, 128⟩ : MemoryRegion).HasBytes s.external (paddedBuffer message) := by
  refine ⟨paddedBuffer_size message, ?_⟩
  intro i
  have hi : i.val < 128 := by simpa only [paddedBuffer_size] using i.isLt
  have remSize := remainderBytes_size message
  change s.external[BitVec.ofNat 64 (base.toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases before : i.val < message.size % 128
  · have byte := tail.2 ⟨i.val, by omega⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    rw [byte]
    apply congrArg some
    simp only [paddedBuffer]
    rw [ByteArray.getElem_append_left
      (by simp only [ByteArray.size_append, remSize]; change _ < message.size % 128 + 1; omega),
      ByteArray.getElem_append_left (by omega)]
  · by_cases eq : i.val = message.size % 128
    · rw [show s.external[base + BitVec.ofNat 64 i.val]? = some 128 by
        simpa only [eq] using marker]
      apply congrArg some
      simp only [paddedBuffer]
      have prefixBound : i.val < message.size % 128 + 1 := by omega
      have one : (⟨#[128]⟩ : ByteArray).size = 1 := by decide
      rw [ByteArray.getElem_append_left
          (by simpa only [ByteArray.size_append, remSize, one] using prefixBound),
        ByteArray.getElem_append_right (by omega)]
      simp only [eq, remSize, Nat.sub_self]
      rfl
    · have after : message.size % 128 + 1 ≤ i.val := by omega
      have byte := zero (i.val - (message.size % 128 + 1)) (by omega)
      rw [Nat.add_sub_of_le after] at byte
      rw [byte]
      apply congrArg some
      simp only [paddedBuffer]
      have prefixBound : message.size % 128 + 1 ≤ i.val := after
      have one : (⟨#[128]⟩ : ByteArray).size = 1 := by decide
      rw [ByteArray.getElem_append_right
        (by simpa only [ByteArray.size_append, remSize, one] using prefixBound)]
      simp [ByteArray.getElem_eq_getElem_data, ByteArray.size_append, remSize]

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad
