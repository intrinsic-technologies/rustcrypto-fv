import P256.Proofs.SHA256.Mathematics.Padding.Finalize

set_option autoImplicit false

namespace P256.Proofs.SHA256
open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem padded_bytes {s : RamState} {message : ByteArray} {base : BitVec 64}
    (tail : (⟨base.toNat, message.size % 64⟩ : MemoryRegion).HasBytes
      s.external (remainderBytes message))
    (marker : s.external[base + BitVec.ofNat 64 (message.size % 64)]? = some 128)
    (zero : ∀ i < 63 - message.size % 64,
      s.external[base + BitVec.ofNat 64 (message.size % 64 + 1 + i)]? = some 0) :
    (⟨base.toNat, 64⟩ : MemoryRegion).HasBytes s.external (paddedBuffer message) := by
  refine ⟨paddedBuffer_size message, ?_⟩
  intro i
  have hi : i.val < 64 := by simpa only [paddedBuffer_size] using i.isLt
  have remSize := remainderBytes_size message
  change s.external[BitVec.ofNat 64 (base.toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases before : i.val < message.size % 64
  · have byte := tail.2 ⟨i.val, by omega⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte
    rw [byte]
    apply congrArg some
    simp only [paddedBuffer]
    rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_append, remSize]; change _ < message.size % 64 + 1; omega),
      ByteArray.getElem_append_left (by omega)]
  · by_cases eq : i.val = message.size % 64
    · rw [show s.external[base + BitVec.ofNat 64 i.val]? = some 128 by simpa only [eq] using marker]
      apply congrArg some
      simp only [paddedBuffer]
      rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_append, remSize]; change _ < message.size % 64 + 1; omega),
        ByteArray.getElem_append_right (by omega)]
      simp only [eq, remSize, Nat.sub_self]
      rfl
    · have after : message.size % 64 + 1 ≤ i.val := by omega
      have byte := zero (i.val - (message.size % 64 + 1)) (by omega)
      rw [Nat.add_sub_of_le after] at byte
      rw [byte]
      apply congrArg some
      simp only [paddedBuffer]
      rw [ByteArray.getElem_append_right (by simp only [ByteArray.size_append, remSize]; change message.size % 64 + 1 ≤ _; omega)]
      simp [ByteArray.getElem_eq_getElem_data]

theorem hasBytes_prefix {memory : Ram} {region : MemoryRegion} {bytes : ByteArray}
    {count : Nat} (input : region.HasBytes memory bytes) (bound : count ≤ region.size) :
    (⟨region.start, count⟩ : MemoryRegion).HasBytes memory (bytes.extract 0 count) := by
  have size : (bytes.extract 0 count).size = count := by
    rw [ByteArray.size_extract, Nat.sub_zero]
    have hsize : bytes.size = region.size := input.1
    omega
  refine ⟨size, ?_⟩
  intro i
  have hi : i.val < bytes.size := by
    have := i.isLt
    have hsize : bytes.size = region.size := input.1
    omega
  simpa only [ByteArray.getElem_extract, Nat.zero_add] using input.2 ⟨i.val, hi⟩

end P256.Proofs.SHA256
