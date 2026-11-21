import AesGcm.Proofs.Machine.Core.Memory

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem tag_words_eq_iff {mem : Ram} {computed supplied : BitVec 64}
    {left right : Vector UInt8 16}
    (hl : (span computed 16).HasBytes mem ⟨left.toArray⟩)
    (hr : (span supplied 16).HasBytes mem ⟨right.toArray⟩) :
    (memLoad mem computed 64 = memLoad mem supplied 64 ∧
      memLoad mem (computed + 8) 64 = memLoad mem (supplied + 8) 64) ↔ left = right := by
  have byte {ptr : BitVec 64} {v : Vector UInt8 16}
      (h : (span ptr 16).HasBytes mem ⟨v.toArray⟩) (i : Nat) (hi : i < 16) :
      memByte mem (ptr + BitVec.ofNat 64 i) = v[i] := by
    have hb := h.2 ⟨i, by simpa only [ByteArray.size, Vector.size_toArray] using hi⟩
    change mem[BitVec.ofNat 64 (ptr.toNat + i)]? = some v[i] at hb
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    simp only [memByte, PhysicalMemory.read, hb, Option.getD_some]
  constructor
  · rintro ⟨h0,h1⟩
    apply Vector.ext
    intro i hi
    by_cases h : i < 8
    · exact (byte hl i hi).symm.trans
        ((memByte_of_memLoad_eq h0 i h).trans (byte hr i hi))
    · have hb := memByte_of_memLoad_eq h1 (i - 8) (by omega)
      have eqaddr (p : BitVec 64) : p + 8 + BitVec.ofNat 64 (i - 8) =
          p + BitVec.ofNat 64 i := by
        rw [BitVec.add_assoc]
        change p + (BitVec.ofNat 64 8 + BitVec.ofNat 64 (i - 8)) = _
        rw [← BitVec.ofNat_add, Nat.add_sub_of_le (by omega : 8 ≤ i)]
      rw [eqaddr, eqaddr] at hb
      exact (byte hl i hi).symm.trans (hb.trans (byte hr i hi))
  · rintro rfl
    constructor
    · apply memLoad_congr
      intro i hi
      exact (byte hl i (by omega)).trans (byte hr i (by omega)).symm
    · apply memLoad_congr
      intro i hi
      have eqaddr (p : BitVec 64) : p + 8 + BitVec.ofNat 64 i =
          p + BitVec.ofNat 64 (8 + i) := by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
      rw [eqaddr, eqaddr]
      exact (byte hl (8+i) (by omega)).trans (byte hr (8+i) (by omega)).symm

end AesGcm.Proofs.Machine.Core.Decrypt
