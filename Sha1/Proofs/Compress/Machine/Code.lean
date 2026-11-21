import Sha1.Proofs.Compress.Machine.Interface
import X86Proofs.Program.Entry

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program

theorem program_text_subset (offset : Nat) {bytes : List UInt8}
    (h : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (hBound : offset + bytes.length ≤ Extracted.textBytes.size) :
    ∀ x ∈ codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes,
      x ∈ Extracted.programImage := by
  intro x hx
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  rw [← h, ← chunked_toList_slice _ _ _ hBound] at hx
  exact codeRange_slice_subset _ _ offset bytes.length x hx

theorem program_text_slice {s : RamState} (hCode : CodeIn Extracted.programImage s)
    (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count)) s :=
  hCode.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset count h

theorem text_address_in_program (offset : Nat) (h : offset < Extracted.textBytes.size) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  have hLength : offset < Extracted.textBytes.toList.length := by
    rwa [chunked_toList_length]
  refine ⟨Extracted.textBytes.toList[offset], ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact mem_codeRange _ _ offset hLength

theorem program_text_range (offset length : Nat)
    (h : offset + length ≤ Extracted.textBytes.size) :
    ∀ i < length, InProgram
      ((Extracted.textAddress + BitVec.ofNat 64 offset) + BitVec.ofNat 64 i) := by
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact text_address_in_program (offset + i) (by omega)

theorem outsideCompression_ne {address pc : BitVec 64} (h : OutsideCompression address)
    (hLow : 0x1024e0 ≤ pc.toNat) (hHigh : pc.toNat < 0x1036df) : pc ≠ address := by
  intro hEq
  subst pc
  unfold OutsideCompression at h
  omega

end Sha1.Proofs.Compress.Machine
