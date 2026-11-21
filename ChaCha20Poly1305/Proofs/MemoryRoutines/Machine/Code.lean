import ChaCha20Poly1305.Proofs.Common.WritableRange
import X86Proofs.Program.Entry
import X86Proofs.Program.Compose
import X86Proofs.Program.ReadWrite.Bytes

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Common

theorem program_text_slice {s : RamState} (hCode : CodeIn Extracted.programImage s)
    (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count)) s :=
  hCode.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset count h

theorem sectionFetch_isSome (sec : ImageSection) (x : BitVec 64 × UInt8)
    (hx : x ∈ sec.toCodeMap) : (sec.fetchByte x.1).isSome := by
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
  have hi : i.val < sec.bytes.size := by
    have := i.isLt
    simp only [chunked_toList_length] at this
    exact this
  have hsub : sec.address + BitVec.ofNat 64 i.val - sec.address = BitVec.ofNat 64 i.val := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have hlt : (BitVec.ofNat 64 i.val).toNat < sec.bytes.size := by
    rw [BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi
  simp only [ImageSection.fetchByte, hsub, Bytes.Chunked.get?, hlt, ↓reduceIte, Option.isSome_some]

theorem sectionsFetch_isSome (sections : ImageSections) (x : BitVec 64 × UInt8)
    (hx : x ∈ sections.toCodeMap) : (sections.fetchByte x.1).isSome := by
  induction sections with
  | nil => simp [ImageSections.toCodeMap] at hx
  | cons sec rest ih =>
    simp only [ImageSections.toCodeMap, List.flatMap_cons, List.mem_append] at hx
    simp only [ImageSections.fetchByte]
    rcases hx with hx | hx
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (sectionFetch_isSome sec x hx)
      simp [hb]
    · cases h : sec.fetchByte x.1 with
      | some b => simp
      | none => simpa using ih hx

theorem inProgram_of_mem {x : BitVec 64 × UInt8} (hx : x ∈ Extracted.programImage) :
    InProgram x.1 := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (sectionsFetch_isSome Extracted.programSections x hx)
  exact ⟨b, hb⟩

theorem text_address_in_program (offset : Nat) (h : offset < Extracted.textBytes.size) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  have hLength : offset < Extracted.textBytes.toList.length := by
    rwa [chunked_toList_length]
  exact inProgram_of_mem (x := (_, Extracted.textBytes.toList[offset]))
    (List.mem_flatMap.mpr ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
      by simp [Extracted.programSections], mem_codeRange _ _ offset hLength⟩)

end ChaCha20Poly1305.Proofs.MemoryRoutines.Machine
