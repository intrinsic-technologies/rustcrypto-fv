import Md5.Spec
import Md5.Proofs.Machine
import X86Proofs.Instructions.Branch.Triple

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem program_text_slice {s : RamState} (hCode : CodeIn Extracted.programImage s)
    (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count)) s :=
  hCode.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset count h

theorem compress_jump [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = Extracted.md5CompressAddress) (hBoundary : 0x101ba0#64 ≠ boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      (jmpEffect 0x100000 5 0x1b9b).Holds s t := by
  have hBytes : CodeIn (codeRange 0x100000 [0xe9, 0x9b, 0x1b, 0x00, 0x00]) s :=
    program_text_slice hCode 0 5 (by decide +kernel)
  exact (jmp_rel32_effect_step 0x100000 0x1b9b (by decide +kernel)).advances
    hReady hBytes hEntry hBoundary

theorem compress_readOutput_of_external_eq {s t : RamState} {buffer : Standards.RFC.MD5.Buffer}
    (hBuffer : Call.Compress.ValidBuffer s buffer) (hMemory : t.external = s.external) :
    Compress.readOutput s t = .ok buffer.toBytes := by
  apply readVector_of_hasBytes
  rw [hMemory]
  exact hBuffer.2

theorem text_address_in_program (offset : Nat) (h : offset < Extracted.textBytes.size) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  have hLength : offset < Extracted.textBytes.toList.length := by
    rwa [chunked_toList_length]
  refine ⟨Extracted.textBytes.toList[offset], ?_⟩
  change _ ∈ Extracted.programSections.flatMap ImageSection.toCodeMap
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact mem_codeRange _ _ offset hLength

theorem text_address_ne_return {boundary : ReturnBoundary} (hOutside : ¬ InProgram boundary.rip)
    (offset : Nat) (h : offset < Extracted.textBytes.size) :
    Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip := by
  intro hEq
  exact hOutside (hEq ▸ text_address_in_program offset h)

end Md5.Proofs.Block
