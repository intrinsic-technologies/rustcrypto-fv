import Sha2.Proofs.Common.Machine.Entry
import X86Proofs.Program.Execution

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem programText_slice {s : RamState}
    (h : CodeIn Extracted.programSections.toCodeMap s)
    (offset : Nat) (bytes : List UInt8)
    (hsize : offset + bytes.length ≤ 71757)
    (hbytes : Extracted.textBytes.toListFrom offset bytes.length = bytes) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) s := by
  have hs := h.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset bytes.length
    (by simpa only [textBytes_size] using hsize)
  simpa only [hbytes] using hs

theorem boundary_ne_program {boundary : ReturnBoundary}
    (h : ¬ InProgram boundary.rip) {address : BitVec 64}
    (ha : InProgram address) : address ≠ boundary.rip :=
  fun he => h (he ▸ ha)

theorem inProgram_of_textOffset (offset : Nat) (h : offset < 71757) :
    InProgram (Extracted.textAddress + BitVec.ofNat 64 offset) := by
  let address := Extracted.textAddress + BitVec.ofNat 64 offset
  have hi : offset < Extracted.textBytes.toList.length := by
    simpa only [chunked_toList_length, textBytes_size] using h
  refine ⟨Extracted.textBytes.toList[offset], ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨Extracted.textAddress, Extracted.textBytes⟩,
    by simp [Extracted.programSections], ?_⟩
  exact (mem_codeRange_iff _ _ _).mpr ⟨⟨offset, hi⟩, rfl⟩

end Sha2.Proofs.Common.Machine
