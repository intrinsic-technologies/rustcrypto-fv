import Standards.RFC.MD5
import Base16ct.Proofs.Copied.Md5.Spec.State
import Base16ct.Proofs.Copied.Md5.Spec.Program
import Base16ct.Proofs.Copied.Md5.Proofs.Machine
import X86Proofs.Instructions.Branch.Triple

namespace Base16ct.Proofs.Copied.Md5.Proofs.Block

open Base16ct.Proofs.Copied.Md5.Spec Base16ct.Proofs.Copied.Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem program_text_slice {s : RamState} (hCode : CodeIn Extracted.programImage s)
    (offset count : Nat) (h : offset + count ≤ Extracted.textBytes.size) :
    CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
      (Extracted.textBytes.toListFrom offset count)) s :=
  hCode.slice_of_section
    (sec := ⟨Extracted.textAddress, Extracted.textBytes⟩)
    (by simp [Extracted.programSections]) offset count h

end Base16ct.Proofs.Copied.Md5.Proofs.Block
