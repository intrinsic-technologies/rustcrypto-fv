import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Parser.Assert

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem advanceText [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {pre : RamState → Prop} {bytes : List UInt8} {e : RamState → Effect}
    (offset : Nat)
    (hstep : StepEffect pre (codeRange
      (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) e)
    (hbytes : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (hsize : offset + bytes.length ≤ 118431)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s) (hp : pre s)
    (hne : (e s).rip ≠ boundary.rip)
    (hav : (e s).Avoids Extracted.programSections.toCodeMap) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ (e s).Holds s t := by
  obtain ⟨t, ha, ht, he⟩ := hstep.advances hr (programText_slice hc offset bytes hsize hbytes) hp hne
  exact ⟨t, ha, ht, he.codeIn hav hc, he⟩

end P256.Proofs.SignatureFromDer.Parser.Assert
