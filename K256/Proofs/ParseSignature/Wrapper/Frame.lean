import K256.Proofs.ParseSignature.Contract
import K256.Proofs.LIR.Fn103ac0.Frame
import K256.Proofs.Common.SignatureRun

namespace K256.Proofs.ParseSignature.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86Proofs K256.Proofs.Lift K256.Proofs.Refine

def pairFrame (initial : RamState) : Activation :=
  let sp := initial.regValue .rsp
  let saved := memStore initial.external (sp - 8) (initial.regValue .rbx)
  { Activation.ofEntry initial signatureFromSlice.minStackBytes 0x102468 with
    original := memStore saved (sp - 96) (0x102468 : BitVec 64)
    rsp := sp - 96
    rbx := initial.regValue .rdi
    rdi := sp - 80 }

end K256.Proofs.ParseSignature.Wrapper
