import P256.Proofs.Program.ScalarFrame.Copy32Input

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.FirstInput

open P256.Spec.Program.Routines X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame

abbrev bytes := Copy32Input.bytes

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x109ada bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x9ada bytes
    (by decide +kernel) (by decide +kernel)

end P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.FirstInput
