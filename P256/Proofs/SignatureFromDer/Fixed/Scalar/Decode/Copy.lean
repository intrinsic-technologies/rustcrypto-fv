import P256.Proofs.Program.ScalarFrame.Copy32Input

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)
open P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev bytes := Program.ScalarFrame.Copy32Input.bytes

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10fa41 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xfa41 bytes
    (by decide +kernel) (by decide +kernel)

theorem run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x10fa41
      (fun s => (Operand.reg 6 : Operand 64).read s + 0)
      (fun s => (Operand.reg 4 : Operand 64).read s + 72))
      (codeRange 0x10fa41 bytes)
      (Effect.post (Copy32.effect 0x10fa64
        (fun s => (Operand.reg 6 : Operand 64).read s + 0)
        (fun s => (Operand.reg 4 : Operand 64).read s + 72))) :=
  Program.ScalarFrame.Copy32Input.run boundary hout 0xfa41 (by decide)

end P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.Copy
