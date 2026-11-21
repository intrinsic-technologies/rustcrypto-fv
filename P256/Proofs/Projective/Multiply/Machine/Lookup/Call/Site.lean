import P256.Proofs.Projective.Multiply.Machine.Lookup.Memory
import P256.Proofs.Program.FieldCall

set_option autoImplicit false

open P256.Proofs.Program (StackCallLayout)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StackCallSite (entry : BitVec 64) (outputBytes reserve : Nat) where
  codeOffset : Nat
  disp : BitVec 32
  codeBound : codeOffset + 5 < 118431
  bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp
  target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 (disp.signExtend 64) = entry
  entryLow : entry.toNat < 2^32
  entryProgram : InProgram entry
  layout : StackCallLayout 496 32 outputBytes reserve
  stack : layout.stackOffset = 368
  outputSaved : outputBytes + 48 ≤ layout.outputOffset

end P256.Proofs.Projective.Multiply.Machine.Lookup
