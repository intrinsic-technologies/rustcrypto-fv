import P256.Proofs.Sec1.SquareRoot.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure MontgomeryPre [Bindings] (s : RamState) (boundary : ReturnBoundary) (entry : BitVec 64 := 0x1145e0) : Prop
    extends Field.BinaryFieldPre s boundary entry 160 where
  modulusBounded : (registerRegion s .rcx 32).Bounded
  modulusAllocated : (registerRegion s .rcx 32).Allocated s.external
  modulusOutput : (registerRegion s .rcx 32).Disjoint (registerRegion s .rdi 32)
  modulusStack : (registerRegion s .rcx 32).Disjoint (Stack.region s 160)
  modulus : P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At s (s.regValue .rcx)
    P256.Spec.Operations.domain.p
  inverse : s.regValue .r8 = 1

end P256.Proofs.Sec1.SquareRoot
