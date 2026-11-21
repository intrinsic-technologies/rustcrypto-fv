import P256.Proofs.Field.Interface
import P256.Proofs.Field.Montgomery.Arithmetic

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square

open P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev WidePre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  CalleePre s boundary 0x11cba0 32 64 88

structure ReductionPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop
    extends CalleePre s boundary 0x1133f0 64 32 112 where
  modulusBounded : (registerRegion s .rdx 32).Bounded
  modulusAllocated : (registerRegion s .rdx 32).Allocated s.external
  modulusOutput : (registerRegion s .rdx 32).Disjoint (registerRegion s .rdi 32)
  modulusStack : (registerRegion s .rdx 32).Disjoint (Stack.region s 112)
  modulus : Nat256At s (s.regValue .rdx) P256.Spec.Operations.domain.p
  inverse : s.regValue .rcx = 1

end P256.Proofs.Sec1.SquareRoot.Square
