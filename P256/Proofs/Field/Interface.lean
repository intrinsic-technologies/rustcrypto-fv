import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Spec.Operations

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def MontgomeryAt (s : RamState) (address : BitVec 64) (value : Nat) : Prop :=
  value < P256.Spec.Operations.domain.p ∧
    Nat256At s address (value * 2^256 % P256.Spec.Operations.domain.p)

structure BinaryFieldPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (entry : BitVec 64) (reserve : Nat) : Prop extends
    CalleePre s boundary entry 32 32 reserve where
  rightBounded : (registerRegion s .rdx 32).Bounded
  rightAllocated : (registerRegion s .rdx 32).Allocated s.external
  rightOutput : (registerRegion s .rdx 32).Disjoint (registerRegion s .rdi 32)
  rightStack : (registerRegion s .rdx 32).Disjoint (Stack.region s reserve)

abbrev AddPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  BinaryFieldPre s boundary 0x1137c0 16

abbrev SubtractPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  BinaryFieldPre s boundary 0x1137e0 24

abbrev MultiplyPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  BinaryFieldPre s boundary 0x113890 280

structure SchoolbookPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop
    extends CalleePre s boundary 0x11c960 32 64 136 where
  rightBounded : (registerRegion s .rcx 32).Bounded
  rightAllocated : (registerRegion s .rcx 32).Allocated s.external
  rightOutput : (registerRegion s .rcx 32).Disjoint (registerRegion s .rdi 64)
  rightStack : (registerRegion s .rcx 32).Disjoint (Stack.region s 136)
  leftLength : s.regValue .rdx = 4
  rightLength : s.regValue .r8 = 4

end P256.Proofs.Field
