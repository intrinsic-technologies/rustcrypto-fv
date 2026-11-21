import P256.Proofs.Field.Interface

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop :=
  CalleePre s boundary 0x114090 32 40 880

structure ParameterPre [Bindings] (s : RamState) (register : X86.Syntax.Reg)
    (outputBytes reserve : Nat) : Prop where
  bounded : (registerRegion s register 32).Bounded
  allocated : (registerRegion s register 32).Allocated s.external
  output : (registerRegion s register 32).Disjoint (registerRegion s .rdi outputBytes)
  stack : (registerRegion s register 32).Disjoint (Stack.region s reserve)

structure SafeGcdPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop extends
    CalleePre s boundary 0x111b70 32 40 704 where
  modulusRegion : ParameterPre s .rdx 40 704
  adjusterRegion : ParameterPre s .r8 40 704
  modulus : Nat256At s (s.regValue .rdx) P256.Spec.Operations.domain.p
  adjuster : Nat256At s (s.regValue .r8) (2^512 % P256.Spec.Operations.domain.p)
  inverse : s.regValue .rcx = 0xffffffffffffffff

end P256.Proofs.Field.Inverse
