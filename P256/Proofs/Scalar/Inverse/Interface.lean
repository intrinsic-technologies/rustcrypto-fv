import P256.Proofs.Field.Inverse.Interface

set_option autoImplicit false

namespace P256.Proofs.Scalar.Inverse

open P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SafeGcdPre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop extends
    CalleePre s boundary 0x111b70 32 40 704 where
  modulusRegion : P256.Proofs.Field.Inverse.ParameterPre s .rdx 40 704
  adjusterRegion : P256.Proofs.Field.Inverse.ParameterPre s .r8 40 704
  modulus : Nat256At s (s.regValue .rdx) P256.Spec.Operations.domain.n
  adjuster : Nat256At s (s.regValue .r8) 1
  inverse : s.regValue .rcx = 0x332e375511ff43b1

end P256.Proofs.Scalar.Inverse
