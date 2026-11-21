import P256.Proofs.SignatureFromDer.Fixed.Scalar.State

set_option autoImplicit false

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ComparedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) : Prop extends FrameState s t where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10fb74
  output : t.regValue .rbx = s.regValue .rdi
  tag : t.regValue .r14 = 1
  valid : t.regValue .rdi = if Arith.uint input < Operations.domain.n then 1 else 0
  limb0 : t.regValue .r15 = BitVec.ofNat 64 (Arith.uint input)
  limb1 : t.regValue .r12 = BitVec.ofNat 64 (Arith.uint input / 2^64)
  limb2 : t.regValue .r13 = BitVec.ofNat 64 (Arith.uint input / 2^128)
  limb3 : t.regValue .rbp = BitVec.ofNat 64 (Arith.uint input / 2^192)

def ScalarResultAt (t : RamState) (address : BitVec 64) (input : ByteArray) : Prop :=
  if Arith.uint input < Operations.domain.n then
    loadBytes t.external address 8 = .ok (0 : BitVec 64) ∧
      P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At t (address + 8) (Arith.uint input)
  else loadBytes t.external address 8 = .ok (1 : BitVec 64)

end P256.Proofs.SignatureFromDer.Fixed.Scalar
