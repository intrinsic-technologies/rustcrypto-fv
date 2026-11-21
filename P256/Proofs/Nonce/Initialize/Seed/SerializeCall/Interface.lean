import P256.Proofs.Nonce.Initialize.Reduce.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure SerializationReady [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) (value : Nat) : Prop where
  stage : Stage initial s boundary
  rip : s.RIP = 0x107b80
  order : s.regValue .r15 = orderAddress
  buffer : s.regValue .r12 = stackPtr s + 200
  length : s.regValue .rbx = 32
  secret : memLoad s.external (stackPtr s + 184) 64 = initial.regValue .rsi
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  entropy : memLoad s.external (stackPtr s + 168) 64 = 1
  outputPointer : s.regValue .r14 = initial.regValue .rdi
  source : s.regValue .rdi = stackPtr s + 8
  orderArg : s.regValue .rsi = orderAddress
  destination : s.regValue .rdx = stackPtr s + 200
  count : s.regValue .rcx = 32
  reduced : Nat256At s (stackPtr s + 8) value

end P256.Proofs.Nonce.Initialize.Seed
