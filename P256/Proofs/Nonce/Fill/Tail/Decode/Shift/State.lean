import P256.Proofs.Nonce.Fill.Tail.Decode.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Shift

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

structure Prepared [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Context initial s orderAddress state where
  rip : s.RIP = 0x107575
  r12 : s.regValue .r12 = frameBase initial + 8
  count : s.regValue .rdx = 0
  source : s.regValue .rsi = frameBase initial + 152
  destination : s.regValue .rdi = frameBase initial + 8
  integer : Nat256At s (frameBase initial + 152) (Signing.Search.nextCandidate state).1

end P256.Proofs.Nonce.Fill.Tail.Decode.Shift
