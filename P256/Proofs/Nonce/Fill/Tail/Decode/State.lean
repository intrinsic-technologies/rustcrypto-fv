import P256.Proofs.Nonce.Fill.Tail.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure ScanReady [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Context initial s orderAddress state where
  rip : s.RIP = 0x1074e8
  r12 : s.regValue .r12 = frameBase initial + 8
  r14 : s.regValue .r14 = 0
  r8 : s.regValue .r8 = 256
  rsi : s.regValue .rsi = 32
  output : (registerRegion initial .rsi 32).HasBytes s.external (updateValue state).value

structure ReadDone [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Context initial s orderAddress state where
  rip : s.RIP = 0x107528
  r12 : s.regValue .r12 = frameBase initial + 8
  r14 : s.regValue .r14 = 0
  status : (Operand.reg 0 : Operand 8).read s = 255
  integer : Nat256At s (frameBase initial + 104) (nextCandidate state).1

end P256.Proofs.Nonce.Fill.Tail.Decode
