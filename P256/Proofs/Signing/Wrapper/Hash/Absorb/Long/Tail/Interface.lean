import P256.Proofs.Signing.Wrapper.Hash.Absorb.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Ready [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Frame initial start t where
  rip : t.RIP = 0x102846
  source : t.regValue .rsi = start.regValue .rsi +
    BitVec.ofNat 64 (64 * (message.size / 64))
  destination : t.regValue .rdi = frameBase initial + 176
  length : t.regValue .rdx = BitVec.ofNat 64 (message.size % 64)
  hash : SHA256.HashStateAt t (frameBase initial + 240)
    (SHA256.compressBlocks SHA256.initialHash message)
  count : loadBytes t.external (frameBase initial + 272) 8 =
    .ok (BitVec.ofNat 64 (message.size / 64))
  position : t.external[frameBase initial + 239]? = some (UInt8.ofNat (message.size % 64))

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail
