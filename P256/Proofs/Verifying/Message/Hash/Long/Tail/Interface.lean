import P256.Proofs.Verifying.Message.Hash.Finalize.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long.Tail

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Ready [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Finalize.Live initial t boundary where
  rip : t.RIP = 0x10d6fa
  current : t.regValue .r13 = initial.regValue .rdx
  endPointer : t.regValue .r12 = initial.regValue .rdx + 16
  source : t.regValue .rsi = memLoad initial.external (initial.regValue .rdx) 64 +
    BitVec.ofNat 64 (64 * (message.size / 64))
  destination : t.regValue .rdi = frameBase initial + 472
  length : t.regValue .rdx = BitVec.ofNat 64 (message.size % 64)
  hash : SHA256.HashStateAt t (frameBase initial + 536)
    (SHA256.compressBlocks SHA256.initialHash message)
  count : loadBytes t.external (frameBase initial + 568) 8 =
    .ok (BitVec.ofNat 64 (message.size / 64))
  position : t.external[frameBase initial + 535]? = some (UInt8.ofNat (message.size % 64))

end P256.Proofs.Verifying.Message.Hash.Long.Tail
