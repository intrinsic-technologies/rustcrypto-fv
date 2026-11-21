import P256.Proofs.Verifying.Message.Hash.Finalize.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Pad

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Loaded [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Live initial t boundary where
  rip : t.RIP = 0x10d755
  hash : SHA256.HashStateAt t (frameBase initial + 192)
    (SHA256.compressBlocks SHA256.initialHash message)
  tail : (MemoryRegion.mk (frameBase initial + 128).toNat (message.size % 64)).HasBytes
    t.external (SHA256.remainderBytes message)
  hashPointer : t.regValue .rbx = frameBase initial + 192
  count : t.regValue .r12 = BitVec.ofNat 64 (message.size / 64)
  position : t.regValue .r15 = BitVec.ofNat 64 (message.size % 64)
  remaining : t.regValue .r14 = BitVec.ofNat 64 (63 - message.size % 64)

structure Marked [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Live initial t boundary where
  rip : t.RIP = 0x10d76e
  hash : SHA256.HashStateAt t (frameBase initial + 192)
    (SHA256.compressBlocks SHA256.initialHash message)
  tail : (MemoryRegion.mk (frameBase initial + 128).toNat (message.size % 64)).HasBytes
    t.external (SHA256.remainderBytes message)
  marker : t.external[frameBase initial + 128 + BitVec.ofNat 64 (message.size % 64)]? = some 128
  hashPointer : t.regValue .rbx = frameBase initial + 192
  count : t.regValue .r12 = BitVec.ofNat 64 (message.size / 64)
  position : t.regValue .r15 = BitVec.ofNat 64 (message.size % 64)
  remaining : t.regValue .r14 = BitVec.ofNat 64 (63 - message.size % 64)
  destination : t.regValue .rdi = frameBase initial + 128 + BitVec.ofNat 64 (message.size % 64 + 1)
  zero : t.regValue .rsi = 0
  length : t.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64)

end P256.Proofs.Verifying.Message.Hash.Finalize.Pad
