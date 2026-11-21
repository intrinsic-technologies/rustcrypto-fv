import P256.Proofs.Signing.Wrapper.Hash.Finalize.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Loaded [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Live initial start t where
  rip : t.RIP = 0x10287d
  hash : SHA256.HashStateAt t (frameBase initial + 128)
    (SHA256.compressBlocks SHA256.initialHash message)
  tail : (MemoryRegion.mk (frameBase initial + 64).toNat (message.size % 64)).HasBytes
    t.external (SHA256.remainderBytes message)
  hashPointer : t.regValue .r15 = frameBase initial + 128
  count : t.regValue .r14 = BitVec.ofNat 64 (message.size / 64)
  position : t.regValue .rbx = BitVec.ofNat 64 (message.size % 64)
  remaining : t.regValue .r12 = BitVec.ofNat 64 (63 - message.size % 64)

structure Marked [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Live initial start t where
  rip : t.RIP = 0x10288f
  hash : SHA256.HashStateAt t (frameBase initial + 128)
    (SHA256.compressBlocks SHA256.initialHash message)
  tail : (MemoryRegion.mk (frameBase initial + 64).toNat (message.size % 64)).HasBytes
    t.external (SHA256.remainderBytes message)
  marker : t.external[frameBase initial + 64 + BitVec.ofNat 64 (message.size % 64)]? = some 128
  hashPointer : t.regValue .r15 = frameBase initial + 128
  count : t.regValue .r14 = BitVec.ofNat 64 (message.size / 64)
  position : t.regValue .rbx = BitVec.ofNat 64 (message.size % 64)
  remaining : t.regValue .r12 = BitVec.ofNat 64 (63 - message.size % 64)
  destination : t.regValue .rdi = frameBase initial + BitVec.ofNat 64 (message.size % 64 + 65)
  zero : t.regValue .rsi = 0
  length : t.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64)

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Pad
