import P256.Proofs.Verifying.Message.Hash.Buffered
import P256.Proofs.SHA256.Mathematics.Padding.Finalize

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Live [Bindings] (initial t : RamState) (boundary : ReturnBoundary) : Prop
    extends Frame initial t where
  execution : ∃ fuel, Advances boundary fuel initial t
  savedKey : memLoad t.external (frameBase initial + 456) 64 = initial.regValue .rsi
  savedOutput : memLoad t.external (frameBase initial + 384) 64 = initial.regValue .rdi
  savedSignature : memLoad t.external (frameBase initial + 464) 64 = initial.regValue .r8
  stackFrame : MemoryWriteFrame initial t #v[Stack.region initial 9992]

structure Copied [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Live initial t boundary where
  rip : t.RIP = 0x10d735
  hash : HMAC.Sha256StateAt t (frameBase initial + 128) message

structure Padded [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Live initial t boundary where
  rip : t.RIP = 0x10d774
  hash : SHA256.HashStateAt t (frameBase initial + 192)
    (SHA256.compressBlocks SHA256.initialHash message)
  buffer : (MemoryRegion.mk (frameBase initial + 128).toNat 64).HasBytes t.external
    (SHA256.paddedBuffer message)
  hashPointer : t.regValue .rbx = frameBase initial + 192
  count : t.regValue .r12 = BitVec.ofNat 64 (message.size / 64)
  position : t.regValue .r15 = BitVec.ofNat 64 (message.size % 64)
  remaining : t.regValue .r14 = BitVec.ofNat 64 (63 - message.size % 64)

structure Result [Bindings] (initial t : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) : Prop extends Live initial t boundary where
  rip : t.RIP = 0x10d8ce
  hash : ∃ hash, SHA256.HashStateAt t (frameBase initial + 192) hash ∧
    SHA256.serializeHash hash = Operations.hash message

end P256.Proofs.Verifying.Message.Hash.Finalize
