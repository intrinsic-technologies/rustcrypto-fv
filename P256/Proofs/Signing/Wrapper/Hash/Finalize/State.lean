import P256.Proofs.Signing.Wrapper.Hash.Finalize.Interface
import P256.Proofs.SHA256.Mathematics.Padding.Finalize

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Live [Bindings] (initial start t : RamState) : Prop
    extends Frame initial start t where

structure Copied [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Live initial start t where
  rip : t.RIP = 0x102861
  hash : HMAC.Sha256StateAt t (frameBase initial + 64) message

structure Padded [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Live initial start t where
  rip : t.RIP = 0x102895
  hash : SHA256.HashStateAt t (frameBase initial + 128)
    (SHA256.compressBlocks SHA256.initialHash message)
  buffer : (MemoryRegion.mk (frameBase initial + 64).toNat 64).HasBytes t.external
    (SHA256.paddedBuffer message)
  hashPointer : t.regValue .r15 = frameBase initial + 128
  count : t.regValue .r14 = BitVec.ofNat 64 (message.size / 64)
  position : t.regValue .rbx = BitVec.ofNat 64 (message.size % 64)
  remaining : t.regValue .r12 = BitVec.ofNat 64 (63 - message.size % 64)

structure Compressed [Bindings] (initial start t : RamState)
    (message : ByteArray) : Prop extends Live initial start t where
  rip : t.RIP = 0x1029a9
  hash : ∃ hash, SHA256.HashStateAt t (frameBase initial + 128) hash ∧
    SHA256.serializeHash hash = Operations.hash message

end P256.Proofs.Signing.Wrapper.Hash.Finalize
