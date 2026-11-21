import P256.Proofs.Verifying.Message.Hash.Finalize.Interface
import P256.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure HashAt [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt32) : Prop extends Live initial s boundary where
  hashWords : SHA256.HashStateAt s (frameBase initial + 192) hash
  hashPointer : s.regValue .rbx = frameBase initial + 192

structure Working [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (hash : Array UInt32) : Prop
    extends HashAt initial s boundary hash where
  blocks : s.regValue .r12 = BitVec.ofNat 64 (message.size / 64)
  tailLength : s.regValue .r15 = BitVec.ofNat 64 (message.size % 64)

structure LengthReady [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (message : ByteArray) (hash : Array UInt32) : Prop
    extends HashAt initial s boundary hash where
  rip : s.RIP = 0x10d857
  prefixBytes : (MemoryRegion.mk (frameBase initial + 128).toNat 56).HasBytes
    s.external (SHA256.finalPrefix message)
  lengthWord : s.regValue .r15 =
    Common.Instructions.bswap64 (BitVec.ofNat 64 (8 * message.size))

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress
