import P256.Proofs.Signing.Wrapper.Hash.Finalize.State
import P256.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure HashAt [Bindings] (initial start s : RamState)
    (hash : Array UInt32) : Prop extends Live initial start s where
  hashWords : SHA256.HashStateAt s (frameBase initial + 128) hash
  hashPointer : s.regValue .r15 = frameBase initial + 128

structure Working [Bindings] (initial start s : RamState)
    (message : ByteArray) (hash : Array UInt32) : Prop
    extends HashAt initial start s hash where
  blocks : s.regValue .r14 = BitVec.ofNat 64 (message.size / 64)
  tailLength : s.regValue .rbx = BitVec.ofNat 64 (message.size % 64)

structure LengthReady [Bindings] (initial start s : RamState)
    (message : ByteArray) (hash : Array UInt32) : Prop
    extends HashAt initial start s hash where
  rip : s.RIP = 0x10294a
  prefixBytes : (MemoryRegion.mk (frameBase initial + 64).toNat 56).HasBytes
    s.external (SHA256.finalPrefix message)
  lengthWord : s.regValue .rbx =
    Common.Instructions.bswap64 (BitVec.ofNat 64 (8 * message.size))

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress
