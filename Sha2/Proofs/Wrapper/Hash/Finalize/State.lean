import Sha2.Proofs.Wrapper.State
import Sha2.Proofs.Common.SHA256.Mathematics.Padding.Tail
import Sha2.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256

def paddedBuffer (message : ByteArray) : ByteArray :=
  remainderBytes message ++ ⟨#[128]⟩ ++ ⟨Array.replicate (63 - message.size % 64) 0⟩

def finalPrefix (message : ByteArray) : ByteArray :=
  if message.size % 64 < 56 then
    remainderBytes message ++ ⟨#[128]⟩ ++ ⟨Array.replicate (55 - message.size % 64) 0⟩
  else ⟨Array.replicate 56 0⟩

def finalBlock (message : ByteArray) : ByteArray :=
  finalPrefix message ++ NIST.Encoding.natToOctets 8 (8 * message.size)

structure HashAt [Bindings] (initial s : RamState) (hash : Array UInt32) (v : Variant := .sha256)
    : Prop extends Preserved initial s v where
  hashWords : HashStateAt s (stackPtr initial - 280) hash
  hashPointer : s.regValue .r14 = stackPtr initial - 280

structure Working [Bindings] (initial s : RamState) (message : ByteArray)
    (hash : Array UInt32) (v : Variant := .sha256) : Prop
    extends HashAt initial s hash v where
  blocks : s.regValue .r12 = BitVec.ofNat 64 (message.size / 64)
  tailLength : s.regValue .r15 = BitVec.ofNat 64 (message.size % 64)

structure Padded [Bindings] (initial s : RamState) (message : ByteArray) (v : Variant := .sha256)
    : Prop
    extends Working initial s message (compressBlocks v.initialHash message) v where
  rip : s.RIP = (v.pc 0x1fc)
  bytes : (⟨(stackPtr initial - 344).toNat, 64⟩ : MemoryRegion).HasBytes
    s.external (paddedBuffer message)
  paddingLength : s.regValue .rbx = BitVec.ofNat 64 (63 - message.size % 64)

structure LengthReady [Bindings] (initial s : RamState) (message : ByteArray)
    (hash : Array UInt32) (v : Variant := .sha256) : Prop
    extends HashAt initial s hash v where
  rip : s.RIP = (v.pc 0x2c2)
  prefixBytes : (⟨(stackPtr initial - 344).toNat, 56⟩ : MemoryRegion).HasBytes
    s.external (finalPrefix message)
  lengthWord : s.regValue .r15 = Common.Instructions.bswap64 (BitVec.ofNat 64 (8 * message.size))

end Sha2.Proofs.Wrapper.Hash.Finalize
