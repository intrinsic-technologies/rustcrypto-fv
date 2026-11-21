import Md5.Proofs.Buffered.DigestPrepare.Contracts

namespace Md5.Proofs.Buffered.DigestPrepare.Long

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure State [Bindings] (initial : RamState) (input : ByteArray)
    (buffer : Standards.RFC.MD5.Buffer) (s : RamState) : Prop
    extends Frame initial (returnBoundary initial) s where
  buffer : (⟨(stackPtr s).toNat + 240, 16⟩ : MemoryRegion).HasBytes
    s.external ⟨buffer.toBytes.toArray⟩
  blocks : (Operand.mem (stackPtr s + 256) : Operand 64).read s =
    BitVec.ofNat 64 (input.size / 64)
  tailPointer : (Operand.reg 12 : Operand 64).read s =
    initial.regValue .rdi + BitVec.ofNat 64 (input.size / 64 * 64)
  tailSize : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (input.size % 64)

structure Prepared [Bindings] (initial : RamState) (input : ByteArray) (s : RamState) : Prop
    extends State initial input Standards.RFC.MD5.Buffer.initial s where
  rip : s.RIP = 0x1000ae
  inputPointer : (Operand.reg 6 : Operand 64).read s = initial.regValue .rdi
  statePointerArg : (Operand.reg 7 : Operand 64).read s = stackPtr s + 240
  blockCount : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 (input.size / 64)

structure Compressed [Bindings] (initial : RamState) (input : ByteArray) (s : RamState) : Prop
    extends State initial input (absorbedBuffer input) s where
  rip : s.RIP = 0x1000b3

end Md5.Proofs.Buffered.DigestPrepare.Long
