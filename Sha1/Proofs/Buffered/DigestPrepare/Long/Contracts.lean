import Sha1.Proofs.Buffered.DigestPrepare.Contracts

namespace Sha1.Proofs.Buffered.DigestPrepare.Long

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure State [Bindings] (initial : RamState) (input : ByteArray)
    (H : Vector (BitVec 32) 5) (s : RamState) : Prop
    extends Frame initial (returnBoundary initial) s where
  hash : (⟨(stackPtr s).toNat + 0x100, 20⟩ : MemoryRegion).HasBytes
    s.external (Wrapper.Hash.Serialize.stateBytes H)
  blocks : (Operand.mem (stackPtr s + 0xf8) : Operand 64).read s =
    BitVec.ofNat 64 (input.size / 64)
  tailPointer : (Operand.reg 12 : Operand 64).read s =
    initial.regValue .rdi + BitVec.ofNat 64 (input.size / 64 * 64)
  tailSize : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 (input.size % 64)

structure Prepared [Bindings] (initial : RamState) (input : ByteArray) (s : RamState) : Prop
    extends State initial input Standards.NIST.SHA1.initialHashValue s where
  rip : s.RIP = 0x1000b9
  inputPointer : (Operand.reg 6 : Operand 64).read s = initial.regValue .rdi
  statePointerArg : (Operand.reg 7 : Operand 64).read s = stackPtr s + 0x100
  blockCount : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 (input.size / 64)

structure Compressed [Bindings] (initial : RamState) (input : ByteArray) (s : RamState) : Prop
    extends State initial input (absorbedHash input) s where
  rip : s.RIP = 0x1000be

end Sha1.Proofs.Buffered.DigestPrepare.Long
