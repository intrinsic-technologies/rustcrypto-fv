import P256.Proofs.Program.Interface
import P256.Proofs.SHA256.Reference

set_option autoImplicit false

namespace P256.Proofs.SHA256

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def blockBits (input : ByteArray) (index : Nat) : Array Bool :=
  Standards.NIST.SHA2.bytesToBits (input.extract (64 * index) (64 * (index + 1)))

def compressBlocksFrom (hash : Array UInt32) (input : ByteArray) (start : Nat) :
    Nat → Array UInt32
  | 0 => hash
  | count + 1 => compressBlocksFrom
      (Reference.compress hash (blockBits input start)) input (start + 1) count

def compressBlocks (hash : Array UInt32) (input : ByteArray) : Array UInt32 :=
  compressBlocksFrom hash input 0 (input.size / 64)

def HashStateAt (s : RamState) (address : BitVec 64) (hash : Array UInt32) : Prop :=
  hash.size = 8 ∧ ∀ i < 8,
    loadBytes s.external (address + BitVec.ofNat 64 (4 * i)) 4 = .ok (hash[i]!.toBitVec.zeroExtend 64)

structure CompressionPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt32) (input : ByteArray) (count : Nat) : Prop extends
    CalleePre s boundary 0x115990 (64 * count) 32 336 where
  countRegister : s.regValue .rdx = BitVec.ofNat 64 count
  inputBytes : (registerRegion s .rsi (64 * count)).HasBytes s.external input
  hashWords : HashStateAt s (s.regValue .rdi) hash

structure CompressionResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt32) (input : ByteArray) : Prop extends
    CalleeResult s t boundary 32 336 where
  hashWords : HashStateAt t (s.regValue .rdi) (compressBlocks hash input)

end P256.Proofs.SHA256
