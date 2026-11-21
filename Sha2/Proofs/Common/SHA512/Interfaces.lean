import Sha2.Proofs.Common.Machine.Interfaces
import Sha2.Proofs.NIST.SHA512

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess
open Sha2.Proofs.Common.Machine

def blockBits (input : ByteArray) (index : Nat) : Array Bool :=
  NIST.Encoding.octetsToBits (input.extract (128 * index) (128 * (index + 1)))

def compressBlocksFrom (hash : Array UInt64) (input : ByteArray) (start : Nat) :
    Nat → Array UInt64
  | 0 => hash
  | count + 1 => compressBlocksFrom
      (NIST.SHA512.compress hash (blockBits input start)) input (start + 1) count

def compressBlocks (hash : Array UInt64) (input : ByteArray) : Array UInt64 :=
  compressBlocksFrom hash input 0 (input.size / 128)

def HashStateAt (s : RamState) (address : BitVec 64) (hash : Array UInt64) : Prop :=
  hash.size = 8 ∧ ∀ i < 8,
    loadBytes s.external (address + BitVec.ofNat 64 (8 * i)) 8 = .ok (hash[i]!.toBitVec)

structure CompressionPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt64) (input : ByteArray) (count : Nat) : Prop extends
    CalleePre s boundary 0x10dd90 (128 * count) 64 416 where
  countRegister : s.regValue .rdx = BitVec.ofNat 64 count
  inputBytes : (registerRegion s .rsi (128 * count)).HasBytes s.external input
  hashWords : HashStateAt s (s.regValue .rdi) hash

structure CompressionResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt64) (input : ByteArray) : Prop extends
    CalleeResult s t boundary 64 416 where
  hashWords : HashStateAt t (s.regValue .rdi) (compressBlocks hash input)

end Sha2.Proofs.Common.SHA512
