import Hkdf.Proofs.Common.Machine.Interfaces
import Hkdf.Proofs.NIST.SHA256

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open Hkdf.Spec Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess
open Hkdf.Proofs.Common.Machine

abbrev initialHash : Array UInt32 := Hkdf.Proofs.NIST.SHA256.initialHash

def blockBits (input : ByteArray) (index : Nat) : Array Bool :=
  NIST.Encoding.octetsToBits (input.extract (64 * index) (64 * (index + 1)))

def compressBlocksFrom (hash : Array UInt32) (input : ByteArray) (start : Nat) :
    Nat → Array UInt32
  | 0 => hash
  | count + 1 => compressBlocksFrom
      (NIST.SHA256.compress hash (blockBits input start)) input (start + 1) count

def compressBlocks (hash : Array UInt32) (input : ByteArray) : Array UInt32 :=
  compressBlocksFrom hash input 0 (input.size / 64)

def HashStateAt (s : RamState) (address : BitVec 64) (hash : Array UInt32) : Prop :=
  hash.size = 8 ∧ ∀ i < 8,
    loadBytes s.external (address + BitVec.ofNat 64 (4 * i)) 4 = .ok (hash[i]!.toBitVec.zeroExtend 64)

structure CompressionPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt32) (input : ByteArray) (count : Nat) : Prop extends
    CalleePre s boundary 0x1095c0 (64 * count) 32 336 where
  hashAligned : (s.regValue .rdi).toNat % 4 = 0
  countRegister : s.regValue .rdx = BitVec.ofNat 64 count
  inputBytes : (registerRegion s .rsi (64 * count)).HasBytes s.external input
  hashWords : HashStateAt s (s.regValue .rdi) hash

structure CompressionResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (hash : Array UInt32) (input : ByteArray) : Prop extends
    CalleeResult s t boundary 32 336 where
  hashWords : HashStateAt t (s.regValue .rdi) (compressBlocks hash input)

end Hkdf.Proofs.Common.SHA256
