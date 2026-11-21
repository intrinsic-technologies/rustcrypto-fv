import Standards.NIST.SHA2

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash

namespace Reference

abbrev bitsToNat (input : Array Bool) : Nat :=
  (BitVec.ofBoolListBE input.toList).toNat

abbrev compress (hash : Array UInt32) (block : Array Bool) : Array UInt32 :=
  (Standards.NIST.SHA2.SHA256.hashBlock
    (Vector.ofFn fun i : Fin 8 => hash[i.val]!.toBitVec)
    (Vector.ofFn fun i : Fin 16 => BitVec.ofNat 32
      (bitsToNat (block.extract (32 * i.val) (32 * (i.val + 1)))))).toArray.map
    UInt32.ofBitVec

end Reference

def blockBits (input : ByteArray) (index : Nat) : Array Bool :=
  Standards.NIST.SHA2.bytesToBits (input.extract (64 * index) (64 * (index + 1)))

def compressBlocksFrom (hash : Array UInt32) (input : ByteArray) (start : Nat) :
    Nat → Array UInt32
  | 0 => hash
  | count + 1 => compressBlocksFrom
      (Reference.compress hash (blockBits input start)) input (start + 1) count

def compressBlocks (hash : Array UInt32) (input : ByteArray) : Array UInt32 :=
  compressBlocksFrom hash input 0 (input.size / 64)

end K256.Proofs.Verify.Hash
