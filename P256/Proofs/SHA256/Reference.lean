import Standards.NIST.SHA2

set_option autoImplicit false

namespace P256.Proofs.SHA256.Reference

abbrev rotateRight (word : UInt32) (count : Nat) : UInt32 :=
  UInt32.ofBitVec (Standards.NIST.SHA2.ROTR count word.toBitVec)

abbrev roundConstants : Array UInt32 :=
  Standards.NIST.SHA2.SHA256.K.toArray.map UInt32.ofBitVec

abbrev bitsToNat (input : Array Bool) : Nat :=
  (BitVec.ofBoolListBE input.toList).toNat

abbrev compress (hash : Array UInt32) (block : Array Bool) : Array UInt32 :=
  (Standards.NIST.SHA2.SHA256.hashBlock
    (Vector.ofFn fun i : Fin 8 => hash[i.val]!.toBitVec)
    (Vector.ofFn fun i : Fin 16 => BitVec.ofNat 32
      (bitsToNat (block.extract (32 * i.val) (32 * (i.val + 1)))))).toArray.map
    UInt32.ofBitVec

end P256.Proofs.SHA256.Reference
