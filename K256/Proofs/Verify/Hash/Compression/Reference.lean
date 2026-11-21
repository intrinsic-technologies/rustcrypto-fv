import K256.Proofs.Verify.Hash.Blocks

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash.Reference

abbrev rotateRight (word : UInt32) (count : Nat) : UInt32 :=
  UInt32.ofBitVec (Standards.NIST.SHA2.ROTR count word.toBitVec)

abbrev roundConstants : Array UInt32 :=
  Standards.NIST.SHA2.SHA256.K.toArray.map UInt32.ofBitVec

end K256.Proofs.Verify.Hash.Reference
