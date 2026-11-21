import K256.Proofs.Verify.Hash.Padding.Bytes
import K256.Proofs.Verify.Hash.Padding.Standard.Computation
import K256.Proofs.Verify.Hash.Padding.Standard.Digest

set_option autoImplicit false

namespace K256.Proofs.Verify.Hash

abbrev initialHash : Array UInt32 :=
  Standards.NIST.SHA2.SHA256.«H⁽⁰⁾».toArray.map UInt32.ofBitVec

theorem serializeHash_compressBlocks_bytePadding (input : ByteArray) :
    serializeHash (compressBlocks initialHash (bytePadding input)) = Standards.NIST.SHA2.SHA256.hashBytes input := by
  rw [initialHash, compressBlocks_eq_hashComputation, serializeHash_eq_digestOfBits,
    bytesToBits_bytePadding]
  rfl

end K256.Proofs.Verify.Hash
