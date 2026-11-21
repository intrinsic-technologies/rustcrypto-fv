import P256.Proofs.SHA256.Mathematics.Padding.Bytes
import P256.Proofs.SHA256.Mathematics.Padding.Standard.Computation
import P256.Proofs.SHA256.Mathematics.Padding.Standard.Digest

set_option autoImplicit false

namespace P256.Proofs.SHA256

abbrev initialHash : Array UInt32 :=
  Standards.NIST.SHA2.SHA256.«H⁽⁰⁾».toArray.map UInt32.ofBitVec

theorem serializeHash_compressBlocks_bytePadding (input : ByteArray) :
    serializeHash (compressBlocks initialHash (bytePadding input)) = Standards.NIST.SHA2.SHA256.hashBytes input := by
  rw [initialHash, compressBlocks_eq_hashComputation, serializeHash_eq_digestOfBits,
    bytesToBits_bytePadding]
  rfl

end P256.Proofs.SHA256
