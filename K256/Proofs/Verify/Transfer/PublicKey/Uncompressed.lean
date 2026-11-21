import K256.Proofs.Sec1.Decode

namespace K256.Proofs.Verify.Transfer.PublicKey

open Standards.SECG.ECC

theorem uncompressedTag {bytes : ByteArray} {p : Curve.Point} (size : bytes.size = 65)
    (decoded : K256.Spec.Secp256k1.decodePublicKey bytes = some p) : bytes.data[0]? = some 4 := by
  have hi : 0 < bytes.data.size := by change 0 < bytes.size; omega
  rw [Array.getElem?_eq_getElem hi]
  apply congrArg some
  apply Decidable.byContradiction
  intro h
  have invalid : (bytes == ⟨#[0]⟩) = false := by
    change (bytes.data == #[0]) = false
    apply beq_eq_false_iff_ne.mpr
    intro he
    have := congrArg Array.size he
    change bytes.size = 1 at this
    omega
  simp only [K256.Spec.Secp256k1.decodePublicKey, size, Nat.reduceBEq, Bool.false_and,
    Bool.false_eq_true, ite_false, Points.decodePublicKey, Points.decodePoint, invalid,
    show (Standards.SECG.DomainParameters.Secp256k1.domain.p.log2 + 8) / 8 = 32 by decide,
    Nat.reduceAdd, Nat.reduceMul, Array.getElem?_eq_getElem hi, Option.getD_some,
    beq_eq_false_iff_ne.mpr h, Bool.and_false] at decoded
  contradiction

theorem uncompressedOnCurve {bytes : ByteArray} {p : Curve.Point} (size : bytes.size = 65)
    (decoded : K256.Spec.Secp256k1.decodePublicKey bytes = some p) :
    Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain p = true := by
  rw [Sec1.decodePublicKey_uncompressed size (uncompressedTag size decoded)] at decoded
  dsimp only at decoded
  split at decoded
  · cases decoded
    assumption
  · cases decoded

end K256.Proofs.Verify.Transfer.PublicKey
