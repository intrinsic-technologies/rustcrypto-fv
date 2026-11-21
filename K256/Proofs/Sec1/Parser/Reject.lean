import K256.Proofs.Sec1.Parser.LengthTable
import K256.Proofs.Sec1.Decode

namespace K256.Proofs.Sec1.Parser

open Standards.SECG.ECC Standards.SECG.DomainParameters

theorem decodePublicKey_invalidTag {bytes : ByteArray} {t : UInt8}
    (head : bytes.data[0]? = some t) (invalid : ¬ validTag t.toBitVec) :
    K256.Spec.Secp256k1.decodePublicKey bytes = none := by
  apply decodePublicKey_wrongTag head <;> intro e <;> subst t <;> exact invalid (by decide)

theorem decodePublicKey_lengthMismatch {bytes : ByteArray} {t : UInt8}
    (head : bytes.data[0]? = some t) (valid : validTag t.toBitVec)
    (mismatch : bytes.size ≠ (lengthTable.get ⟨t.toNat, validTag_lt valid⟩).toNat) :
    K256.Spec.Secp256k1.decodePublicKey bytes = none := by
  have tags : t = 0 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by
    simp only [← UInt8.toBitVec_inj]
    exact valid
  rcases tags with rfl | rfl | rfl | rfl | rfl
  · exact decodePublicKey_wrongTag head (by decide) (by decide) (by decide) (by decide)
  all_goals
    first | change bytes.size ≠ 33 at mismatch | change bytes.size ≠ 65 at mismatch
    simp only [K256.Spec.Secp256k1.decodePublicKey, head, Option.some_beq_some,
      Points.decodePublicKey, Points.decodePoint,
      show (Secp256k1.domain.p.log2 + 8) / 8 = 32 by decide,
      Nat.reduceMul, Nat.reduceAdd, beq_eq_false_iff_ne.mpr mismatch]
    split <;> simp_all

end K256.Proofs.Sec1.Parser
