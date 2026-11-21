import K256.Proofs.Sec1.Decode

namespace K256.Proofs.Ecdh.Decode

open Standards.SECG.ECC Standards.SECG.DomainParameters

theorem groupPoint_cases {bytes : ByteArray} {q : Curve.Point}
    (h : K256.Spec.Secp256k1.groupPoint bytes = some q) :
    (bytes = ⟨Array.replicate 33 0⟩ ∧ q = .infinity) ∨
    (bytes.size = 33 ∧ ∃ tag : UInt8, bytes.data[0]? = some tag ∧
      (tag = 2 ∨ tag = 3 ∨ tag = 5) ∧
      Sec1.decompress (if tag = 5 then 2 else tag)
        (Encoding.octetsToNat (bytes.extract 1 33)) = some q) := by
  unfold K256.Spec.Secp256k1.groupPoint at h
  split at h
  next zero =>
    have data : bytes.data = Array.replicate 33 0 := eq_of_beq (α := Array UInt8) zero
    exact Or.inl ⟨congrArg ByteArray.mk data, (Option.some.inj h).symm⟩
  next =>
    split at h
    next size =>
      have len : bytes.size = 33 := eq_of_beq size
      let tag := bytes[0]'(by omega)
      have head : bytes.data[0]? = some tag := Array.getElem?_eq_getElem (by change 0 < bytes.size; omega)
      have valid : tag = 2 ∨ tag = 3 ∨ tag = 5 := by
        by_cases two : tag = 2
        · exact .inl two
        by_cases three : tag = 3
        · exact .inr (.inl three)
        by_cases five : tag = 5
        · exact .inr (.inr five)
        by_cases four : tag = 4
        · have header := head.trans (congrArg some four)
          have identity : (bytes == ⟨#[0]⟩) = false := by
            change (bytes.data == #[0]) = false
            apply beq_eq_false_iff_ne.mpr
            intro eq
            have : bytes.size = 1 := congrArg Array.size eq
            omega
          simp only [K256.Spec.Secp256k1.decodePublicKey, len, header,
            show (some (4 : UInt8) == some 5) = false by decide, Bool.and_false,
            Bool.false_eq_true, ite_false, Points.decodePublicKey, Points.decodePoint, identity,
            show (Secp256k1.domain.p.log2 + 8) / 8 = 32 by decide, Option.getD_some,
            Nat.reduceMul, Nat.reduceAdd, Nat.reduceBEq, Bool.false_and,
            show ((4 : UInt8) == 2 || (4 : UInt8) == 3) = false by decide] at h
          contradiction
        · rw [Sec1.decodePublicKey_wrongTag head two three four five] at h
          contradiction
      refine Or.inr ⟨len, tag, head, valid, ?_⟩
      rcases valid with e | e | e
      · simpa only [e, show (2 : UInt8) ≠ 5 by decide, ite_false] using
          (Sec1.decodePublicKey_compressed len head (Or.inl e)).symm.trans h
      · simpa only [e, show (3 : UInt8) ≠ 5 by decide, ite_false] using
          (Sec1.decodePublicKey_compressed len head (Or.inr e)).symm.trans h
      · simpa only [e, ite_true] using
          (Sec1.decodePublicKey_compact len (head.trans (congrArg some e))).symm.trans h
    next => contradiction

end K256.Proofs.Ecdh.Decode
