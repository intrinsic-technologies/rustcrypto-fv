import K256.Spec.Secp256k1

namespace K256.Proofs.Sec1

open K256.Spec Standards.SECG.ECC Standards.SECG.DomainParameters

private theorem coordinateWidth : (Secp256k1.domain.p.log2 + 8) / 8 = 32 := by decide

theorem decodePublicKey_wrongLength {bytes : ByteArray} (hc : bytes.size ≠ 33)
    (hu : bytes.size ≠ 65) : K256.Spec.Secp256k1.decodePublicKey bytes = none := by
  simp only [K256.Spec.Secp256k1.decodePublicKey, beq_eq_false_iff_ne.mpr hc, Bool.false_and,
    Bool.false_eq_true, ite_false, Points.decodePublicKey, Points.decodePoint, coordinateWidth]
  split
  · rfl
  · simp [hu]

private theorem notIdentityEncoding {bytes : ByteArray} (h : bytes.size ≠ 1) :
    (bytes == ⟨#[0]⟩) = false := by
  change (bytes.data == #[0]) = false
  apply beq_eq_false_iff_ne.mpr
  intro he
  exact h (congrArg Array.size he)

theorem decodePublicKey_uncompressed {bytes : ByteArray} (hlen : bytes.size = 65)
    (htag : bytes.data[0]? = some 4) :
    K256.Spec.Secp256k1.decodePublicKey bytes =
      let point := Curve.Point.affine (Encoding.octetsToNat (bytes.extract 1 33))
        (Encoding.octetsToNat (bytes.extract 33 65))
      if Curve.onCurve Secp256k1.domain point then some point else none := by
  have hne := notIdentityEncoding (bytes := bytes) (by omega : bytes.size ≠ 1)
  simp only [K256.Spec.Secp256k1.decodePublicKey, hlen, Nat.reduceBEq, Bool.false_and,
    Bool.false_eq_true, ite_false, Points.decodePublicKey, Points.decodePoint, hne,
    coordinateWidth, Nat.reduceMul, Nat.reduceAdd, htag, Option.getD_some, beq_self_eq_true,
    Bool.true_and, ite_true]
  split <;> rfl

theorem decodePublicKey_wrongTag {bytes : ByteArray} {tag : UInt8}
    (htag : bytes.data[0]? = some tag) (h₂ : tag ≠ 2) (h₃ : tag ≠ 3)
    (h₄ : tag ≠ 4) (h₅ : tag ≠ 5) : K256.Spec.Secp256k1.decodePublicKey bytes = none := by
  simp only [K256.Spec.Secp256k1.decodePublicKey, htag, Option.some_beq_some,
    beq_eq_false_iff_ne.mpr h₅, Bool.and_false, Bool.false_eq_true, ite_false,
    Points.decodePublicKey, Points.decodePoint, Option.getD_some, beq_eq_false_iff_ne.mpr h₄,
    beq_eq_false_iff_ne.mpr h₂, beq_eq_false_iff_ne.mpr h₃, Bool.or_false, Bool.and_false]
  split <;> rfl

def decompress (tag : UInt8) (x : Nat) : Option Curve.Point := do
  let p := Secp256k1.domain.p
  if x ≥ p then none else
    let square := (x * x * x + 7) % p
    let root := (← K256.Spec.Secp256k1.sqrtMod square) % p
    let y := if root % 2 == tag.toNat % 2 then root else Curve.fieldSub p 0 root
    if y * y % p == square && y % 2 == tag.toNat % 2 then some (.affine x y) else none

private theorem decodeCompressed {bytes : ByteArray} {tag : UInt8} (hlen : bytes.size = 33)
    (htag : bytes.data[0]? = some tag) (ht : tag = 2 ∨ tag = 3) :
    Points.decodePublicKey Secp256k1.domain K256.Spec.Secp256k1.sqrtMod bytes =
      decompress tag (Encoding.octetsToNat (bytes.extract 1 33)) := by
  have hne := notIdentityEncoding (bytes := bytes) (by omega : bytes.size ≠ 1)
  have hor : (tag == 2 || tag == 3) = true := by rcases ht with rfl | rfl <;> decide
  simp only [Points.decodePublicKey, Points.decodePoint, hne, Bool.false_eq_true, ite_false,
    coordinateWidth, hlen, htag, Option.getD_some, Nat.reduceAdd, Nat.reduceMul, Nat.reduceBEq,
    Bool.false_and, hor, Bool.true_and, ite_true, decompress]
  simp only [show Secp256k1.domain.a = 0 from rfl, Nat.zero_mul, Nat.add_zero,
    show Secp256k1.domain.b = 7 from rfl]
  split
  · rfl
  · cases K256.Spec.Secp256k1.sqrtMod _ with
    | none => rfl
    | some r =>
      dsimp only [Bind.bind, Option.bind, Pure.pure]
      generalize (_ && _) = valid
      cases valid <;> rfl

theorem decodePublicKey_compressed {bytes : ByteArray} {tag : UInt8} (hlen : bytes.size = 33)
    (htag : bytes.data[0]? = some tag) (ht : tag = 2 ∨ tag = 3) :
    K256.Spec.Secp256k1.decodePublicKey bytes =
      decompress tag (Encoding.octetsToNat (bytes.extract 1 33)) := by
  have h₅ : (some tag == some (5 : UInt8)) = false := by
    rcases ht with rfl | rfl <;> decide
  simp only [K256.Spec.Secp256k1.decodePublicKey, htag, h₅, Bool.and_false,
    Bool.false_eq_true, ite_false]
  exact decodeCompressed hlen htag ht

theorem decodePublicKey_compact {bytes : ByteArray} (hlen : bytes.size = 33)
    (htag : bytes.data[0]? = some 5) :
    K256.Spec.Secp256k1.decodePublicKey bytes =
      decompress 2 (Encoding.octetsToNat (bytes.extract 1 33)) := by
  let tagBytes : ByteArray := ⟨#[2]⟩
  let x := bytes.extract 1 33
  have hs : x.size = 32 := by simp [x, hlen]
  have hz : (tagBytes ++ x).size = 33 := by rw [ByteArray.size_append, hs]; rfl
  have ht : (tagBytes ++ x).data[0]? = some 2 := by
    simp [tagBytes, ByteArray.data_append, Array.getElem?_append]
  have hx : (tagBytes ++ x).extract 1 33 = x :=
    ByteArray.extract_append_eq_right rfl (by rw [hs]; rfl)
  simp only [K256.Spec.Secp256k1.decodePublicKey, hlen, htag, beq_self_eq_true,
    Bool.and_self, ite_true]
  rw [decodeCompressed hz ht (Or.inl rfl), hx]

end K256.Proofs.Sec1
