import P256.Proofs.Sec1.Interface
import P256.Spec.Keys
import P256.Proofs.SecretKeyFromBytes.Encoding

set_option autoImplicit false

namespace P256.Proofs.Sec1

open P256.Spec
open Standards.SECG.ECC.Curve (Point)

def EncodingShape (bytes : ByteArray) : Prop :=
  (bytes = ⟨#[0]⟩) ∨
  (bytes.size = 33 ∧ (bytes.data[0]? = some 2 ∨ bytes.data[0]? = some 3 ∨
    bytes.data[0]? = some 5)) ∨
  (bytes.size = 65 ∧ bytes.data[0]? = some 4)

theorem field_octets : (Operations.domain.p.log2 + 8) / 8 = 32 := by decide +kernel

theorem decodePublicKey_ne_infinity (bytes : ByteArray) :
    Points.decodePublicKey bytes ≠ some Point.infinity := by
  simp only [Points.decodePublicKey]
  cases Points.decodePoint bytes with
  | none => simp
  | some point => cases point <;> simp

theorem decodePublicKey_affine {bytes : ByteArray} {x y : Nat} :
    Points.decodePublicKey bytes = some (.affine x y) ↔
      Points.decodePoint bytes = some (.affine x y) := by
  simp only [Points.decodePublicKey]
  cases Points.decodePoint bytes with
  | none => simp
  | some point => cases point <;> simp

theorem publicKeyFromSec1_eq (bytes : ByteArray) :
    Keys.publicKeyFromSec1 #[bytes] = (Points.decodePublicKey bytes).map Keys.uncompressed := rfl

theorem decodePoint_invalid_size {bytes : ByteArray}
    (h1 : bytes.size ≠ 1) (h33 : bytes.size ≠ 33) (h65 : bytes.size ≠ 65) :
    Points.decodePoint bytes = none := by
  have notIdentity : bytes ≠ ⟨#[0]⟩ := by
    intro he
    apply h1
    rw [he]
    rfl
  have notIdentityBool : (bytes == (⟨#[0]⟩ : ByteArray)) = false := by
    change (bytes.data == #[0]) = false
    apply Bool.eq_false_iff.mpr
    intro h
    exact notIdentity (ByteArray.ext (eq_of_beq h))
  simp [Points.decodePoint, h33, Standards.SECG.ECC.Points.decodePoint,
    field_octets, h65, notIdentityBool]

theorem decodePublicKey_invalid_size {bytes : ByteArray}
    (h1 : bytes.size ≠ 1) (h33 : bytes.size ≠ 33) (h65 : bytes.size ≠ 65) :
    Points.decodePublicKey bytes = none := by
  simp only [Points.decodePublicKey, decodePoint_invalid_size h1 h33 h65]

theorem EncodingShape.size {bytes : ByteArray} (shape : EncodingShape bytes) :
    bytes.size = 1 ∨ bytes.size = 33 ∨ bytes.size = 65 := by
  rcases shape with rfl | ⟨hs, _⟩ | ⟨hs, _⟩
  · exact .inl rfl
  · exact .inr (.inl hs)
  · exact .inr (.inr hs)

theorem decodePoint_invalid_shape {bytes : ByteArray} (shape : ¬ EncodingShape bytes) :
    Points.decodePoint bytes = none := by
  have notIdentity : (bytes == (⟨#[0]⟩ : ByteArray)) = false := by
    change (bytes.data == #[0]) = false
    apply Bool.eq_false_iff.mpr
    intro h
    exact shape (.inl (ByteArray.ext (eq_of_beq h)))
  have notCompact : ¬ (bytes.size = 33 ∧ bytes.data[0]? = some 5) :=
    fun h ↦ shape (.inr (.inl ⟨h.1, .inr (.inr h.2)⟩))
  have notUncompressed : (bytes.size == 65 && bytes.data[0]?.getD 0 == 4) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have tag : bytes.data[0]? = some 4 := by
      cases he : bytes.data[0]? with
      | none => simp [he] at h
      | some value => simpa only [he, Option.getD_some, Option.some.injEq] using h.2
    exact shape (.inr (.inr ⟨h.1, tag⟩))
  have notCompressed :
      (bytes.size == 33 && (bytes.data[0]?.getD 0 == 2 || bytes.data[0]?.getD 0 == 3)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    have tag : bytes.data[0]? = some 2 ∨ bytes.data[0]? = some 3 := by
      cases he : bytes.data[0]? with
      | none => simp [he] at h
      | some value => simpa only [he, Option.getD_some, Option.some.injEq] using h.2
    exact shape (.inr (.inl ⟨h.1, tag.elim Or.inl (fun he ↦ .inr (.inl he))⟩))
  simp only [Points.decodePoint, notCompact, ite_false, Standards.SECG.ECC.Points.decodePoint,
    notIdentity, Bool.false_eq_true, field_octets, Nat.reduceMul, Nat.reduceAdd,
    notUncompressed, notCompressed]

theorem decodePoint_identity : Points.decodePoint ⟨#[0]⟩ = some .infinity := by
  decide +kernel

theorem decodePoint_some_shape {bytes : ByteArray} {point : Point}
    (decoded : Points.decodePoint bytes = some point) : EncodingShape bytes := by
  classical
  by_cases shape : EncodingShape bytes
  · exact shape
  · rw [decodePoint_invalid_shape shape] at decoded
    contradiction

theorem decodePublicKey_some_affine {bytes : ByteArray} {point : Point}
    (decoded : Points.decodePublicKey bytes = some point) : ∃ x y, point = .affine x y := by
  cases point with
  | infinity => exact (decodePublicKey_ne_infinity bytes decoded).elim
  | affine x y => exact ⟨x, y, rfl⟩

theorem decodePublicKey_some_size {bytes : ByteArray} {point : Point}
    (decoded : Points.decodePublicKey bytes = some point) : bytes.size = 33 ∨ bytes.size = 65 := by
  obtain ⟨x, y, rfl⟩ := decodePublicKey_some_affine decoded
  have raw := decodePublicKey_affine.mp decoded
  rcases decodePoint_some_shape raw with identity | ⟨size, _⟩ | ⟨size, _⟩
  · rw [identity, decodePoint_identity] at raw
    cases raw
  · exact .inl size
  · exact .inr size

theorem uncompressed_affine_size (x y : Nat) : (Keys.uncompressed (.affine x y)).size = 65 := by
  have tagSize : (⟨#[4]⟩ : ByteArray).size = 1 := rfl
  simp [Keys.uncompressed, Keys.encodePoint, Standards.SECG.ECC.Points.encodePoint,
    P256.Proofs.SecretKeyFromBytes.Encoding.natToOctets_size, field_octets, tagSize]

theorem publicKeyFromSec1_result_size {bytes result : ByteArray}
    (decoded : Keys.publicKeyFromSec1 #[bytes] = some result) : result.size = 65 := by
  rw [publicKeyFromSec1_eq] at decoded
  obtain ⟨point, hp, hr⟩ := Option.map_eq_some_iff.mp decoded
  obtain ⟨x, y, rfl⟩ := decodePublicKey_some_affine hp
  rw [← hr]
  exact uncompressed_affine_size x y

end P256.Proofs.Sec1
