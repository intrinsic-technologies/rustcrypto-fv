import P256.Proofs.Sec1.Decode.Header
import P256.Proofs.Sec1.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Header

open Prelude

theorem accepts_iff (tag : BitVec 8) (n : Nat) (bound : n < 2^64) :
    accepts tag (BitVec.ofNat 64 n) = true ↔
      (n = 1 ∧ tag = 0) ∨
      (n = 33 ∧ (tag = 2 ∨ tag = 3 ∨ tag = 5)) ∨ (n = 65 ∧ tag = 4) := by
  have word (m : Nat) (small : m < 2^64) :
      BitVec.ofNat 64 n = BitVec.ofNat 64 m ↔ n = m := by
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt small] using hn
    · exact congrArg (BitVec.ofNat 64)
  constructor
  · intro h
    have pair : validTag tag = true ∧ (BitVec.ofNat 64 n == expectedLength tag) = true := by
      simpa only [accepts, Bool.and_eq_true] using h
    obtain ⟨valid, len⟩ := pair
    simp only [validTag, Bool.or_eq_true, beq_iff_eq] at valid
    have len := eq_of_beq len
    rcases valid with (((h | h) | h) | h) | h
    · subst tag
      exact .inl ⟨(word 1 (by decide)).mp len, rfl⟩
    · subst tag
      exact .inr (.inl ⟨(word 33 (by decide)).mp len, .inl rfl⟩)
    · subst tag
      exact .inr (.inl ⟨(word 33 (by decide)).mp len, .inr (.inl rfl)⟩)
    · subst tag
      exact .inr (.inr ⟨(word 65 (by decide)).mp len, rfl⟩)
    · subst tag
      exact .inr (.inl ⟨(word 33 (by decide)).mp len, .inr (.inr rfl)⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩)
    all_goals decide +kernel

theorem singleton_zero {bytes : ByteArray} (size : bytes.size = 1)
    (tag : bytes.data[0]? = some 0) : bytes = ⟨#[0]⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · exact size
  · intro i hi hj
    have iz : i = 0 := by change i < bytes.size at hi; omega
    subst i
    exact Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans tag)

theorem accepts_shape {bytes : ByteArray} (positive : 0 < bytes.size)
    (bound : bytes.size < 2^64) :
    accepts (bytes.data[0]?.getD 0).toBitVec (BitVec.ofNat 64 bytes.size) = true ↔
      EncodingShape bytes := by
  have first : bytes.data[0]? = some bytes.data[0] := Array.getElem?_eq_getElem positive
  have tag (v : UInt8) : (bytes.data[0]?.getD 0).toBitVec = v.toBitVec ↔
      bytes.data[0]? = some v := by
    rw [first]
    simp only [Option.getD_some, UInt8.toBitVec_inj, Option.some.injEq]
  rw [accepts_iff _ _ bound]
  constructor
  · rintro (⟨size, h⟩ | ⟨size, h | h | h⟩ | ⟨size, h⟩)
    · exact .inl (singleton_zero size ((tag 0).mp h))
    · exact .inr (.inl ⟨size, .inl ((tag 2).mp h)⟩)
    · exact .inr (.inl ⟨size, .inr (.inl ((tag 3).mp h))⟩)
    · exact .inr (.inl ⟨size, .inr (.inr ((tag 5).mp h))⟩)
    · exact .inr (.inr ⟨size, (tag 4).mp h⟩)
  · rintro (rfl | ⟨size, h | h | h⟩ | ⟨size, h⟩)
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr (.inl ⟨size, .inl ((tag 2).mpr h)⟩)
    · exact .inr (.inl ⟨size, .inr (.inl ((tag 3).mpr h))⟩)
    · exact .inr (.inl ⟨size, .inr (.inr ((tag 5).mpr h))⟩)
    · exact .inr (.inr ⟨size, (tag 4).mpr h⟩)

end P256.Proofs.Sec1.Decode.Header
