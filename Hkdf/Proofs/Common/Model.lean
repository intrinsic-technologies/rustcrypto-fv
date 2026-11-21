import Hkdf.Spec.RFC5869

namespace Hkdf.Proofs.Common

open Standards.RFC
open Hkdf.Spec

theorem extract_sha256_size (salt : Option ByteArray) (ikm : ByteArray) :
    (RFC5869.extract .sha256 salt ikm).size = 32 := by
  simp only [RFC5869.extract, HKDF.extract, HMAC.hmac, HKDF.Hash.sha256,
    Standards.NIST.SHA2.SHA256.hashBytes, ByteArray.size, Vector.size_toArray]

theorem expand_sha256_none_iff (prk info : ByteArray) (length : Nat) :
    HKDF.expand .sha256 prk info length = none ↔ 8160 < length := by
  unfold HKDF.expand
  change (if length > 8160 then none else _) = none ↔ 8160 < length
  split <;> simp_all only [Option.some_ne_none]

theorem expand_sha256_zero (prk info : ByteArray) :
    HKDF.expand .sha256 prk info 0 = some ByteArray.empty := by
  simp [HKDF.expand, HKDF.Hash.sha256]

theorem expandFromPrk_sha256_invalidPrkLength (prk info : ByteArray) (length : Nat)
    (short : prk.size < 32) :
    RFC5869.expandFromPrk .sha256 prk info length = .error .invalidPrkLength := by
  simp only [RFC5869.expandFromPrk, show HKDF.Hash.sha256.hashLen = 32 from rfl,
    short, ↓reduceIte]

theorem expandFromPrk_sha256_invalidPrkLength_iff (prk info : ByteArray) (length : Nat) :
    RFC5869.expandFromPrk .sha256 prk info length = .error .invalidPrkLength ↔
      prk.size < 32 := by
  unfold RFC5869.expandFromPrk
  simp only [show HKDF.Hash.sha256.hashLen = 32 from rfl]
  split
  · simp_all only
  · cases HKDF.expand .sha256 prk info length <;> simp_all

theorem expandFromPrk_sha256_invalidLength_iff (prk info : ByteArray) (length : Nat) :
    RFC5869.expandFromPrk .sha256 prk info length = .error .invalidLength ↔
      32 ≤ prk.size ∧ 8160 < length := by
  unfold RFC5869.expandFromPrk
  simp only [show HKDF.Hash.sha256.hashLen = 32 from rfl]
  split
  · rename_i short
    simp only [Except.error.injEq, reduceCtorEq, false_iff, not_and]
    omega
  · rename_i enough
    have bound : 32 ≤ prk.size := by omega
    cases result : HKDF.expand .sha256 prk info length with
    | none =>
      have large := (expand_sha256_none_iff prk info length).mp result
      simp only [bound, large, and_self]
    | some okm =>
      have small : ¬8160 < length := by
        intro large
        have := (expand_sha256_none_iff prk info length).mpr large
        rw [result] at this
        contradiction
      simp only [reduceCtorEq, bound, small, and_false]

theorem expandFromPrk_sha256_zero (prk info : ByteArray) (enough : 32 ≤ prk.size) :
    RFC5869.expandFromPrk .sha256 prk info 0 = .ok ByteArray.empty := by
  have not_short : ¬prk.size < 32 := by omega
  simp only [RFC5869.expandFromPrk, show HKDF.Hash.sha256.hashLen = 32 from rfl,
    not_short, ↓reduceIte, expand_sha256_zero]

theorem expandFromPrk_sha256_ok_iff (prk info okm : ByteArray) (length : Nat) :
    RFC5869.expandFromPrk .sha256 prk info length = .ok okm ↔
      32 ≤ prk.size ∧ HKDF.expand .sha256 prk info length = some okm := by
  unfold RFC5869.expandFromPrk
  simp only [show HKDF.Hash.sha256.hashLen = 32 from rfl]
  split
  · rename_i short
    have not_enough : ¬32 ≤ prk.size := by omega
    simp only [reduceCtorEq, not_enough, false_and]
  · rename_i enough
    have bound : 32 ≤ prk.size := by omega
    cases HKDF.expand .sha256 prk info length <;> simp [bound]

end Hkdf.Proofs.Common
