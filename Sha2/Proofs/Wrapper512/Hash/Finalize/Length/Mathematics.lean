import Sha2.Proofs.Wrapper512.Hash.Finalize.State

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Length

open Sha2.Proofs.Common.Instructions

theorem low_word (n : Nat) :
    ((((BitVec.ofNat 64 (n % 128)).setWidth 8).setWidth 32 <<< 3).setWidth 64 |||
      ((BitVec.ofNat 64 (n / 128)) <<< 10)) = BitVec.ofNat 64 (8 * n) := by
  have remBound : n % 128 < 128 := Nat.mod_lt _ (by decide)
  have low : (((BitVec.ofNat 64 (n % 128)).setWidth 8).setWidth 32 <<< 3).setWidth 64 =
      BitVec.ofNat 64 (8 * (n % 128)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.reducePow]
    omega
  rw [low]
  have high : ((BitVec.ofNat 64 (n / 128)) <<< 10) =
      BitVec.ofNat 64 (1024 * (n / 128)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    simp only [BitVec.twoPow, BitVec.ofNat_mul, Nat.mul_comm]
    rfl
  rw [high, ← BitVec.ofNat_or]
  have join := Nat.two_pow_add_eq_or_of_lt (i := 10) (b := 8 * (n % 128)) (by omega) (n / 128)
  rw [Nat.or_comm, ← join]
  congr 1
  omega

theorem high_word (n : Nat) :
    ((BitVec.ofNat 64 ((n / 128) / 2^64) ++ BitVec.ofNat 64 (n / 128)).extractLsb' 54 64) =
      BitVec.ofNat 64 ((8 * n) / 2^64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_append, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow]
  have join := Nat.two_pow_add_eq_or_of_lt (i := 64)
    (b := n / 128 % 2^64) (Nat.mod_lt _ (by decide)) (n / 128 / 2^64 % 2^64)
  simp only [Nat.reducePow] at join
  rw [Nat.mul_comm _ 18446744073709551616, ← join]
  omega

end Sha2.Proofs.Wrapper512.Hash.Finalize.Length
