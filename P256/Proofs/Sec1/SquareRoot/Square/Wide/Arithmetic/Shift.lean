import P256.Proofs.Field.Schoolbook.WordSpecs
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Arithmetic.DoubleOperation
set_option autoImplicit false

open P256.Proofs.Field.Montgomery (wordBase)
open P256.Proofs.Common.Instructions.ShiftLeft (shldOneResult)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide


open X86Proofs

theorem shld_concat_bound (x y : BitVec 64) : x.toNat * 2^64 + y.toNat < 2^128 := by
  have hx := x.isLt
  have hy := y.isLt
  omega

theorem shld_concat_div (x y : Nat) :
    (x * 2^64 + y) / 2^63 = 2*x + y / 2^63 := by
  rw [show x * 2^64 = 2^63 * (2*x) by omega,
    Nat.mul_add_div (by decide +kernel)]

theorem shld_double_mod (x y : Nat) (hx : x < 2^64) (hy : y < 2^64) :
    (2*x + y/2^63) % 2^64 + 2^64*(x/2^63) = 2*x + y/2^63 := by
  have hybit : y / 2^63 < 2 := (Nat.div_lt_iff_lt_mul (by decide +kernel)).mpr (by omega)
  by_cases h : x < 2^63
  · rw [Nat.div_eq_of_lt h, Nat.mul_zero, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega)]
  · rw [show x / 2^63 = 1 from Nat.div_eq_of_lt_le (by omega) (by omega)]
    rw [Nat.mod_eq_sub_mod (by omega : 2^64 ≤ 2*x+y/2^63),
      Nat.mod_eq_of_lt (by omega)]
    omega

theorem extract_shift_add_toNat (x y n s m : Nat) :
    ((BitVec.ofNat m ((x <<< n) + y)).extractLsb' s n).toNat =
      (((x * 2^n + y) % 2^m) / 2^s) % 2^n := by
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

theorem ushiftRight_toNat_div {n : Nat} (x : BitVec n) (i : Nat) :
    (x >>> i).toNat = x.toNat / 2^i := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shldOneResult_toNat (x y : BitVec 64) :
    (shldOneResult x y).toNat + wordBase * (x >>> 63).toNat =
      2 * x.toNat + (y >>> 63).toNat := by
  rw [shldOneResult, extract_shift_add_toNat, ushiftRight_toNat_div, ushiftRight_toNat_div]
  rw [Nat.mod_eq_of_lt (shld_concat_bound x y), shld_concat_div]
  exact shld_double_mod x.toNat y.toNat x.isLt y.isLt

theorem addSpec_self_toNat (x : BitVec 64) :
    (addSpec x x).1.toNat + wordBase * (x >>> 63).toNat = 2*x.toNat := by
  change (x+x).toNat + wordBase * (x >>> 63).toNat = _
  rw [BitVec.toNat_add, ushiftRight_toNat_div]
  have h := shld_double_mod x.toNat 0 x.isLt (by decide +kernel)
  simpa only [Nat.zero_div, Nat.add_zero, Nat.two_mul, wordBase] using h

end P256.Proofs.Sec1.SquareRoot.Square.Wide
