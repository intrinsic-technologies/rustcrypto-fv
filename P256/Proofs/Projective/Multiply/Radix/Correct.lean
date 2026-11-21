import P256.Proofs.Projective.Multiply.Radix.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.ScalarMul

open ProjectiveRadix

def radixPrefix (d i : Nat) : Nat := d / 16 ^ i + carry d i

theorem radixPrefix_zero (d : Nat) : radixPrefix d 0 = d := by
  simp only [radixPrefix, Nat.pow_zero, Nat.div_one, carry, Nat.add_zero]

theorem radixPrefix_initial (d : Nat) (hbound : d < 2 ^ 256) :
    digitInt d 64 = (radixPrefix d 64 : Int) := by
  have hbound' : d < 16 ^ 64 := by
    simpa only [show 16 ^ 64 = 2 ^ 256 by decide +kernel] using hbound
  simp only [radixPrefix, Nat.div_eq_of_lt hbound', Nat.zero_add, digitInt_last]

theorem radixPrefix_step (d i : Nat) (hi : i < 64) :
    ((16 * radixPrefix d (i + 1) : Nat) : Int) + digitInt d i = radixPrefix d i := by
  have hq := nibble_quotient d i
  simp only [radixPrefix, digitInt, ite_eq_left hi, centeredDigit]
  omega

end P256.Proofs.Projective.Multiply.ScalarMul
