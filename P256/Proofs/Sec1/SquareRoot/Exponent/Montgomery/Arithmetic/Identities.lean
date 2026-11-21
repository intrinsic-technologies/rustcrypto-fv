import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Arithmetic.Words

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

theorem bool_eq_of_toNat_eq (a b : Bool) (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

theorem wordCarry_eq (x y : BitVec 64 × Bool)
    (h : x.1.toNat + wordBase*x.2.toNat = y.1.toNat + wordBase*y.2.toNat) : x = y := by
  have hx := x.1.isLt
  have hy := y.1.isLt
  change x.1.toNat + 18446744073709551616*x.2.toNat =
    y.1.toNat + 18446744073709551616*y.2.toNat at h
  apply Prod.ext
  · apply BitVec.eq_of_toNat_eq
    omega
  · apply bool_eq_of_toNat_eq
    omega

theorem adc64_false (a b : BitVec 64) : adc64 a b false = add64 a b := by
  apply wordCarry_eq
  rw [adc64_value, add64_value]
  rfl

theorem add64_comm (a b : BitVec 64) : add64 a b = add64 b a := by
  apply wordCarry_eq
  rw [add64_value, add64_value, Nat.add_comm]

theorem add64_zero (a : BitVec 64) : add64 a 0 = (a, false) := by
  apply wordCarry_eq
  rw [add64_value]
  rfl

end P256.Proofs.Sec1.SquareRoot.Montgomery
