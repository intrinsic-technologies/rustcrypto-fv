import Std.Tactic

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd


theorem signed64_natAbs_le (x : BitVec 64) : x.toInt.natAbs ≤ 2^63 := by
  have hlo := BitVec.le_toInt x
  have hhi := BitVec.toInt_lt (x := x)
  rcases Int.natAbs_eq x.toInt with h | h <;> omega

theorem signed256_product_lt {f : Int} (u : BitVec 64) (hf : f.natAbs < 2^256) :
    (f*u.toInt).natAbs < 2^319 := by
  rw [Int.natAbs_mul]
  have hu := signed64_natAbs_le u
  have hle := Nat.mul_le_mul_left f.natAbs hu
  have hlt := Nat.mul_lt_mul_of_pos_right hf (by decide : 0 < (2 : Nat)^63)
  have he : (2 : Nat)^256*2^63=2^319 := by decide +kernel
  rw [he] at hlt
  exact Nat.lt_of_le_of_lt hle hlt

end P256.Proofs.Field.Inverse.SafeGcd
