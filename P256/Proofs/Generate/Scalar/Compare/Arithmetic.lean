import P256.Proofs.Generate.Scalar.Compare.Common

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open Prelude P256.Proofs.SecretKeyFromBytes.Scalar

theorem third_word_eq (x b : BitVec 64) (hb : b = 0 ∨ b = 1) :
    (-b).sshiftRight 63 + x + 1 = ((b - 1) >>> 63) + x := by
  rcases hb with rfl | rfl
  · change 0#64 + x + 1#64 = 1#64 + x
    rw [BitVec.zero_add, BitVec.add_comm]
  · change (-1#64) + x + 1#64 = 0#64 + x
    rw [BitVec.add_comm (-1#64), BitVec.add_assoc,
      show (-1#64) + 1#64 = 0#64 by decide +kernel, BitVec.add_zero, BitVec.zero_add]

theorem third_word_shift_eq (x y : BitVec 64) :
    (-(y >>> 63)).sshiftRight 63 + x + 1 = (((y >>> 63) - 1) >>> 63) + x := by
  apply third_word_eq
  apply eq_zero_or_one
  rw [BitVec.toNat_ushiftRight]
  have := y.isLt
  rw [Nat.shiftRight_eq_div_pow]
  omega

end P256.Proofs.Generate.Scalar
