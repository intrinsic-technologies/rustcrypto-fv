import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace Sha1.Proofs.Wrapper.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs


theorem tail_zero_count (tail : Nat) (bound : tail < 64) :
    BitVec.ofNat 64 tail ^^^ 63 = BitVec.ofNat 64 (63 - tail) := by
  have computed : ∀ tail : Fin 64,
      BitVec.ofNat 64 tail.val ^^^ 63 = BitVec.ofNat 64 (63 - tail.val) := by
    decide +kernel
  exact computed ⟨tail, bound⟩


theorem tail_shift_or_blocks (n : Nat) :
    (((BitVec.ofNat 32 (n % 64)) <<< 3).setWidth 64 |||
      ((BitVec.ofNat 64 (n / 64)) <<< 9)) = BitVec.ofNat 64 (8 * n) := by
  have remBound : n % 64 < 64 := Nat.mod_lt _ (by decide)
  have low : ((BitVec.ofNat 32 (n % 64)) <<< 3).setWidth 64 =
      BitVec.ofNat 64 (8 * (n % 64)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.reducePow]
    omega
  rw [low]
  have high : ((BitVec.ofNat 64 (n / 64)) <<< 9) =
      BitVec.ofNat 64 (512 * (n / 64)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    simp only [BitVec.twoPow, BitVec.ofNat_mul, Nat.mul_comm]
    rfl
  rw [high, ← BitVec.ofNat_or]
  have join := Nat.two_pow_add_eq_or_of_lt (i := 9) (b := 8 * (n % 64)) (by omega) (n / 64)
  rw [Nat.or_comm, ← join]
  congr 1
  omega

end Sha1.Proofs.Wrapper.Hash
