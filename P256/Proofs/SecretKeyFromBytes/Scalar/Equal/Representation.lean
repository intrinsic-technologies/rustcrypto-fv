import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Loop
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.SecretKeyFromBytes.Scalar.Equal

open X86 X86.Machine X86Proofs

theorem prefixEqual_nat256 {s : RamState} {x y : Nat}
    (hx : Nat256At s (s.regValue .rdi) x)
    (hy : Nat256At s (s.regValue .rdx) y) :
    prefixEqual s 4 = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  rw [prefixEqual_iff, decide_eq_true_eq]
  have h (j : Nat) (hj : j < 4) :
      limb s .rdi j = limb s .rdx j ↔
        BitVec.ofNat 64 (x / 2^(64*j)) = BitVec.ofNat 64 (y / 2^(64*j)) := by
    rw [limb, limb, hx.memLoad_limb j hj, hy.memLoad_limb j hj]
  constructor
  · intro he
    have h0 := (h 0 (by decide)).mp (he 0 (by decide))
    have h1 := (h 1 (by decide)).mp (he 1 (by decide))
    have h2 := (h 2 (by decide)).mp (he 2 (by decide))
    have h3 := (h 3 (by decide)).mp (he 3 (by decide))
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h0
    rw [← limbs_ofNat_toNat x hx.1, ← limbs_ofNat_toNat y hy.1, h0, h1, h2, h3]
  · rintro rfl j hj
    exact (h j hj).mpr rfl

end P256.Proofs.SecretKeyFromBytes.Scalar.Equal
