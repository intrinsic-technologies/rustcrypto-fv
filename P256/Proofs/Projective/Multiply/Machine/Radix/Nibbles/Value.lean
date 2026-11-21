import P256.Proofs.Projective.Multiply.Radix.Value

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Proofs.Projective.Multiply.ProjectiveRadix

theorem nibble_even (d i : Nat) : nibble d (2*i) = d / 256 ^ i % 16 := by
  rw [nibble,Nat.pow_mul]

theorem nibble_odd (d i : Nat) : nibble d (2*i+1) = (d / 256 ^ i / 16) % 16 := by
  rw [nibble,Nat.pow_succ,Nat.pow_mul,← Nat.div_div_eq_div_mul]

theorem byte_low_nibble (d i : Nat) :
    BitVec.ofNat 8 (d / 256 ^ i % 256) &&& 15 = BitVec.ofNat 8 (nibble d (2*i)) := by
  have low : ∀ b : BitVec 8, b &&& 15 = BitVec.ofNat 8 (b.toNat % 16) := by decide +kernel
  rw [low,BitVec.toNat_ofNat,nibble_even]
  simp only [show 2^8 = 256 by decide,Nat.mod_mod,
    Nat.mod_mod_of_dvd _ (show 16 ∣ 256 by decide)]

theorem byte_high_nibble (d i : Nat) :
    BitVec.ofNat 8 (d / 256 ^ i % 256) >>> 4 = BitVec.ofNat 8 (nibble d (2*i+1)) := by
  have high : ∀ b : BitVec 8, b >>> 4 = BitVec.ofNat 8 (b.toNat / 16) := by decide +kernel
  rw [high,BitVec.toNat_ofNat,nibble_odd]
  simp only [show 2^8 = 256 by decide,Nat.mod_mod]
  rw [show 256 = 16*16 by decide,Nat.mod_mul_right_div_self]

end P256.Proofs.Projective.Multiply.Machine.Radix
