namespace Sha1.Proofs.Buffered.DigestPrepare.Long

theorem fullBlockMask_toNat (x : BitVec 64) (hx : x.toNat < 2^63) :
    (x &&& 0x7fffffffffffffc0).toNat = x.toNat / 64 * 64 := by
  rw [BitVec.toNat_and]
  change x.toNat &&& 9223372036854775744 = x.toNat / 64 * 64
  have hdiv := Nat.and_div_two_pow (a := x.toNat) (b := 9223372036854775744) (n := 6)
  change (x.toNat &&& 9223372036854775744) / 64 =
    x.toNat / 64 &&& (2^57 - 1) at hdiv
  rw [Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)] at hdiv
  have hmod := Nat.and_mod_two_pow (a := x.toNat) (b := 9223372036854775744) (n := 6)
  change (x.toNat &&& 9223372036854775744) % 64 = x.toNat % 64 &&& 0 at hmod
  rw [Nat.and_zero] at hmod
  omega

theorem tailMask_toNat (x : BitVec 64) :
    ((x.setWidth 32 &&& 63).setWidth 64).toNat = x.toNat % 64 := by
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change (x.toNat % 2^32) &&& (2^6 - 1) = x.toNat % 64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

end Sha1.Proofs.Buffered.DigestPrepare.Long
