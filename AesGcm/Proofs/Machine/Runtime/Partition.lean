import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store

namespace AesGcm.Proofs.Machine.Runtime

def alignmentBytes (dst : BitVec 64) : BitVec 64 :=
  ((-(dst.setWidth 32)) &&& 7).setWidth 64

def prefixBytes (dst count : BitVec 64) : BitVec 64 :=
  if count.toNat < (alignmentBytes dst).toNat then count else alignmentBytes dst

theorem alignmentBytes_toNat (dst : BitVec 64) :
    (alignmentBytes dst).toNat = (8 - dst.toNat % 8) % 8 := by
  unfold alignmentBytes
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change ((-(dst.setWidth 32)).toNat &&& (2^3 - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_neg, BitVec.toNat_setWidth]
  have := dst.isLt
  omega

theorem prefixBytes_toNat (dst count : BitVec 64) :
    (prefixBytes dst count).toNat = min ((8 - dst.toNat % 8) % 8) count.toNat := by
  unfold prefixBytes
  rw [alignmentBytes_toNat]
  split
  · omega
  · rw [alignmentBytes_toNat]
    omega

theorem prefixBytes_le (dst count : BitVec 64) :
    (prefixBytes dst count).toNat ≤ count.toNat := by
  rw [prefixBytes_toNat]
  omega

theorem prefixBytes_align (dst count : BitVec 64)
    (h : (prefixBytes dst count).toNat < count.toNat) :
    (dst.toNat + (prefixBytes dst count).toNat) % 8 = 0 := by
  rw [prefixBytes_toNat] at h ⊢
  omega

theorem middleBytes_toNat (dst count : BitVec 64) :
    ((count - prefixBytes dst count) >>> 3).toNat =
      (count.toNat - (prefixBytes dst count).toNat) / 8 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  have := prefixBytes_le dst count
  have := count.isLt
  omega

theorem tailBytes_toNat (dst count : BitVec 64) :
    (((count - prefixBytes dst count).setWidth 32 &&& 7).setWidth 64).toNat =
      (count.toNat - (prefixBytes dst count).toNat) % 8 := by
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_and]
  change ((count - prefixBytes dst count).setWidth 32).toNat &&& (2^3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, BitVec.toNat_sub]
  have := prefixBytes_le dst count
  have := count.isLt
  omega

end AesGcm.Proofs.Machine.Runtime
