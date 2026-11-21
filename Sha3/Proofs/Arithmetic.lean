import Std

namespace Sha3.Proofs

theorem sha3_224_reciprocal_div (n : Nat) (hn : n < 2 ^ 32) :
    (n * 0xe38e38e38e38e38f / 2 ^ 64) / 128 = n / 144 := by
  omega

theorem sha3_256_reciprocal_div (n : Nat) (hn : n < 2 ^ 32) :
    (n * 0xf0f0f0f0f0f0f0f1 / 2 ^ 64) / 128 = n / 136 := by
  omega

theorem sha3_384_reciprocal_div (n : Nat) (hn : n < 2 ^ 32) :
    (n * 0x4ec4ec4ec4ec4ec5 / 2 ^ 64) / 32 = n / 104 := by
  omega

theorem sha3_512_reciprocal_div (n : Nat) (hn : n < 2 ^ 32) :
    (n * 0xe38e38e38e38e38f / 2 ^ 64) / 64 = n / 72 := by
  omega

theorem mulHigh64_toNat (x y : BitVec 64) :
    (((x.setWidth 128) * (y.setWidth 128)).extractLsb' 64 64).toNat =
      x.toNat * y.toNat / 2 ^ 64 := by
  have hp := BitVec.toNat_mul_toNat_lt (x := x) (y := y)
  have hq : x.toNat * y.toNat / 2 ^ 64 < 2 ^ 64 := by omega
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_mul,
    BitVec.toNat_setWidth_of_le (show 64 ≤ 128 by omega),
    Nat.mod_eq_of_lt hp, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hq]

theorem mulHigh64_eq (x y : BitVec 64) :
    ((x.setWidth 128) * (y.setWidth 128)).extractLsb' 64 64 =
      BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) :=
  (BitVec.toNat_eq_nat.mp (mulHigh64_toNat x y)).2

theorem and_highMask_toNat {w : Nat} (x : BitVec w) (s : Nat) :
    (x &&& (BitVec.allOnes w <<< s)).toNat = (x.toNat / 2 ^ s * 2 ^ s) := by
  rw [← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) x.isLt)

def sha3_224_fullBlockBytes (n : BitVec 64) : BitVec 64 :=
  let high := ((n.setWidth 128) * ((0xe38e38e38e38e38f : BitVec 64).setWidth 128)).extractLsb' 64 64
  let aligned := high >>> 3 &&& 0xfffffffffffffff0
  aligned + aligned * 8

def sha3_256_fullBlockBytes (n : BitVec 64) : BitVec 64 :=
  let high := ((n.setWidth 128) * ((0xf0f0f0f0f0f0f0f1 : BitVec 64).setWidth 128)).extractLsb' 64 64
  (high &&& (0xffffffffffffff80 : BitVec 64)) + (high >>> 7) * 8

def sha3_384_fullBlockBytes (n : BitVec 64) : BitVec 64 :=
  let high := ((n.setWidth 128) * ((0x4ec4ec4ec4ec4ec5 : BitVec 64).setWidth 128)).extractLsb' 64 64
  (high >>> 5) * 104

def sha3_512_fullBlockBytes (n : BitVec 64) : BitVec 64 :=
  let high := ((n.setWidth 128) * ((0xe38e38e38e38e38f : BitVec 64).setWidth 128)).extractLsb' 64 64
  let aligned := high >>> 3 &&& 0xfffffffffffffff8
  aligned + aligned * 8

theorem sha3_224_fullBlockBytes_toNat (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    (sha3_224_fullBlockBytes n).toNat = 144 * (n.toNat / 144) := by
  let high := ((n.setWidth 128) *
    ((0xe38e38e38e38e38f : BitVec 64).setWidth 128)).extractLsb' 64 64
  let aligned := high >>> 3 &&& (0xfffffffffffffff0 : BitVec 64)
  change (aligned + aligned * 8).toNat = _
  have hh : high.toNat = n.toNat * 0xe38e38e38e38e38f / 2 ^ 64 := by
    exact mulHigh64_toNat n 0xe38e38e38e38e38f
  have hmask : (0xfffffffffffffff0 : BitVec 64) = BitVec.allOnes 64 <<< 4 := by
    decide +kernel
  have ha : aligned.toNat = 16 * (n.toNat / 144) := by
    dsimp only [aligned]
    rw [hmask, and_highMask_toNat, BitVec.toNat_ushiftRight, hh, Nat.shiftRight_eq_div_pow]
    change n.toNat * 0xe38e38e38e38e38f / 2 ^ 64 / 8 / 16 * 16 = _
    have hdiv : n.toNat * 0xe38e38e38e38e38f / 2 ^ 64 / 8 / 16 = n.toNat / 144 := by
      simpa only [Nat.div_div_eq_div_mul] using sha3_224_reciprocal_div n.toNat hn
    rw [hdiv, Nat.mul_comm]
  rw [BitVec.toNat_add, BitVec.toNat_mul, ha]
  change (16 * (n.toNat / 144) + (16 * (n.toNat / 144) * 8) % 2 ^ 64) % 2 ^ 64 = _
  omega

theorem sha3_256_fullBlockBytes_toNat (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    (sha3_256_fullBlockBytes n).toNat = 136 * (n.toNat / 136) := by
  let high := ((n.setWidth 128) *
    ((0xf0f0f0f0f0f0f0f1 : BitVec 64).setWidth 128)).extractLsb' 64 64
  change ((high &&& (0xffffffffffffff80 : BitVec 64)) + (high >>> 7) * 8).toNat = _
  have hh : high.toNat = n.toNat * 0xf0f0f0f0f0f0f0f1 / 2 ^ 64 := by
    exact mulHigh64_toNat n 0xf0f0f0f0f0f0f0f1
  have hmask : (0xffffffffffffff80 : BitVec 64) = BitVec.allOnes 64 <<< 7 := by
    decide +kernel
  rw [BitVec.toNat_add, BitVec.toNat_mul, hmask, and_highMask_toNat,
    BitVec.toNat_ushiftRight, hh, Nat.shiftRight_eq_div_pow]
  change ((n.toNat * 0xf0f0f0f0f0f0f0f1 / 2 ^ 64 / 128) * 128 +
    ((n.toNat * 0xf0f0f0f0f0f0f0f1 / 2 ^ 64 / 128) * 8) % 2 ^ 64) % 2 ^ 64 = _
  rw [sha3_256_reciprocal_div n.toNat hn]
  omega

theorem sha3_384_fullBlockBytes_toNat (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    (sha3_384_fullBlockBytes n).toNat = 104 * (n.toNat / 104) := by
  let high := ((n.setWidth 128) *
    ((0x4ec4ec4ec4ec4ec5 : BitVec 64).setWidth 128)).extractLsb' 64 64
  change ((high >>> 5) * 104).toNat = _
  have hh : high.toNat = n.toNat * 0x4ec4ec4ec4ec4ec5 / 2 ^ 64 := by
    exact mulHigh64_toNat n 0x4ec4ec4ec4ec4ec5
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, hh, Nat.shiftRight_eq_div_pow]
  change ((n.toNat * 0x4ec4ec4ec4ec4ec5 / 2 ^ 64 / 32) * 104) % 2 ^ 64 = _
  rw [sha3_384_reciprocal_div n.toNat hn]
  omega

theorem sha3_512_fullBlockBytes_toNat (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    (sha3_512_fullBlockBytes n).toNat = 72 * (n.toNat / 72) := by
  let high := ((n.setWidth 128) *
    ((0xe38e38e38e38e38f : BitVec 64).setWidth 128)).extractLsb' 64 64
  let aligned := high >>> 3 &&& (0xfffffffffffffff8 : BitVec 64)
  change (aligned + aligned * 8).toNat = _
  have hh : high.toNat = n.toNat * 0xe38e38e38e38e38f / 2 ^ 64 := by
    exact mulHigh64_toNat n 0xe38e38e38e38e38f
  have hmask : (0xfffffffffffffff8 : BitVec 64) = BitVec.allOnes 64 <<< 3 := by
    decide +kernel
  have ha : aligned.toNat = 8 * (n.toNat / 72) := by
    dsimp only [aligned]
    rw [hmask, and_highMask_toNat, BitVec.toNat_ushiftRight, hh, Nat.shiftRight_eq_div_pow]
    change n.toNat * 0xe38e38e38e38e38f / 2 ^ 64 / 8 / 8 * 8 = _
    have hdiv : n.toNat * 0xe38e38e38e38e38f / 2 ^ 64 / 8 / 8 = n.toNat / 72 := by
      simpa only [Nat.div_div_eq_div_mul] using sha3_512_reciprocal_div n.toNat hn
    rw [hdiv, Nat.mul_comm]
  rw [BitVec.toNat_add, BitVec.toNat_mul, ha]
  change (8 * (n.toNat / 72) + (8 * (n.toNat / 72) * 8) % 2 ^ 64) % 2 ^ 64 = _
  omega

theorem sub_fullBlockBytes_toNat (n bytes : BitVec 64) (rate : Nat)
    (hbytes : bytes.toNat = rate * (n.toNat / rate)) :
    (n - bytes).toNat = n.toNat % rate := by
  have hdiv := Nat.mod_add_div n.toNat rate
  have hle : bytes ≤ n := by
    rw [BitVec.le_def, hbytes]
    omega
  rw [BitVec.toNat_sub_of_le hle, hbytes]
  omega

theorem sha3_224_fullBlockBytes_eq (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    sha3_224_fullBlockBytes n = BitVec.ofNat 64 (144 * (n.toNat / 144)) :=
  (BitVec.toNat_eq_nat.mp (sha3_224_fullBlockBytes_toNat n hn)).2

theorem sha3_224_remaining_toNat (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    (n - sha3_224_fullBlockBytes n).toNat = n.toNat % 144 :=
  sub_fullBlockBytes_toNat n _ 144 (sha3_224_fullBlockBytes_toNat n hn)

theorem sha3_224_remaining (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    n - sha3_224_fullBlockBytes n = BitVec.ofNat 64 (n.toNat % 144) :=
  (BitVec.toNat_eq_nat.mp (sha3_224_remaining_toNat n hn)).2

theorem sha3_256_fullBlockBytes_eq (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    sha3_256_fullBlockBytes n = BitVec.ofNat 64 (136 * (n.toNat / 136)) :=
  (BitVec.toNat_eq_nat.mp (sha3_256_fullBlockBytes_toNat n hn)).2

theorem sha3_256_remaining_toNat (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    (n - sha3_256_fullBlockBytes n).toNat = n.toNat % 136 :=
  sub_fullBlockBytes_toNat n _ 136 (sha3_256_fullBlockBytes_toNat n hn)

theorem sha3_256_remaining (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    n - sha3_256_fullBlockBytes n = BitVec.ofNat 64 (n.toNat % 136) :=
  (BitVec.toNat_eq_nat.mp (sha3_256_remaining_toNat n hn)).2

theorem sha3_384_fullBlockBytes_eq (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    sha3_384_fullBlockBytes n = BitVec.ofNat 64 (104 * (n.toNat / 104)) :=
  (BitVec.toNat_eq_nat.mp (sha3_384_fullBlockBytes_toNat n hn)).2

theorem sha3_384_remaining_toNat (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    (n - sha3_384_fullBlockBytes n).toNat = n.toNat % 104 :=
  sub_fullBlockBytes_toNat n _ 104 (sha3_384_fullBlockBytes_toNat n hn)

theorem sha3_384_remaining (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    n - sha3_384_fullBlockBytes n = BitVec.ofNat 64 (n.toNat % 104) :=
  (BitVec.toNat_eq_nat.mp (sha3_384_remaining_toNat n hn)).2

theorem sha3_512_fullBlockBytes_eq (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    sha3_512_fullBlockBytes n = BitVec.ofNat 64 (72 * (n.toNat / 72)) :=
  (BitVec.toNat_eq_nat.mp (sha3_512_fullBlockBytes_toNat n hn)).2

theorem sha3_512_remaining_toNat (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    (n - sha3_512_fullBlockBytes n).toNat = n.toNat % 72 :=
  sub_fullBlockBytes_toNat n _ 72 (sha3_512_fullBlockBytes_toNat n hn)

theorem sha3_512_remaining (n : BitVec 64) (hn : n.toNat < 2 ^ 32) :
    n - sha3_512_fullBlockBytes n = BitVec.ofNat 64 (n.toNat % 72) :=
  (BitVec.toNat_eq_nat.mp (sha3_512_remaining_toNat n hn)).2

theorem padding_shiftCount_toNat (remaining : BitVec 8) :
    (((remaining.setWidth 32 * 8).setWidth 8) &&& (63 : BitVec 8)).toNat =
      8 * (remaining.toNat % 8) := by
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_mul,
    BitVec.toNat_setWidth_of_le (show 8 ≤ 32 by omega)]
  change ((remaining.toNat * 8 % 2 ^ 32) % 256 &&& (2 ^ 6 - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  have hr := remaining.isLt
  omega

theorem padding_shift_eq (remaining : BitVec 8) :
    (6 : BitVec 64) <<<
      ((((remaining.setWidth 32 * 8).setWidth 8) &&& (63 : BitVec 8)).toNat) =
        (6 : BitVec 64) <<< (8 * (remaining.toNat % 8)) := by
  rw [padding_shiftCount_toNat]

theorem padding_shift_toNat (remaining : BitVec 8) :
    ((6 : BitVec 64) <<<
      ((((remaining.setWidth 32 * 8).setWidth 8) &&& (63 : BitVec 8)).toNat)).toNat =
        6 * 2 ^ (8 * (remaining.toNat % 8)) := by
  rw [padding_shift_eq, BitVec.toNat_shiftLeft]
  change (6 <<< (8 * (remaining.toNat % 8))) % 2 ^ 64 = _
  rw [Nat.shiftLeft_eq]
  have he : 8 * (remaining.toNat % 8) ≤ 56 := by omega
  have hp : 2 ^ (8 * (remaining.toNat % 8)) ≤ 2 ^ 56 :=
    Nat.pow_le_pow_right (by omega) he
  apply Nat.mod_eq_of_lt
  omega

theorem padding_laneOffset_toNat (remaining : BitVec 8) :
    ((remaining.setWidth 32) &&& (248 : BitVec 32)).toNat =
      remaining.toNat / 8 * 8 := by
  have hwide : (248 : BitVec 32) = (248 : BitVec 8).setWidth 32 := by decide +kernel
  have hmask : (248 : BitVec 8) = BitVec.allOnes 8 <<< 3 := by decide +kernel
  rw [hwide, ← BitVec.setWidth_and,
    BitVec.toNat_setWidth_of_le (show 8 ≤ 32 by omega), hmask, and_highMask_toNat]

end Sha3.Proofs
