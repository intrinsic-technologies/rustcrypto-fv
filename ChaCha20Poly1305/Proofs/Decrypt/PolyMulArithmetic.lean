import ChaCha20Poly1305.Proofs.Decrypt.PolyMul
import ChaCha20Poly1305.Proofs.Decrypt.PolyBounds

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul

def asLimbs (v : Vector (BitVec 32) 5) : Limbs :=
  ⟨v[0].toNat, v[1].toNat, v[2].toNat, v[3].toNat, v[4].toNat⟩

def added (x : Input) := (asLimbs x.acc).plus (fullBlock x.block.toNat)

def products (x : Input) := convolution (added x) (asLimbs x.r)

def output (x : Input) : Vector (BitVec 32) 5 :=
  #v[v101c97 x,v101c94 x,v101ca5 x,v101cb0 x,v101cba x]

private theorem masked (x : BitVec 32) : (x &&& 67108863).toNat = x.toNat % B :=
  Nat.and_two_pow_sub_one_eq_mod _ 26

private theorem maskedLeft (x : BitVec 32) : (67108863 &&& x).toNat = x.toNat % B := by
  rw [BitVec.and_comm, masked]

set_option linter.unusedSimpArgs false

variable {x : Input} (ha : (asLimbs x.acc).Bounded) (hr : (asLimbs x.r).Tight)

include ha in
private theorem add0 : (v101b05 x).toNat = (added x).x0 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  have hb := x.block.isLt
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  simp only [v101b05, v101b02, added, asLimbs, Limbs.plus, fullBlock, splitLimbs,
    masked, maskedLeft, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, B, Nat.reducePow, Nat.reduceMod] 
  omega

include ha in
private theorem add1 : (v101b19 x).toNat = (added x).x1 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  have hb := x.block.isLt
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  simp only [v101b19, v101b13, v101b10, added, asLimbs, Limbs.plus, fullBlock, splitLimbs,
    masked, maskedLeft, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, B, Nat.reducePow, Nat.reduceMod] 
  omega

include ha in
private theorem add2 : (v101b28 x).toNat = (added x).x2 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  have hb := x.block.isLt
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  simp only [v101b28, v101b21, v101b1d, added, asLimbs, Limbs.plus, fullBlock, splitLimbs,
    masked, maskedLeft, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, B, Nat.reducePow, Nat.reduceMod] 
  omega

include ha in
private theorem add3 : (v101b32 x).toNat = (added x).x3 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  have hb := x.block.isLt
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  simp only [v101b32, v101b2f, added, asLimbs, Limbs.plus, fullBlock, splitLimbs,
    masked, maskedLeft, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, B, Nat.reducePow, Nat.reduceMod] 
  omega

include ha in
private theorem add4 : (v101b40 x).toNat = (added x).x4 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := ha
  have hb := x.block.isLt
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  have top : ((16777216 : Nat) : BitVec 32).toNat = 16777216 := rfl
  simp only [top, v101b40, v101b3c, v101b39, added, asLimbs, Limbs.plus, fullBlock, splitLimbs,
    masked, maskedLeft, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, B, Nat.reducePow, Nat.reduceMod] 
  omega

include hr in
private theorem scale1 : (v101b6b x).toNat = 5 * x.r[1].toNat := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := hr
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  simp only [v101b6b, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reducePow]
  omega

include hr in
private theorem scale2 : (v101ae9 x).toNat = 5 * x.r[2].toNat := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := hr
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  simp only [v101ae9, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reducePow]
  omega

include hr in
private theorem scale3 : (v101af1 x).toNat = 5 * x.r[3].toNat := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := hr
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  simp only [v101af1, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reducePow]
  omega

include hr in
private theorem scale4 : (v101af9 x).toNat = 5 * x.r[4].toNat := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := hr
  simp only [asLimbs, B, Nat.reducePow] at h0 h1 h2 h3 h4
  simp only [v101af9, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reducePow]
  omega

include ha hr in
theorem product0 : v101b74 x = BitVec.ofNat 64 (products x).x0 := by
  simp only [v101b74, v101b70, v101b64, v101b61, v101b5d, v101b56, v101b50, v101b4c, v101b45, ← BitVec.ofNat_toNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat,
    add0 ha, add1 ha, add2 ha, add3 ha, add4 ha, scale1 hr, scale2 hr, scale3 hr, scale4 hr]
  apply congrArg (BitVec.ofNat 64)
  simp only [products, convolution, asLimbs]
  grind

include ha hr in
theorem product1 : v101bac x = BitVec.ofNat 64 (products x).x1 := by
  simp only [v101bac, v101ba8, v101ba0, v101b9d, v101b99, v101b8e, v101b88, v101b81, v101b7a, ← BitVec.ofNat_toNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat,
    add0 ha, add1 ha, add2 ha, add3 ha, add4 ha, scale1 hr, scale2 hr, scale3 hr, scale4 hr]
  apply congrArg (BitVec.ofNat 64)
  simp only [products, convolution, asLimbs]
  grind

include ha hr in
theorem product2 : v101be5 x = BitVec.ofNat 64 (products x).x2 := by
  simp only [v101be5, v101be1, v101bdb, v101bd8, v101bd4, v101bcd, v101bc7, v101bc3, v101bbc, ← BitVec.ofNat_toNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat,
    add0 ha, add1 ha, add2 ha, add3 ha, add4 ha, scale1 hr, scale2 hr, scale3 hr, scale4 hr]
  apply congrArg (BitVec.ofNat 64)
  simp only [products, convolution, asLimbs]
  grind

include ha hr in
theorem product3 : v101c1a x = BitVec.ofNat 64 (products x).x3 := by
  simp only [v101c1a, v101c16, v101c13, v101c10, v101c0c, v101c05, v101bff, v101bfb, v101bf4, ← BitVec.ofNat_toNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat,
    add0 ha, add1 ha, add2 ha, add3 ha, add4 ha, scale1 hr, scale2 hr, scale3 hr, scale4 hr]
  apply congrArg (BitVec.ofNat 64)
  simp only [products, convolution, asLimbs]
  grind

include ha in
theorem product4 : v101c3c x = BitVec.ofNat 64 (products x).x4 := by
  simp only [v101c3c, v101c38, v101c35, v101c32, v101c2e, v101c2a, v101c27, v101c23, v101c1d, ← BitVec.ofNat_toNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat,
    add0 ha, add1 ha, add2 ha, add3 ha, add4 ha]
  apply congrArg (BitVec.ofNat 64)
  simp only [products, convolution, asLimbs]
  grind

include ha hr in
theorem output_eq : asLimbs (output x) = update (asLimbs x.acc) (asLimbs x.r) (fullBlock x.block.toNat) := by
  let d := products x
  obtain ⟨f0,f1,f2,f3,f4,foldBound⟩ : Fits d :=
    convolution_fits ha hr (tight_split _)
  simp only [B, Nat.reducePow] at f0 f1 f2 f3 f4 foldBound
  have p0 : (v101b74 x).toNat = d.x0 := by
    rw [product0 ha hr, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    change d.x0 < 2^64
    omega
  have p1 : (v101bac x).toNat = d.x1 := by
    rw [product1 ha hr, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    change d.x1 < 2^64
    omega
  have p2 : (v101be5 x).toNat = d.x2 := by
    rw [product2 ha hr, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    change d.x2 < 2^64
    omega
  have p3 : (v101c1a x).toNat = d.x3 := by
    rw [product3 ha hr, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    change d.x3 < 2^64
    omega
  have p4 : (v101c3c x).toNat = d.x4 := by
    rw [product4 ha, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    change d.x4 < 2^64
    omega
  have t1 : (v101c50 x).toNat = d.x1 + (d.x0)/B := by
    simp only [v101c50, v101c42, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, p0, p1, B]
    omega
  have t2 : (v101c66 x).toNat = d.x2 + (d.x1 + (d.x0)/B)/B := by
    simp only [v101c66, v101c58, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, t1, p2, B]
    omega
  have t3 : (v101c73 x).toNat = d.x3 + (d.x2 + (d.x1 + (d.x0)/B)/B)/B := by
    simp only [v101c73, v101c6d, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, t2, p3, B]
    omega
  have t4 : (v101c7f x).toNat = d.x4 + (d.x3 + (d.x2 + (d.x1 + (d.x0)/B)/B)/B)/B := by
    simp only [v101c7f, v101c79, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, t3, p4, B]
    omega
  let z := d.x4 + (d.x3 + (d.x2 + (d.x1 + d.x0/B)/B)/B)/B
  change (v101c7f x).toNat = z at t4
  change d.x0 % 67108864 + 5*(z/67108864) < 4294967296 at foldBound
  have modMask (u : Nat) : u % 4294967296 % 67108864 = u % 67108864 :=
    Nat.mod_mod_of_dvd _ (by decide)
  have five : (v101c89 x).toNat = 5*(z/67108864) := by
    simp only [v101c89, v101c85, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow,t4]
    omega
  have folded : (v101c8c x).toNat = d.x0 % 67108864 + 5*(z/67108864) := by
    simp only [v101c8c, BitVec.toNat_add,five,v101c46,masked,BitVec.toNat_setWidth,p0,
      B,Nat.reducePow,modMask]
    omega
  change asLimbs (output x) = (carry d).limbs
  simp only [output, asLimbs, carry, v101c97, v101c94, v101ca5, v101cb0, v101cba,
    v101c91, v101c5c, masked, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.reducePow, folded, t1, t2, t3, t4, B, modMask, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, Limbs.mk.injEq]
  have small : (d.x0 % 67108864 + 5*(z/67108864)) / 67108864 < 64 := by omega
  simp only [z, B, Nat.reducePow] at *
  simp only [eq_self, true_and, and_true]
  apply (Nat.mod_eq_of_lt _).trans (Nat.add_comm _ _)
  have hmod := Nat.mod_lt (d.x1 + d.x0/67108864) (show 0 < 67108864 by decide)
  omega

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
