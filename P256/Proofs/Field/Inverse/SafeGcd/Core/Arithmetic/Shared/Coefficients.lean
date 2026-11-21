import P256.Proofs.Projective.Algebra.Field.Prime

set_option autoImplicit false

open P256.Proofs.Projective.Algebra.FieldArithmetic (coprime_mul_mod_injective)

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Coefficients



theorem two_pow_mul_mod_cancel {modulus : Nat} (positive : 0 < modulus)
    (coprime : Nat.Coprime 2 modulus) {x y : Int} (shift : Nat)
    (h : ((2 : Int)^shift * x) % modulus =
      ((2 : Int)^shift * y) % modulus) :
    x % modulus = y % modulus := by
  have hp : 0 < (modulus : Int) := by exact_mod_cast positive
  have hx0 := Int.emod_nonneg x (by omega : (modulus : Int) ≠ 0)
  have hy0 := Int.emod_nonneg y (by omega : (modulus : Int) ≠ 0)
  have hxp := Int.emod_lt_of_pos x hp
  have hyp := Int.emod_lt_of_pos y hp
  have hx : ((x % modulus).toNat : Int) = x % modulus :=
    Int.toNat_of_nonneg hx0
  have hy : ((y % modulus).toNat : Int) = y % modulus :=
    Int.toNat_of_nonneg hy0
  have hnorm : ((2 : Int)^shift * (x % modulus)) % modulus =
      ((2 : Int)^shift * (y % modulus)) % modulus := by
    simpa only [Int.mul_emod, Int.emod_emod] using h
  have hnat : (2^shift * (x % modulus).toNat) % modulus =
      (2^shift * (y % modulus).toNat) % modulus := by
    exact_mod_cast (show ((2 : Int)^shift * ((x % modulus).toNat : Int)) % modulus =
      ((2 : Int)^shift * ((y % modulus).toNat : Int)) % modulus by rw [hx, hy]; exact hnorm)
  have heq := coprime_mul_mod_injective
    (Nat.Coprime.pow_left shift coprime)
    (show (x % modulus).toNat < modulus by omega)
    (show (y % modulus).toNat < modulus by omega) hnat
  omega

theorem coefficient_update {modulus : Nat} (positive : 0 < modulus)
    (coprime : Nat.Coprime 2 modulus) {a scale f g d e u v fNext dNext : Int} (shift : Nat)
    (hd : (d * a) % modulus = (f * scale) % modulus)
    (he : (e * a) % modulus = (g * scale) % modulus)
    (hf : (2 : Int)^shift * fNext = u * f + v * g)
    (hn : ((2 : Int)^shift * dNext) % modulus =
      (u * d + v * e) % modulus) :
    (dNext * a) % modulus = (fNext * scale) % modulus := by
  apply two_pow_mul_mod_cancel positive coprime shift
  calc
    ((2 : Int)^shift * (dNext * a)) % modulus =
        (((2 : Int)^shift * dNext) * a) % modulus := by rw [Int.mul_assoc]
    _ = ((u * d + v * e) * a) % modulus := by
      rw [Int.mul_emod, hn, ← Int.mul_emod]
    _ = (u * (d * a) + v * (e * a)) % modulus := by congr 1; grind only
    _ = (u * (f * scale) + v * (g * scale)) % modulus := by
      rw [Int.add_emod, Int.mul_emod u, Int.mul_emod v, hd, he,
        ← Int.mul_emod, ← Int.mul_emod, ← Int.add_emod]
    _ = ((u * f + v * g) * scale) % modulus := by congr 1; grind only
    _ = ((2 : Int)^shift * (fNext * scale)) % modulus := by rw [← hf, Int.mul_assoc]

theorem coefficient_terminal {modulus : Nat} (positive : 0 < modulus) {a scale : Nat} {f d : Int}
    (hscale : scale < modulus) (hf : f.natAbs = 1)
    (hinv : (d * (a : Int)) % modulus =
      (f * (scale : Int)) % modulus) :
    let result := ((if f < 0 then -d else d) % (modulus : Int)).toNat
    result < modulus ∧ result * a % modulus = scale := by
  let signed := if f < 0 then -d else d
  have hscaleMod : (scale : Int) % modulus = scale :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hscale)
  have hc : (signed * (a : Int)) % modulus = scale := by
    by_cases hneg : f < 0
    · have habs := Int.ofNat_natAbs_of_nonpos (by omega : f ≤ 0)
      have hfone : f = -1 := by omega
      have hn := (Int.emod_sub_cancel_left (m := d * (a : Int))
        (n := (modulus : Int)) (k := f * (scale : Int)) 0).mpr hinv
      simpa only [signed, ite_eq_left hneg, Int.zero_sub, hfone,
        Int.neg_one_mul, Int.neg_neg, ← Int.neg_mul, hscaleMod] using hn
    · have habs := Int.natAbs_of_nonneg (by omega : 0 ≤ f)
      have hfone : f = 1 := by omega
      simpa only [signed, ite_eq_right hneg, hfone, Int.one_mul, hscaleMod] using hinv
  have hp : 0 < (modulus : Int) := by exact_mod_cast positive
  have hzero := Int.emod_nonneg signed (by omega : (modulus : Int) ≠ 0)
  have hlt := Int.emod_lt_of_pos signed hp
  have hcast : ((signed % modulus).toNat : Int) = signed % modulus :=
    Int.toNat_of_nonneg hzero
  change (signed % modulus).toNat < modulus ∧
    (signed % modulus).toNat * a % modulus = scale
  refine ⟨by omega, ?_⟩
  have he : (((signed % modulus).toNat : Int) * (a : Int)) % modulus = scale := by
    rw [hcast, Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
    exact hc
  exact_mod_cast he

end P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Coefficients
