import Standards.SECG.DomainParameters.Secp256k1

namespace K256.Proofs.Generate.Curve

open Standards.SECG.DomainParameters.Secp256k1

def eigenvalue : Nat := 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

def minusB1 : Nat := 0xe4437ed6010e88286f547fa90abfe4c3

def minusB2 : Nat := 0xfffffffffffffffffffffffffffffffe8a280ac50774346dd765cda83db1562c

def g1 : Nat := 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031

def g2 : Nat := 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71

def mulShift384 (k g : Nat) : Nat := (k * g + 2^383) / 2^384

def splitSecond (k : Nat) : Nat :=
  (mulShift384 k g1 * minusB1 + mulShift384 k g2 * minusB2) % domain.n

def splitFirst (k : Nat) : Nat :=
  (k + splitSecond k * (domain.n - eigenvalue)) % domain.n

def centered (r : Nat) : Int :=
  if domain.n / 2 < r then (r : Int) - domain.n else r

private def a1 : Int := 0x3086d221a7d46bcde86c90e49284eb15
private def a2 : Int := 0x114ca50f7a8e2f3f657c1108d9d44cfd8
private def b2 : Int := a1

set_option exponentiation.threshold 384 in
private theorem rounding_bounds (k g : Nat) :
    -(2^383 : Int) ≤ (k : Int) * g - (mulShift384 k g : Int) * 2^384 ∧
    (k : Int) * g - (mulShift384 k g : Int) * 2^384 < 2^383 := by
  simp only [mulShift384, Int.natCast_ediv, Int.natCast_add, Int.natCast_mul]
  change -(2^383 : Int) ≤ (k : Int) * g - (((k : Int) * g + 2^383) / 2^384) * 2^384 ∧
    (k : Int) * g - (((k : Int) * g + 2^383) / 2^384) * 2^384 < 2^383
  omega

private theorem lattice_bounds (k : Nat) (hk : k < domain.n) :
    ((k : Int) + (mulShift384 k g1 : Int) * (-a1) + (mulShift384 k g2 : Int) * (-a2)).natAbs < 2^128 ∧
    ((mulShift384 k g1 : Int) * minusB1 + (mulShift384 k g2 : Int) * (-b2)).natAbs < 2^128 := by
  obtain ⟨lower₁, upper₁⟩ := rounding_bounds k g1
  obtain ⟨lower₂, upper₂⟩ := rounding_bounds k g2
  generalize mulShift384 k g1 = c₁ at *
  generalize mulShift384 k g2 = c₂ at *
  simp only [domain] at hk
  simp only [g1, g2] at lower₁ upper₁ lower₂ upper₂
  simp only [a1, a2, b2, minusB1]
  constructor <;> omega

private theorem centered_nat_mod (x : Nat) :
    centered (x % domain.n) = (x : Int).bmod domain.n := by
  rw [centered, Int.bmod_def, ← Int.natCast_emod]
  have threshold : ((domain.n : Int) + 1) / 2 = (domain.n / 2 : Nat) + (1 : Int) := by
    decide +kernel
  rw [threshold]
  by_cases high : domain.n / 2 < x % domain.n
  · rw [ite_eq_left high, ite_eq_right]
    omega
  · rw [ite_eq_right high, ite_eq_left]
    omega

private theorem bmod_linear_combination (x c d a b a' b' : Int)
    (ha : a.bmod domain.n = a'.bmod domain.n)
    (hb : b.bmod domain.n = b'.bmod domain.n) :
    (x + c * a + d * b).bmod domain.n = (x + c * a' + d * b').bmod domain.n := by
  have hc : (c * a).bmod domain.n = (c * a').bmod domain.n := by
    rw [Int.mul_bmod c a, Int.mul_bmod c a', ha]
  have hd : (d * b).bmod domain.n = (d * b').bmod domain.n := by
    rw [Int.mul_bmod d b, Int.mul_bmod d b', hb]
  exact (Int.add_bmod_eq_add_bmod_right _ (Int.add_bmod_eq_add_bmod_left x hc)).trans
    (Int.add_bmod_eq_add_bmod_left _ hd)

private theorem splitFirst_bmod (k : Nat) :
    centered (splitFirst k) =
      ((k : Int) - centered (splitSecond k) * eigenvalue).bmod domain.n := by
  have hEigenvalue : eigenvalue ≤ domain.n := by decide +kernel
  rw [splitFirst, centered_nat_mod]
  simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_sub hEigenvalue]
  let r : Int := splitSecond k
  change ((k : Int) + r * ((domain.n : Int) - eigenvalue)).bmod domain.n = _
  have h : (k : Int) + r * ((domain.n : Int) - eigenvalue) =
      (k : Int) - r * eigenvalue + r * domain.n := by
    rw [Int.mul_sub]
    simp only [Int.sub_eq_add_neg]
    ac_rfl
  rw [h, Int.add_mul_bmod_self_right]
  apply (Int.bmod_sub_cancel_left (k : Int)).mpr
  dsimp only [r]
  rw [splitSecond, centered_nat_mod, Int.bmod_mul_bmod, Int.natCast_emod, Int.emod_mul_bmod]

private theorem splitSecond_lattice (k : Nat) :
    centered (splitSecond k) =
      ((mulShift384 k g1 : Int) * minusB1 + (mulShift384 k g2 : Int) * (-b2)).bmod domain.n := by
  rw [splitSecond, centered_nat_mod]
  simp only [Int.natCast_add, Int.natCast_mul]
  have hb : (minusB2 : Int).bmod domain.n = (-b2).bmod domain.n := by decide +kernel
  have h := bmod_linear_combination 0 (mulShift384 k g1) (mulShift384 k g2)
    minusB1 minusB2 minusB1 (-b2) rfl hb
  simpa only [Int.zero_add] using h

private theorem splitFirst_lattice (k : Nat) :
    centered (splitFirst k) =
      ((k : Int) + (mulShift384 k g1 : Int) * (-a1) +
        (mulShift384 k g2 : Int) * (-a2)).bmod domain.n := by
  rw [splitFirst_bmod, splitSecond_lattice]
  simp only [Int.sub_eq_add_neg, ← Int.mul_neg]
  rw [← @Int.add_bmod_bmod (k : Int) _ domain.n, Int.bmod_mul_bmod, Int.add_bmod_bmod]
  simp only [Int.add_mul, Int.mul_assoc, ← Int.add_assoc]
  apply bmod_linear_combination <;> decide +kernel

private theorem bmod_eq_of_small {x : Int} (hx : x.natAbs < 2^128) :
    x.bmod domain.n = x := by
  apply Int.bmod_eq_of_le
  · have h : (2^128 : Int) ≤ ((domain.n : Int) / 2) := by decide +kernel
    omega
  · have h : (2^128 : Int) ≤ (((domain.n : Int) + 1) / 2) := by decide +kernel
    omega

theorem split_correct (k : Nat) (hk : k < domain.n) :
    ((centered (splitFirst k) + centered (splitSecond k) * eigenvalue) % (domain.n : Int)) =
      (k : Int) ∧ (centered (splitFirst k)).natAbs < 2^128 ∧
      (centered (splitSecond k)).natAbs < 2^128 := by
  constructor
  · rw [splitFirst_bmod]
    rw [Int.add_emod_eq_add_emod_right _ Int.bmod_emod, Int.sub_add_cancel]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hk)
  · obtain ⟨hFirst, hSecond⟩ := lattice_bounds k hk
    rw [splitFirst_lattice, splitSecond_lattice, bmod_eq_of_small hFirst, bmod_eq_of_small hSecond]
    exact ⟨hFirst, hSecond⟩

end K256.Proofs.Generate.Curve
