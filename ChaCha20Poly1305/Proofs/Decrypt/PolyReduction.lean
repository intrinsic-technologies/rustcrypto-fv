import ChaCha20Poly1305.Proofs.Decrypt.PolyBounds

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305

def normalize (a : Limbs) : Limbs :=
  let c2 := a.x2 + a.x1/B
  let c3 := a.x3 + c2/B
  let c4 := a.x4 + c3/B
  let c0 := a.x0 + 5*(c4/B)
  ⟨c0%B, a.x1%B + c0/B, c2%B, c3%B, c4%B⟩

theorem normalize_tight {a : Limbs} (h : a.Bounded) : (normalize a).Tight := by
  obtain ⟨ha,hb,hc,hd,he⟩ := h
  simp only [Limbs.Tight, normalize, B, Nat.reducePow] at *
  by_cases hb' : a.x1 < 67108864 <;> omega

theorem normalize_value {a : Limbs} : (normalize a).value % modulus = a.value % modulus := by
  let q := (a.x4 + (a.x3 + (a.x2 + a.x1/B)/B)/B)/B
  have hh : a.value = (normalize a).value + q * modulus := by
    simp only [normalize, Limbs.value, q, B, modulus, Nat.reducePow, Nat.reduceSub]
    omega
  rw [hh, Nat.add_mul_mod_self_right]

def plusFive (a : Limbs) : Limbs :=
  let r0 := a.x0 + 5
  let r1 := a.x1 + r0/B
  let r2 := a.x2 + r1/B
  let r3 := a.x3 + r2/B
  let r4 := a.x4 + r3/B
  ⟨r0%B, r1%B, r2%B, r3%B, r4⟩

theorem plusFive_value (a : Limbs) : (plusFive a).value = a.value + 5 := by
  simp only [plusFive, Limbs.value, B, Nat.reducePow]
  omega

theorem topBound {a : Limbs} (h : a.Tight) : (plusFive a).x4 ≤ B := by
  obtain ⟨ha,hb,hc,hd,he⟩ := h
  simp only [plusFive, B, Nat.reducePow] at *
  omega

theorem tight_value_lt {a : Limbs} (h : a.Tight) : a.value < 2^130 := by
  obtain ⟨ha,hb,hc,hd,he⟩ := h
  simp only [Limbs.value, B, Nat.reducePow] at *
  omega

theorem plusFive_test {a : Limbs} (h : a.Tight) : (plusFive a).x4 < B ↔ a.value < modulus := by
  obtain ⟨ha,hb,hc,hd,he⟩ := h
  simp only [plusFive, Limbs.value, modulus, B, Nat.reducePow,Nat.reduceSub] at *
  omega

theorem chosen_value {a : Limbs} (h : a.Tight) :
    (if (plusFive a).x4 < B then a.value else (plusFive a).value) % 2^128 =
      (a.value % modulus) % 2^128 := by
  have hv := tight_value_lt h
  rw [plusFive_value]
  by_cases ht : (plusFive a).x4 < B
  · rw [ite_eq_left ht, Nat.mod_eq_of_lt ((plusFive_test h).mp ht)]
  · have hp := (not_congr (plusFive_test h)).mp ht
    rw [ite_eq_right ht]
    simp only [modulus, Nat.reducePow, Nat.reduceSub] at hp hv ⊢
    omega

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305
