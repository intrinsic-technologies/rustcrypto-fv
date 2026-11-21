import K256.Proofs.Common.Arithmetic.CubicNonzero.Prime

set_option autoImplicit false

namespace K256.Proofs.Common.Arithmetic.CubicNonzero

structure ModularOrder (modulus base order : Nat) : Prop where
  positive : 0 < order
  power : base ^ order % modulus = 1
  minimal : ∀ e, 0 < e → base ^ e % modulus = 1 → order ≤ e

theorem exists_modularOrder (modulus base exponent : Nat) (hpos : 0 < exponent)
    (hpow : base ^ exponent % modulus = 1) :
    ∃ order, ModularOrder modulus base order := by
  induction exponent using Nat.strongRecOn with
  | ind exponent ih =>
    classical
    by_cases hex : ∃ e, 0 < e ∧ e < exponent ∧ base ^ e % modulus = 1
    · obtain ⟨e, he, hlt, heq⟩ := hex
      exact ih e hlt he heq
    · refine ⟨exponent, hpos, hpow, ?_⟩
      intro e he heq
      by_cases hle : exponent ≤ e
      · exact hle
      · exact False.elim (hex ⟨e, he, by omega, heq⟩)

theorem pow_mod_eq_pow_mod_order {modulus base order : Nat}
    (hpow : base ^ order % modulus = 1) (exponent : Nat) :
    base ^ exponent % modulus = base ^ (exponent % order) % modulus := by
  calc
    _ = (base ^ (exponent % order) * (base ^ order) ^ (exponent / order)) % modulus := by
      rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mod_add_div]
    _ = (base ^ (exponent % order) % modulus *
        ((base ^ order % modulus) ^ (exponent / order) % modulus)) % modulus := by
      rw [Nat.mul_mod, Nat.pow_mod (base ^ order)]
    _ = _ := by simp [hpow]

theorem ModularOrder.dvd_of_pow_eq_one {modulus base order exponent : Nat}
    (horder : ModularOrder modulus base order) (hpow : base ^ exponent % modulus = 1) :
    order ∣ exponent := by
  apply Nat.dvd_of_mod_eq_zero
  have he := (pow_mod_eq_pow_mod_order horder.power exponent).symm.trans hpow
  by_cases hzero : exponent % order = 0
  · exact hzero
  · have hsmall := horder.minimal _ (by omega) he
    have hlt := Nat.mod_lt exponent horder.positive
    omega

end K256.Proofs.Common.Arithmetic.CubicNonzero
