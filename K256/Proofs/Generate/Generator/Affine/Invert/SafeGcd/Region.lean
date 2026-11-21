import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Bounds

set_option autoImplicit false

namespace K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Contraction

inductive Region (f g t : Rat) : Int → Prop
  | positive (k : Nat)
      (h : Contains positive (alpha^k*f) ((2*alpha)^k*g) t) :
      Region f g t (2*(k : Int)+1)
  | negativeOne (h : Contains negative f g t) : Region f g t (-1)
  | negative (k : Nat)
      (h : Contains positive (alpha^(k+3)*(f-2*g))
        ((2 : Rat)^(k+2)*alpha^(k+3)*f) t) :
      Region f g t (-(2*(k : Int)+3))

theorem one_le_power {a : Rat} (n : Nat) (ha : 1 ≤ a) : 1 ≤ a^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Rat.mul_le_mul_of_nonneg_left ih (show 0 ≤ a by grind only)
    rw [Rat.pow_succ]
    grind only

theorem reciprocal_power_bound (n : Nat) :
    0 ≤ (1 : Rat)/2^(n+4) ∧ (1 : Rat)/2^(n+4) ≤ 1/16 := by
  have hp : 0 < (2 : Rat)^(n+4) := Rat.pow_pos (by decide)
  have hne : (2 : Rat)^(n+4) ≠ 0 := Rat.ne_of_gt hp
  have hpos : 0 < (1 : Rat)/2^(n+4) := by
    rw [Rat.lt_div_iff hp]
    simp +decide
  have hpow := one_le_power n (by decide : (1 : Rat) ≤ 2)
  have hden : (16 : Rat) ≤ 2^(n+4) := by
    simp only [Rat.pow_succ]
    grind only
  have h := Rat.mul_le_mul_of_nonneg_left hden (Rat.le_of_lt hpos)
  have heq : (1 : Rat)/2^(n+4)*2^(n+4)=1 := Rat.div_mul_cancel hne
  constructor
  · exact Rat.le_of_lt hpos
  · grind only

theorem Region.even {f g t : Rat} {delta : Int}
    (h : Region f g t delta) (ht : 0 ≤ t) :
    Region f (g/2) (alpha*t) (delta+2) := by
  cases h with
  | positive k hp =>
    have hn := hp.scale (Rat.le_of_lt alpha_pos)
    have he : 2*(k : Int)+1+2=2*((k+1 : Nat) : Int)+1 := by omega
    rw [he]
    apply Region.positive (k+1)
    simp only [Rat.pow_succ]
    exact Contains.congr hn (by grind only) (by grind only) rfl
  | negativeOne hp =>
    have hn := negative_even ht hp
    exact Region.positive 0 (by simpa only [Rat.pow_zero, Rat.one_mul] using hn)
  | negative k hp =>
    cases k with
    | zero =>
      have hn := (boundary_even ht hp).scale (Rat.le_of_lt alpha_pos)
      apply Region.negativeOne
      dsimp only [alpha] at hn ⊢
      exact Contains.congr hn (by grind only) (by grind only) rfl
    | succ k =>
      have hz := reciprocal_power_bound k
      have hn := (positive_shear ht hp (by grind only : -1/16 ≤ (1 : Rat)/2^(k+4)) hz.2).scale
        (Rat.le_of_lt alpha_pos)
      have he : -(2*((k+1 : Nat) : Int)+3)+2=-(2*(k : Int)+3) := by omega
      rw [he]
      apply Region.negative k
      have ha : alpha ≠ 0 := Rat.ne_of_gt alpha_pos
      have hb : (2 : Rat)^k ≠ 0 := Rat.ne_of_gt (Rat.pow_pos (by decide))
      simp only [Nat.add_assoc, Rat.pow_succ] at hn ⊢
      exact Contains.congr hn (by grind only) (by grind only) rfl

theorem Region.odd {f g t : Rat} {delta : Int}
    (h : Region f g t delta) (ht : 0 ≤ t) :
    if 0 < delta then Region g ((g-f)/2) (alpha*t) (2-delta)
    else Region f ((g+f)/2) (alpha*t) (delta+2) := by
  cases h with
  | positive k hp =>
    rw [ite_eq_left (by omega)]
    cases k with
    | zero =>
      apply Region.positive 0
      simpa only [Rat.pow_zero, Rat.one_mul] using
        swap_positive ht (by simpa only [Rat.pow_zero, Rat.one_mul] using hp)
    | succ k =>
      cases k with
      | zero =>
        have hn := (swap_negative ht hp).scale (Rat.le_of_lt alpha_pos)
        apply Region.negativeOne
        dsimp only [alpha] at hn ⊢
        exact Contains.congr hn (by grind only) (by grind only) rfl
      | succ k =>
        have hn := hp.scale (Rat.le_of_lt alpha_pos)
        have he : 2-(2*((k+1+1 : Nat) : Int)+1)=-(2*(k : Int)+3) := by omega
        rw [he]
        apply Region.negative k
        simp only [Nat.add_assoc, Rat.pow_succ, Lean.Grind.CommSemiring.mul_pow] at hn ⊢
        exact Contains.congr hn (by grind only) (by grind only) rfl
  | negativeOne hp =>
    rw [ite_eq_right (by decide)]
    exact Region.positive 0 (by simpa only [Rat.pow_zero, Rat.one_mul] using negative_odd ht hp)
  | negative k hp =>
    rw [ite_eq_right (by omega)]
    cases k with
    | zero =>
      have hn := (boundary_odd ht hp).scale (Rat.le_of_lt alpha_pos)
      apply Region.negativeOne
      dsimp only [alpha] at hn ⊢
      exact Contains.congr hn (by grind only) (by grind only) rfl
    | succ k =>
      have hz := reciprocal_power_bound k
      have hn := (positive_shear ht hp (by grind only : -1/16 ≤ -((1 : Rat)/2^(k+4)))
        (by grind only : -((1 : Rat)/2^(k+4)) ≤ 1/16)).scale (Rat.le_of_lt alpha_pos)
      have he : -(2*((k+1 : Nat) : Int)+3)+2=-(2*(k : Int)+3) := by omega
      rw [he]
      apply Region.negative k
      have ha : alpha ≠ 0 := Rat.ne_of_gt alpha_pos
      have hb : (2 : Rat)^k ≠ 0 := Rat.ne_of_gt (Rat.pow_pos (by decide))
      simp only [Nat.add_assoc, Rat.pow_succ] at hn ⊢
      exact Contains.congr hn (by grind only) (by grind only) rfl

end K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Contraction
