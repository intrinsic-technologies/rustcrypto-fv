import P256.Proofs.Field.Inverse.SafeGcd.Arithmetic.Region

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Contraction

def Budget (delta : Int) (t : Rat) : Prop := (2*alpha)^(delta.natAbs/2) ≤ t

theorem Budget.one_le {delta : Int} {t : Rat} (h : Budget delta t) : 1 ≤ t :=
  Rat.le_trans (one_le_power _ two_alpha_ge_one) h

theorem positive_budget {f t : Rat} {g delta : Int}
    (h : Region f (g : Rat) t delta) (ht : 0 ≤ t) (hd : 0 < delta) (hg : g ≠ 0) :
    Budget delta t := by
  cases h with
  | positive k hp =>
    have heq : (2*(k : Int)+1).natAbs/2=k := by
      have he : ((2*(k : Int)+1).natAbs : Int)=2*(k : Int)+1 :=
        Int.natAbs_of_nonneg (by omega)
      omega
    unfold Budget
    rw [heq]
    have hb := positive_g_bound ht hp
    have hp : 0 ≤ (2*alpha)^k := Rat.pow_nonneg (by have := two_alpha_ge_one; grind only)
    by_cases hneg : g < 0
    · have hg' : (g : Rat) ≤ -1 := by
        have hi : g ≤ -1 := by omega
        exact Rat.intCast_le_intCast.mpr hi
      have hm := Rat.mul_le_mul_of_nonneg_left hg' hp
      grind only
    · have hg' : (1 : Rat) ≤ (g : Rat) := by
        have hi : 1 ≤ g := by omega
        exact Rat.intCast_le_intCast.mpr hi
      have hm := Rat.mul_le_mul_of_nonneg_left hg' hp
      grind only
  | negativeOne hp => omega
  | negative k hp => omega

theorem budget_shrink {k : Nat} {t : Rat} (h : (2*alpha)^(k+1) ≤ t) :
    (2*alpha)^k ≤ alpha*t := by
  have hp : 0 ≤ (2*alpha)^k := Rat.pow_nonneg (by have := two_alpha_ge_one; grind only)
  have hn := Rat.mul_le_mul_of_nonneg_right two_alpha_sq_ge_one hp
  have hm := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt alpha_pos)
  simp only [Rat.pow_succ] at hm
  have he : 2*alpha^2*((2*alpha)^k) = alpha*((2*alpha)^k*(2*alpha)) := by grind only
  grind only

theorem negative_budget {delta delta' : Int} {t : Rat} (h : Budget delta t)
    (hd : delta' < 0) (step : delta'=delta+2 ∨ delta'=2-delta) :
    Budget delta' (alpha*t) := by
  have hnew : (delta'.natAbs : Int)=-delta' := Int.ofNat_natAbs_of_nonpos (by omega)
  have heq : delta.natAbs/2=delta'.natAbs/2+1 := by
    rcases step with he | he
    · have hold : (delta.natAbs : Int)=-delta := Int.ofNat_natAbs_of_nonpos (by omega)
      omega
    · have hold : (delta.natAbs : Int)=delta := Int.natAbs_of_nonneg (by omega)
      omega
  unfold Budget at h ⊢
  rw [heq] at h
  exact budget_shrink h

theorem Region.delta_ne_zero {f g t : Rat} {delta : Int} (h : Region f g t delta) :
    delta ≠ 0 := by
  cases h <;> omega

theorem cast_half (x : Int) (h : x % 2=0) : ((x/2 : Int) : Rat)=(x : Rat)/2 := by
  have hh : 2*(x/2)=x := by omega
  have hc := congrArg (fun z : Int => (z : Rat)) hh
  simp only [Rat.intCast_mul] at hc
  change 2*((x/2 : Int) : Rat)=(x : Rat) at hc
  grind only

theorem divstep_region {s : DivState} {t : Rat}
    (h : Region (s.f : Rat) (s.g : Rat) t s.delta) (ht : 0 ≤ t) (odd : s.f % 2=1) :
    Region ((divstep s).f : Rat) ((divstep s).g : Rat) (alpha*t) (divstep s).delta := by
  dsimp only [divstep]
  split
  · rename_i even
    simpa only [cast_half s.g even] using Region.even h ht
  · rename_i oddg
    have hn := Region.odd h ht
    split
    · rename_i hd
      rw [ite_eq_left hd] at hn
      simpa only [cast_half (s.g-s.f) (by omega), Rat.intCast_sub] using hn
    · rename_i hd
      rw [ite_eq_right hd] at hn
      simpa only [cast_half (s.g+s.f) (by omega), Rat.intCast_add] using hn

theorem divstep_budget {s : DivState} {t : Rat}
    (h : Region ((divstep s).f : Rat) ((divstep s).g : Rat) (alpha*t) (divstep s).delta)
    (budget : Budget s.delta t) (nonzero : (divstep s).g ≠ 0) :
    Budget (divstep s).delta (alpha*t) := by
  by_cases hd : 0 < (divstep s).delta
  · apply positive_budget h _ hd nonzero
    exact Rat.mul_nonneg (Rat.le_of_lt alpha_pos) (Rat.le_trans (by decide) budget.one_le)
  · apply negative_budget budget (by have := h.delta_ne_zero; omega)
    dsimp only [divstep]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl

end P256.Proofs.Field.Inverse.SafeGcd.Contraction
