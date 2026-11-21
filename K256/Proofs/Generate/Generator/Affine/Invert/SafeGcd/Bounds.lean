import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Certificate

set_option autoImplicit false

namespace K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Contraction

theorem Contains.congr {ps : List Plane} {x y t u v z : Rat}
    (h : Contains ps x y t) (hx : x=u) (hy : y=v) (ht : t=z) : Contains ps u v z := by
  subst u v z
  exact h

theorem positive_initial {f g : Rat} (hg : 0 ≤ g) (hgf : g ≤ f) :
    Contains positive f g ((111/100)*f) := by
  intro p hp
  rcases initial_certifies p hp with ⟨ha,hb⟩
  have h1 := Rat.mul_le_mul_of_nonneg_right ha (show 0 ≤ f-g by grind only)
  have h2 := Rat.mul_le_mul_of_nonneg_right hb hg
  calc
    _ = p.a*(f-g)+(p.a+p.b)*g := by grind only
    _ ≤ (p.c*(111/100))*(f-g)+(p.c*(111/100))*g := by grind only
    _ = _ := by grind only

theorem positive_g_bound {x y t : Rat} (ht : 0 ≤ t) (h : Contains positive x y t) :
    -t ≤ y ∧ y ≤ t := by
  have hu := Witness.sound upper_certifies ht h
  have hl := Witness.sound lower_certifies ht h
  dsimp only at hu hl
  grind only

theorem swap_positive {x y t : Rat} (ht : 0 ≤ t) (h : Contains positive x y t) :
    Contains positive y ((y-x)/2) (alpha*t) := by
  have hn := (Certifies.sound swapP_certifies ht h).scale (Rat.le_of_lt alpha_pos)
  dsimp only [swapP, alpha] at hn ⊢
  exact Contains.congr hn (by grind only) (by grind only) (by grind only)

theorem swap_negative {x y t : Rat} (ht : 0 ≤ t) (h : Contains positive x y t) :
    Contains negative (y/(2*alpha^2)) ((y-2*x)/(4*alpha^2)) t := by
  have hn := Certifies.sound swapN_certifies ht h
  dsimp only [swapN, alpha] at hn ⊢
  exact Contains.congr hn (by grind only) (by grind only) (by grind only)

theorem negative_even {x y t : Rat} (ht : 0 ≤ t) (h : Contains negative x y t) :
    Contains positive x (y/2) (alpha*t) := by
  have hn := (Certifies.sound evenN_certifies ht h).scale (Rat.le_of_lt alpha_pos)
  dsimp only [evenN, alpha] at hn ⊢
  exact Contains.congr hn (by grind only) (by grind only) (by grind only)

theorem negative_odd {x y t : Rat} (ht : 0 ≤ t) (h : Contains negative x y t) :
    Contains positive x ((y+x)/2) (alpha*t) := by
  have hn := (Certifies.sound oddN_certifies ht h).scale (Rat.le_of_lt alpha_pos)
  dsimp only [oddN, alpha] at hn ⊢
  exact Contains.congr hn (by grind only) (by grind only) (by grind only)

theorem boundary_even {x y t : Rat} (ht : 0 ≤ t) (h : Contains positive x y t) :
    Contains negative (y/(4*alpha^4)) ((y-4*x)/(16*alpha^4)) t := by
  have hn := Certifies.sound evenBoundary_certifies ht h
  dsimp only [evenBoundary, alpha] at hn ⊢
  exact Contains.congr hn (by grind only) (by grind only) (by grind only)

theorem boundary_odd {x y t : Rat} (ht : 0 ≤ t) (h : Contains positive x y t) :
    Contains negative (y/(4*alpha^4)) ((3*y-4*x)/(16*alpha^4)) t := by
  have hn := Certifies.sound oddBoundary_certifies ht h
  dsimp only [oddBoundary, alpha] at hn ⊢
  exact Contains.congr hn (by grind only) (by grind only) (by grind only)

theorem positive_shear {x y t z : Rat} (ht : 0 ≤ t) (h : Contains positive x y t)
    (hz : -1/16 ≤ z) (hz' : z ≤ 1/16) :
    Contains positive ((x/2+z*y)/alpha^2) (y/(2*alpha^2)) t := by
  have hl : 0 ≤ (1+16*z)/2 := by grind only
  have hr : 0 ≤ (1-16*z)/2 := by grind only
  have h1 := (Certifies.sound shearPlus_certifies ht h).scale hl
  have h2 := (Certifies.sound shearMinus_certifies ht h).scale hr
  have hn := h1.add h2
  dsimp only [shearPlus, shearMinus, alpha] at hn ⊢
  exact Contains.congr hn (by grind only) (by grind only) (by grind only)

end K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Contraction
