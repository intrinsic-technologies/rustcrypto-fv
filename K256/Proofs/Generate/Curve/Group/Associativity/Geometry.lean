import K256.Proofs.Generate.Curve.Group.Cancellation
import K256.Proofs.Generate.Curve.Group.Infinity

set_option autoImplicit false

namespace K256.Proofs.Generate.Curve.Group.Affine

open Lean.Grind

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
theorem affine_double_den (a b x y : F) (h2 : (2 : F) ≠ 0)
    (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (hp : onCurve a b (.affine x y)) : 2 * y ≠ 0 := by
  have hy : y ≠ 0 := by
    intro hy
    exact hnozero x (by simp only [onCurve] at hp; grind only)
  intro h
  exact (Field.of_mul_eq_zero h).elim h2 hy

theorem same_x_of_add_ne_infinity (a b x y z : F)
    (hp : onCurve a b (.affine x y)) (hq : onCurve a b (.affine x z))
    (hsum : add a (.affine x y) (.affine x z) ≠ .infinity) : y = z := by
  rcases square_eq_square_cases y z (hp.trans hq.symm) with he | hn
  · exact he
  · exact False.elim (hsum (by simp [add, hn]))

theorem assoc_reverse (a b : F) (p q r : Point F)
    (hp : onCurve a b p) (hq : onCurve a b q) (hr : onCurve a b r)
    (h : add a (add a r q) p = add a r (add a q p)) :
    add a (add a p q) r = add a p (add a q r) := by
  rw [add_comm a b p q hp hq,
    add_comm a b (add a q p) r (add_onCurve a b q p hq hp) hr,
    ← h, add_comm a b r q hr hq,
    add_comm a b (add a q r) p (add_onCurve a b q r hq hr) hp]

theorem add_assoc_zero_left (a b : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (p q r : Point F) (hp : onCurve a b p) (hr : onCurve a b r)
    (h : add a p q = .infinity) :
    add a (add a p q) r = add a p (add a q r) := by
  have hq := (add_eq_infinity_iff a p q).mp h
  rw [h, infinity_add, hq, add_neg_cancel_left a b h2 hnozero p r hp hr]

theorem add_assoc_zero_sum_left (a b : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (p q r : Point F) (hp : onCurve a b p) (hq : onCurve a b q)
    (h : add a (add a p q) r = .infinity) :
    add a (add a p q) r = add a p (add a q r) := by
  have hu := add_onCurve a b p q hp hq
  have hnp := neg_onCurve a b p hp
  have hnu := neg_onCurve a b (add a p q) hu
  have hr := (add_eq_infinity_iff a (add a p q) r).mp h
  have hqu : q = add a (add a p q) (neg p) := by
    rw [add_comm a b (add a p q) (neg p) hu hnp]
    exact (neg_add_cancel_left a b h2 hnozero p q hp hq).symm
  have hqr : add a q r = neg p := by
    rw [hr, add_comm a b q (neg (add a p q)) hq hnu]
    calc
      add a (neg (add a p q)) q =
          add a (neg (add a p q)) (add a (add a p q) (neg p)) := congrArg _ hqu
      _ = neg p := neg_add_cancel_left a b h2 hnozero (add a p q) (neg p) hu hnp
  rw [h, hqr, add_neg_cancel]

theorem second_sum_x_ne (a b x y u v : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (r : Point F) (hp : onCurve a b (.affine x y)) (hr : onCurve a b r)
    (hrne : r ≠ .infinity) (hsum : add a (.affine x y) r = .affine u v)
    (hfinal : add a (.affine x y) (.affine u v) ≠ .infinity) : u ≠ x := by
  intro hx
  subst u
  have hv : onCurve a b (.affine x v) := hsum ▸ add_onCurve a b (.affine x y) r hp hr
  have hy := same_x_of_add_ne_infinity a b x y v hp hv hfinal
  subst v
  have he : add a (.affine x y) r = add a (.affine x y) .infinity :=
    hsum.trans (add_infinity _ _).symm
  exact hrne (add_left_cancel a b h2 hnozero (.affine x y) r .infinity hp hr trivial he)

theorem add_exchange_impossible (a b : F)
    (h2 : (2 : F) ≠ 0) (hnozero : ∀ x, x * x * x + a * x + b ≠ 0)
    (p q r : Point F) (hp : onCurve a b p) (hq : onCurve a b q) (hr : onCurve a b r)
    (hqne : q ≠ .infinity) (hfirst : add a p q = r) (hsecond : add a q r = p) : False := by
  have hnq := neg_onCurve a b q hq
  have hcancel : add a (neg q) r = p := by
    rw [← hfirst, add_comm a b p q hp hq]
    exact neg_add_cancel_left a b h2 hnozero q p hq hp
  have heq := add_right_cancel a b h2 hnozero r q (neg q) hr hq hnq
    (hsecond.trans hcancel.symm)
  cases q with
  | infinity => exact hqne rfl
  | affine x y =>
    have hy : y = -y := (Point.affine.inj heq).2
    exact affine_double_den a b x y h2 hnozero hq (by grind only)

omit [DecidableEq F] in
theorem secant_x_swap (x y u v : F) :
    ((v - y) / (u - x)) ^ 2 - x - u = ((y - v) / (x - u)) ^ 2 - u - x := by
  have hd : x - u = -(u - x) := by grind only
  simp only [Field.div_eq_mul_inv, hd, Field.inv_neg]
  grind only

end K256.Proofs.Generate.Curve.Group.Affine
