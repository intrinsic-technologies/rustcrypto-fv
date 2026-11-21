import K256.Proofs.Generate.Generator.Multiply.Projective

namespace K256.Proofs.Generate.Generator.Multiply.Projective

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve.Group
open CurveArithmetic Lean.Grind Fin.NatCast Fin.IntCast
open K256.Proofs.Generate.Curve

private abbrev AP := Group.Affine.Point Fp

private def lift : AP → Projective
  | .infinity => ⟨0, 1, 0⟩
  | .affine x y => ⟨x, y, 1⟩

private def scale (k : Fp) (p : Projective) : Projective :=
  ⟨k * p.x, k * p.y, k * p.z⟩

private theorem no_root (x : Fp) : x * x * x + 7 ≠ 0 := by
  have h := secp256k1_cubic_ne_zero x
  change x * x * x + 0 * x + 7 ≠ 0 at h
  simpa only [Semiring.zero_mul, Semiring.add_zero] using h

private theorem y_nonzero {x y : Fp} (hc : y * y = x * x * x + 7) : y ≠ 0 := by
  intro h
  apply no_root x
  rw [← hc, h, Semiring.zero_mul]

private theorem ext_coords {p q : Projective} (hx : p.x = q.x) (hy : p.y = q.y)
    (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  congr

private theorem scale_add (k l : Fp) (p q : Projective) :
    (scale k p).add (scale l q) = scale (k * l * (k * l)) (p.add q) := by
  apply ext_coords <;> dsimp only [scale, add] <;> grind only

private theorem scale_scale (k l : Fp) (p : Projective) :
    scale k (scale l p) = scale (k * l) p := by
  apply ext_coords <;> dsimp only [scale] <;> grind only

private theorem normalize (p : Projective) (hp : p.valid) :
    ∃ (a : AP) (k : Fp), k ≠ 0 ∧ p = scale k (lift a) ∧
      Group.Affine.onCurve (0 : Fp) 7 a := by
  obtain ⟨hc, hn⟩ := hp
  by_cases hz : p.z = 0
  · have hx : p.x = 0 := by grind only
    have hy : p.y ≠ 0 := by grind only
    refine ⟨.infinity, p.y, hy, ?_, trivial⟩
    apply ext_coords <;> dsimp only [lift, scale] <;> grind only
  · have hi := fp_mul_inv hz
    refine ⟨.affine (p.x * p.z⁻¹) (p.y * p.z⁻¹), p.z, hz, ?_, ?_⟩
    · apply ext_coords <;> dsimp only [lift, scale] <;> grind only
    · change _ * _ = _ * _ * _ + 0 * _ + 7
      grind only

private theorem scaled_value (a : AP) (k : Fp) (hk : k ≠ 0) :
    (scale k (lift a)).value = decodePoint a := by
  cases a with
  | infinity =>
    simp only [scale, lift, value, Affine.toAffine, Semiring.mul_zero, Fin.val_zero,
      ite_true, decodePoint]
  | affine x y =>
    have hv : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp only [scale, lift, value, Affine.toAffine, Semiring.mul_one, hv, ite_false, decodePoint]
    change Curve.Point.affine (k * x * k⁻¹).val (k * y * k⁻¹).val = _
    have hi := fp_mul_inv hk
    congr 1 <;> apply congrArg Fin.val <;> grind only

private theorem scaled_valid (a : AP) (k : Fp) (hk : k ≠ 0)
    (hc : Group.Affine.onCurve (0 : Fp) 7 a) :
    (scale k (lift a)).valid := by
  cases a with
  | infinity =>
    simp only [valid, scale, lift, Semiring.mul_zero, Semiring.mul_one,
      Semiring.add_zero]
    exact ⟨True.intro, Or.inr (Or.inl hk)⟩
  | affine x y =>
    change y * y = x * x * x + 0 * x + 7 at hc
    refine ⟨?_, Or.inr (Or.inr ?_)⟩
    · dsimp only [scale, lift]
      grind only
    · simpa only [scale, lift, Semiring.mul_one] using hk

private theorem decoded_add (a b : AP)
    (ha : Group.Affine.onCurve (0 : Fp) 7 a)
    (hb : Group.Affine.onCurve (0 : Fp) 7 b) :
    decodePoint (Group.Affine.add 0 a b) =
      Curve.add domain (decodePoint a) (decodePoint b) := by
  have hd₁ := decode_onCurve a ha
  have hd₂ := decode_onCurve b hb
  have cancel (t : AP) : encodePoint (decodePoint t) = t := by
    cases t with
    | infinity => rfl
    | affine x y =>
      change Group.Affine.Point.affine (x.val : Fp) (y.val : Fp) = _
      congr 1 <;> apply Fin.ext <;> apply Nat.mod_eq_of_lt <;> exact Fin.isLt _
  rw [← decode_encode_add _ _ hd₁ hd₂, encode_add _ _ hd₁ hd₂, cancel, cancel]
  rfl

private theorem cubic_zero (u v : Fp) (hc : u * u * u + 7 * v * v * v = 0) :
    u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · grind only
  · have hi := fp_mul_inv hv
    exact False.elim (no_root (u * v⁻¹) (by grind only))

private theorem distinct_scale (x y u v : Fp)
    (hl : y * y = x * x * x + 7) (hr : v * v = u * u * u + 7) (hx : x ≠ u) :
    let r := (lift (.affine x y)).add (lift (.affine u v))
    let s := (v - y) / (u - x)
    let tx := s * s - x - u
    r.z ≠ 0 ∧ r = scale r.z (lift (.affine tx (s * (x - tx) - y))) := by
  have hd : u - x ≠ 0 := by grind only
  have hi := fp_mul_inv hd
  let r := (lift (.affine x y)).add (lift (.affine u v))
  let s := (v - y) / (u - x)
  let tx := s * s - x - u
  have ex : r.x = r.z * tx := by
    dsimp only [r, s, tx, lift, add, Field.div_eq_mul_inv]
    grind only
  have ey : r.y = r.z * (s * (x - tx) - y) := by
    dsimp only [r, s, tx, lift, add, Field.div_eq_mul_inv]
    grind only
  have nz : r.z ≠ 0 := by
    intro hz
    have h₁ : r.x = 0 := by rw [ex, hz, Semiring.zero_mul]
    have h₂ : r.y = 0 := by rw [ey, hz, Semiring.zero_mul]
    have h : (x * v + y * u) * (x * v + y * u) * (x * v + y * u) + 7 * (y + v) * (y + v) * (y + v) = 0 := by
      clear ex ey hi
      dsimp only [r, add, lift] at h₁ h₂ hz
      grind only
    have h₃ := cubic_zero _ _ h
    have hy := y_nonzero hl
    obtain ⟨ha, hb⟩ := h₃
    clear h h₁ h₂ hz hi ex ey hl hr
    grind only
  exact ⟨nz, ext_coords ex ey (Semiring.mul_one _).symm⟩

private theorem tangent_scale (x y : Fp) (hl : y * y = x * x * x + 7) :
    let r := (lift (.affine x y)).add (lift (.affine x y))
    let s := (3 * x * x) / (2 * y)
    let tx := s * s - x - x
    r.z ≠ 0 ∧ r = scale r.z (lift (.affine tx (s * (x - tx) - y))) := by
  have hy := y_nonzero hl
  have ht := secp256k1_two_ne_zero
  have hd : 2 * y ≠ 0 := fun h => (Field.of_mul_eq_zero h).elim ht hy
  have hi := fp_mul_inv hd
  dsimp only [lift, add, scale, Field.div_eq_mul_inv]
  constructor
  · grind only
  · apply ext_coords <;> dsimp only <;> grind only

private theorem opposite_scale (x y : Fp) (hl : y * y = x * x * x + 7) :
    let r := (lift (.affine x y)).add (lift (.affine x (-y)))
    r.y ≠ 0 ∧ r = scale r.y (lift .infinity) := by
  let r := (lift (.affine x y)).add (lift (.affine x (-y)))
  let t := (lift (.affine x y)).add (lift (.affine x y))
  have hty : t.y = r.y := by
    dsimp only [t, r, lift, add]
    grind only
  let s := (3 * x * x) / (2 * y)
  let tx := s * s - x - x
  have hy := y_nonzero hl
  have ht := secp256k1_two_ne_zero
  have hd : 2 * y ≠ 0 := fun h => (Field.of_mul_eq_zero h).elim ht hy
  have hc := Group.Affine.tangent_onCurve (0 : Fp) 7 x y s (by grind only)
      (by dsimp only [s]; rw [Field.div_mul_cancel hd]; grind only)
  have hn : s * (x - tx) - y ≠ 0 := y_nonzero (x := tx) (by
    simpa only [Semiring.zero_mul, Semiring.add_zero, tx] using hc)
  obtain ⟨hz, he⟩ := tangent_scale x y hl
  have he' := congrArg Projective.y he
  change t.y = t.z * (s * (x - tx) - y) at he'
  constructor
  · change r.y ≠ 0
    rw [← hty, he']
    exact fun h => (Field.of_mul_eq_zero h).elim hz hn
  · apply ext_coords <;> dsimp only [add, lift, scale] <;> grind only

private theorem lift_add (a b : AP) (ha : Group.Affine.onCurve (0 : Fp) 7 a)
    (hb : Group.Affine.onCurve (0 : Fp) 7 b) :
    ∃ k : Fp, k ≠ 0 ∧ (lift a).add (lift b) = scale k (lift (Group.Affine.add 0 a b)) := by
  cases a with
  | infinity =>
    cases b with
    | infinity =>
      refine ⟨1, by decide +kernel, ?_⟩
      apply ext_coords <;> decide +kernel
    | affine u v =>
      have hc : v * v = u * u * u + 7 := by simpa only [Group.Affine.onCurve, Semiring.zero_mul,
        Semiring.add_zero] using hb
      refine ⟨v, y_nonzero hc, ?_⟩
      apply ext_coords <;> dsimp only [scale, add, lift, Group.Affine.add] <;> grind only
  | affine x y =>
    have hl : y * y = x * x * x + 7 := by simpa only [Group.Affine.onCurve, Semiring.zero_mul,
      Semiring.add_zero] using ha
    cases b with
    | infinity =>
      refine ⟨y, y_nonzero hl, ?_⟩
      apply ext_coords <;> dsimp only [scale, add, lift, Group.Affine.add] <;> grind only
    | affine u v =>
      have hr : v * v = u * u * u + 7 := by simpa only [Group.Affine.onCurve, Semiring.zero_mul,
        Semiring.add_zero] using hb
      by_cases hx : x = u
      · subst u
        by_cases hsum : y + v = 0
        · have hv : v = -y := by grind only
          subst v
          simp only [Group.Affine.add, hsum, and_self, ite_true]
          exact ⟨_, opposite_scale x y hl⟩
        · have hv := (Group.Affine.square_eq_square_cases y v (hl.trans hr.symm)).resolve_right hsum
          subst v
          simp only [Group.Affine.add, hsum, and_false, ite_false, ite_true, Semiring.add_zero]
          exact ⟨_, tangent_scale x y hl⟩
      · simp only [Group.Affine.add, hx, false_and, ite_false]
        exact ⟨_, distinct_scale x y u v hl hr hx⟩

theorem add_correct (p q : Projective) (hp : p.valid) (hq : q.valid) :
    (p.add q).valid ∧ (p.add q).value = Curve.add domain p.value q.value := by
  obtain ⟨a, k, hk, rfl, ha⟩ := normalize p hp
  obtain ⟨b, l, hl, rfl, hb⟩ := normalize q hq
  obtain ⟨t, ht, he⟩ := lift_add a b ha hb
  rw [scale_add, he, scale_scale, scaled_value a k hk, scaled_value b l hl]
  have mul_nz {u v : Fp} (hu : u ≠ 0) (hv : v ≠ 0) : u * v ≠ 0 :=
    fun h => (Field.of_mul_eq_zero h).elim hu hv
  have hn := mul_nz (mul_nz (mul_nz hk hl) (mul_nz hk hl)) ht
  exact ⟨scaled_valid _ _ hn (Group.Affine.add_onCurve _ _ _ _ ha hb),
    (scaled_value _ _ hn).trans (decoded_add a b ha hb)⟩

end K256.Proofs.Generate.Generator.Multiply.Projective
