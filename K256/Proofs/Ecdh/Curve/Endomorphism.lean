import K256.Proofs.Generate.Curve

set_option autoImplicit false

namespace K256.Proofs.Ecdh.Curve

open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve
open Group Group.CurveArithmetic
open Lean.Grind Fin.NatCast

private def scaleX {F : Type} [Mul F] (b : F) : Affine.Point F → Affine.Point F
  | .infinity => .infinity
  | .affine x y => .affine (b * x) y

private theorem scaleX_onCurve {F : Type} [Field F] (b c : F)
    (hb : b * b * b = 1) (p : Affine.Point F)
    (hp : Affine.onCurve 0 c p) : Affine.onCurve 0 c (scaleX b p) := by
  cases p with
  | infinity => trivial
  | affine x y =>
    simp only [Affine.onCurve, scaleX] at hp ⊢
    calc
      y * y = x * x * x + 0 * x + c := hp
      _ = (b * b * b) * (x * x * x) + c := by rw [hb]; grind
      _ = (b * x) * (b * x) * (b * x) + 0 * (b * x) + c := by grind only

private theorem scaleX_add {F : Type} [Field F] [DecidableEq F] (b : F)
    (hb : b * b * b = 1) (p q : Affine.Point F) :
    scaleX b (Affine.add 0 p q) = Affine.add 0 (scaleX b p) (scaleX b q) := by
  cases p with
  | infinity => rfl
  | affine x₁ y₁ =>
    cases q with
    | infinity => rfl
    | affine x₂ y₂ =>
      have hb0 : b ≠ 0 := by
        intro h
        exact Field.zero_ne_one (by simpa only [h, Semiring.zero_mul] using hb)
      have hbinv : b⁻¹ = b * b := by
        calc
          b⁻¹ = (b * b * b) * b⁻¹ := by rw [hb, Semiring.one_mul]
          _ = (b * b) * (b * b⁻¹) := Semiring.mul_assoc ..
          _ = b * b := by rw [Field.mul_inv_cancel hb0, Semiring.mul_one]
      have heq : b * x₁ = b * x₂ ↔ x₁ = x₂ := by
        constructor
        · intro h
          have h' := congrArg (fun x => b⁻¹ * x) h
          simpa only [← Semiring.mul_assoc, Field.inv_mul_cancel hb0, Semiring.one_mul] using h'
        · exact congrArg (b * ·)
      simp only [Affine.add, scaleX, heq]
      by_cases hzero : x₁ = x₂ ∧ y₁ + y₂ = 0
      · simp only [ite_eq_left hzero]
      · simp only [ite_eq_right hzero]
        let s := if x₁ = x₂ then (3 * x₁ * x₁ + 0) / (2 * y₁)
                 else (y₂ - y₁) / (x₂ - x₁)
        have hs : (if x₁ = x₂ then (3 * (b * x₁) * (b * x₁) + 0) / (2 * y₁)
                   else (y₂ - y₁) / (b * x₂ - b * x₁)) = b * b * s := by
          dsimp only [s]
          split
          · simp only [Field.div_eq_mul_inv]
            grind only
          · have hx : b * x₂ - b * x₁ = b * (x₂ - x₁) := by grind only
            simp only [hx, Field.div_eq_mul_inv, Field.inv_mul, hbinv]
            grind only
        rw [hs]
        change Affine.Point.affine (b * (s * s - x₁ - x₂)) (s * (x₁ - (s * s - x₁ - x₂)) - y₁) =
          .affine ((b * b * s) * (b * b * s) - b * x₁ - b * x₂)
            ((b * b * s) * (b * x₁ - ((b * b * s) * (b * b * s) - b * x₁ - b * x₂)) - y₁)
        have hx : b * (s * s - x₁ - x₂) =
            (b * b * s) * (b * b * s) - b * x₁ - b * x₂ := by
          calc
            _ = (b * b * b) * (b * s * s) - b * x₁ - b * x₂ := by rw [hb]; grind
            _ = _ := by grind only
        rw [← hx]
        congr 1
        calc
          _ = (b * b * b) * (s * (x₁ - (s * s - x₁ - x₂))) - y₁ := by rw [hb]; grind
          _ = _ := by grind only

private def beta : Fp :=
  (0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee : Nat)

private theorem beta_cube : beta * beta * beta = 1 := by decide +kernel

private theorem domain_a_zero : (domain.a : Fp) = 0 := by decide +kernel

private theorem endomorphism_decode (p : Affine.Point Fp) :
    endomorphism (decodePoint p) = decodePoint (scaleX beta p) := by
  cases p with
  | infinity => rfl
  | affine x y =>
    change Curve.Point.affine
      (x.val * beta.val % domain.p) y.val =
      Curve.Point.affine (beta.val * x.val % domain.p) y.val
    rw [Nat.mul_comm x.val]

private theorem endomorphism_onCurve (p : Curve.Point) (hp : Curve.onCurve domain p = true) :
    Curve.onCurve domain (endomorphism p) = true := by
  have h := encode_onCurve p hp
  rw [domain_a_zero] at h
  rw [← decode_encode p hp, endomorphism_decode]
  apply decode_onCurve
  rw [domain_a_zero]
  exact scaleX_onCurve beta (domain.b : Fp) beta_cube _ h

private theorem endomorphism_add (p q : Curve.Point)
    (hp : Curve.onCurve domain p = true) (hq : Curve.onCurve domain q = true) :
    endomorphism (Curve.add domain p q) =
      Curve.add domain (endomorphism p) (endomorphism q) := by
  have hencode (r : Curve.Point) :
      encodePoint (endomorphism r) = scaleX beta (encodePoint r) := by
    cases r <;> simp only [endomorphism, encodePoint, scaleX, cast_mod, Semiring.natCast_mul,
      beta, CommSemiring.mul_comm]
  rw [← decode_encode_add p q hp hq, endomorphism_decode, encode_add p q hp hq,
    ← decode_encode_add _ _ (endomorphism_onCurve p hp) (endomorphism_onCurve q hq),
    encode_add _ _ (endomorphism_onCurve p hp) (endomorphism_onCurve q hq),
    hencode p, hencode q, domain_a_zero, scaleX_add beta beta_cube]

theorem endomorphism_generatorMultiple (a : Int) :
    endomorphism (generatorMultiple a) = generatorMultiple (eigenvalue * a) := by
  have hone : generatorMultiple 1 = domain.G := by decide +kernel
  have hnat (n : Nat) :
      endomorphism (generatorMultiple (n : Int)) = generatorMultiple (eigenvalue * (n : Int)) := by
    induction n with
    | zero => simp only [Int.natCast_zero, Int.mul_zero]; decide +kernel
    | succ n ih =>
      rw [Int.natCast_succ, ← generatorMultiple_add, endomorphism_add _ _
        (generatorMultiple_onCurve _) (generatorMultiple_onCurve _), ih, hone,
        endomorphism_generator, generatorMultiple_add, Int.mul_add, Int.mul_one]
  have hn : (0 : Int) < domain.n := by decide +kernel
  have ha : ((a % (domain.n : Int)).toNat : Int) = a % (domain.n : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hn))
  have hbase : generatorMultiple ((a % (domain.n : Int)).toNat : Int) = generatorMultiple a := by
    simp only [generatorMultiple, ha, Int.emod_emod]
  have hresult : generatorMultiple (eigenvalue * ((a % (domain.n : Int)).toNat : Int)) =
      generatorMultiple (eigenvalue * a) := by
    unfold generatorMultiple
    rw [ha, Int.mul_emod eigenvalue (a % (domain.n : Int)), Int.emod_emod, ← Int.mul_emod]
  rw [← hbase, hnat, hresult]

end K256.Proofs.Ecdh.Curve
