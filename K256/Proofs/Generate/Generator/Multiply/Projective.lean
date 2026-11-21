import K256.Proofs.Generate.Curve.Group.Concrete
import K256.Proofs.Generate.Generator.Affine.Repr

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Proofs.Generate.Curve.Group.CurveArithmetic Standards.SECG.ECC

structure Projective where
  x : Fp
  y : Fp
  z : Fp

namespace Projective

def valid (p : Projective) : Prop :=
  p.y * p.y * p.z = p.x * p.x * p.x + 7 * p.z * p.z * p.z ∧
    (p.x ≠ 0 ∨ p.y ≠ 0 ∨ p.z ≠ 0)

def value (p : Projective) : Curve.Point := Affine.toAffine p.x p.y p.z

def add (p q : Projective) : Projective :=
  let xx := p.x * q.x
  let yy := p.y * q.y
  let zz := p.z * q.z
  let xy := (p.x + p.y) * (q.x + q.y) - (xx + yy)
  let yz := (p.y + p.z) * (q.y + q.z) - (yy + zz)
  let xz := (p.x + p.z) * (q.x + q.z) - (xx + zz)
  let minus := yy - 21 * zz
  let plus := yy + 21 * zz
  ⟨xy * minus - 21 * yz * xz, plus * minus + 63 * xx * xz,
    yz * plus + 3 * xx * xy⟩

def double (p : Projective) : Projective :=
  let yy := p.y * p.y
  let zz := p.z * p.z
  let minus := yy - 63 * zz
  ⟨2 * (p.x * p.y) * minus, minus * (yy + 21 * zz) + 168 * yy * zz,
    8 * (yy * p.y) * p.z⟩

def neg (p : Projective) : Projective := ⟨p.x, -p.y, p.z⟩

theorem neg_valid {p : Projective} (h : p.valid) : p.neg.valid := by
  obtain ⟨hc, hn⟩ := h
  simp only [valid, neg]
  exact ⟨by rw [show -p.y * -p.y = p.y * p.y by grind only]; exact hc, by grind only⟩

theorem neg_value (p : Projective) :
    p.neg.value = Curve.neg Standards.SECG.DomainParameters.Secp256k1.domain p.value := by
  by_cases hz : p.z.val = 0
  · simp only [value, neg, Affine.toAffine, hz, ite_true, Curve.neg]
  · simp only [value, neg, Affine.toAffine, hz, ite_false, Curve.neg, Curve.Point.affine.injEq,
      true_and, Curve.fieldSub, Nat.zero_mod, Nat.zero_add]
    let k : Fp := Affine.inverse p.z
    change (-p.y * k).val = (_ - (p.y * k).val % _) % _
    rw [show -p.y * k = -(p.y * k) by grind only, Fin.val_neg', Nat.mod_eq_of_lt (p.y * k).isLt]

end Projective
end K256.Proofs.Generate.Generator.Multiply
