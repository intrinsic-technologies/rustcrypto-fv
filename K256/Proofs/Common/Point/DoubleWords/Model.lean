import K256.Proofs.Common.Point.DoubleWords.Field
import K256.Proofs.Common.Field.Multiply
import K256.Proofs.Generate.Generator.Multiply.Projective

namespace K256.Proofs.Common.Point.DoubleWords

open Field AddWords Lean.Grind Fin.NatCast
open Generate.Curve.Group.CurveArithmetic (Fp)
open Generate.Generator.Multiply (Projective)

def double (p : PointWords) : PointWords :=
  let yy := squareWords p.y
  let zz := squareWords p.z
  let xy2 := scale 2 (mulWords p.x p.y)
  let bzz3 := weak (scale 21 zz)
  let bzz9 := weak (scale 3 bzz3)
  let minus := sum yy (negate 1 bzz9)
  let plus := sum yy bzz3
  let correction := scale 7 (weak (scale 24 (mulWords yy zz)))
  ⟨mulWords xy2 minus, weak (sum (mulWords minus plus) correction),
    weak (scale 8 (mulWords (mulWords yy p.y) p.z))⟩

theorem double_repr {words : PointWords} {p : Projective}
    (hx : FieldRepr words.x p.x 1) (hy : FieldRepr words.y p.y 1)
    (hz : FieldRepr words.z p.z 1) :
    FieldRepr (double words).x p.double.x 1 ∧
    FieldRepr (double words).y p.double.y 1 ∧
    FieldRepr (double words).z p.double.z 1 := by
  have mul {al bl a b m n} (ha : FieldRepr al a m) (hb : FieldRepr bl b n)
      (hm : m ≤ 8 := by decide) (hn : n ≤ 8 := by decide) :
      FieldRepr (mulWords al bl) (a * b) 1 :=
    mulWords_repr al bl a b (ha.mono hm) (hb.mono hn)
  have hyy := squareWords_repr _ _ (hy.mono (by decide))
  have hzz := squareWords_repr _ _ (hz.mono (by decide))
  have hxy := scale_repr 2 (mul hx hy) (by decide)
  have hbzz3 := weak_repr (scale_repr 21 hzz (by decide)) (by decide)
  have hbzz9 := weak_repr (scale_repr 3 hbzz3 (by decide)) (by decide)
  have hminus := sum_repr hyy (negate_repr hbzz9 (by decide)) (by decide)
  have hplus := sum_repr hyy hbzz3 (by decide)
  have hcorr := scale_repr 7 (weak_repr (scale_repr 24 (mul hyy hzz) (by decide)) (by decide))
    (by decide)
  have hX := mul hxy hminus
  have hY := weak_repr (sum_repr (mul hminus hplus) hcorr (by decide)) (by decide)
  have hZ := weak_repr (scale_repr 8 (mul (mul hyy hy) hz) (by decide)) (by decide)
  have eX : (2 : Fp) * (p.x * p.y) * (p.y * p.y + -(3 * (21 * (p.z * p.z)))) =
      p.double.x := by
    dsimp only [Projective.double]
    grind only
  have eY : (p.y * p.y + -(3 * (21 * (p.z * p.z)))) * (p.y * p.y + 21 * (p.z * p.z)) +
      7 * (24 * ((p.y * p.y) * (p.z * p.z))) = p.double.y := by
    dsimp only [Projective.double]
    grind only
  have eZ : (8 : Fp) * (p.y * p.y * p.y * p.z) = p.double.z := by
    dsimp only [Projective.double]
    grind only
  exact ⟨eX ▸ hX, eY ▸ hY, eZ ▸ hZ⟩

end K256.Proofs.Common.Point.DoubleWords
