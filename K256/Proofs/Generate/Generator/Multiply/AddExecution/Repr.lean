import K256.Proofs.Common.Point.DoubleWords.Field
import K256.Proofs.Common.Field.Multiply
import K256.Proofs.Generate.Generator.Multiply.Projective

namespace K256.Proofs.Generate.Generator.Multiply.Projective

open K256.Proofs.Common K256.Proofs.Common.Field Point AddWords Curve.Group.CurveArithmetic
open Lean.Grind Fin.NatCast Fin.IntCast

structure WordsRepr (w : PointWords) (p : Projective) : Prop where
  x : FieldRepr w.x p.x 1
  y : FieldRepr w.y p.y 1
  z : FieldRepr w.z p.z 1

private theorem product_repr {a b : Limbs} {x y : Fp} {m n : Nat}
    (ha : FieldRepr a x m) (hb : FieldRepr b y n) (hma : m ≤ 8) (hmb : n ≤ 8) :
    FieldRepr (mulWords a b) (x * y) 1 :=
  mulWords_repr _ _ _ _ (ha.mono hma) (hb.mono hmb)

private theorem pairs_repr {a b c d ac bd : Limbs} {u v w t : Fp}
    (ha : FieldRepr a u 1) (hb : FieldRepr b v 1) (hc : FieldRepr c w 1)
    (hd : FieldRepr d t 1) (hac : FieldRepr ac (u * w) 1) (hbd : FieldRepr bd (v * t) 1) :
    FieldRepr (pairs a b c d ac bd) ((u + v) * (w + t) - (u * w + v * t)) 4 := by
  have h := sum_repr (product_repr (sum_repr ha hb (by decide)) (sum_repr hc hd (by decide))
    (by decide) (by decide)) (negate_repr (sum_repr hac hbd (by decide)) (by decide)) (by decide)
  simpa only [pairs, pairsWith, Ring.sub_eq_add_neg] using h

theorem WordsRepr.add {a b : PointWords} {p q : Projective} (ha : WordsRepr a p)
    (hb : WordsRepr b q) : WordsRepr (AddWords.add a b) (p.add q) := by
  have xx := product_repr ha.x hb.x (by decide) (by decide)
  have yy := product_repr ha.y hb.y (by decide) (by decide)
  have zz := product_repr ha.z hb.z (by decide) (by decide)
  have xy := pairs_repr ha.x ha.y hb.x hb.y xx yy
  have yz := pairs_repr ha.y ha.z hb.y hb.z yy zz
  have xz := pairs_repr ha.x ha.z hb.x hb.z xx zz
  have bzz := weak_repr (scale_repr 21 zz (by decide)) (by decide)
  have minus := sum_repr yy (negate_repr bzz (by decide)) (by decide)
  have plus := sum_repr yy bzz (by decide)
  have byz := weak_repr (scale_repr 3 (weak_repr (scale_repr 7 yz (by decide)) (by decide))
    (by decide)) (by decide)
  have xx3 := scale_repr 3 xx (by decide)
  have bxx := weak_repr (scale_repr 7 (weak_repr (scale_repr 9 xx (by decide)) (by decide))
    (by decide)) (by decide)
  have rx := weak_repr (sum_repr (product_repr xy minus (by decide) (by decide))
    (negate_repr (product_repr byz xz (by decide) (by decide)) (by decide)) (by decide)) (by decide)
  have ry := weak_repr (sum_repr (product_repr plus minus (by decide) (by decide))
    (product_repr bxx xz (by decide) (by decide)) (by decide)) (by decide)
  have rz := weak_repr (sum_repr (product_repr yz plus (by decide) (by decide))
    (product_repr xx3 xy (by decide) (by decide)) (by decide)) (by decide)
  have conv {w : Limbs} {x y : Fp} (h : FieldRepr w x 1) (he : x = y) :
      FieldRepr w y 1 := he ▸ h
  constructor
  · apply conv rx
    dsimp only [Projective.add]
    grind only
  · apply conv ry
    dsimp only [Projective.add]
    grind only
  · exact rz

end K256.Proofs.Generate.Generator.Multiply.Projective
