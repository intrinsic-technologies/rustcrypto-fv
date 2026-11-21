import K256.Proofs.Common.Point.AddWords.Product
import K256.Proofs.Common.Point.DoubleWords.Field
import K256.Proofs.Common.Field.Multiply

namespace K256.Proofs.Common.Point.AddWords.Raw

open Field Field.Multiply.SqrtSchedule

def schedule : ProductKind → Product.Schedule
  | .xx | .zz | .yz | .xz => .diagonal
  | .yy | .xy => .reverseCarry
  | .xLeft | .zLeft | .zRight => .fullCarry
  | .xRight => .xRight
  | .yLeft => .yLeft
  | .yRight => .yRight

def product (k : ProductKind) (a b : Limbs) : Limbs := Product.words (schedule k) b a

def add : PointWords → PointWords → PointWords := addWith product

private theorem product_eq (k : ProductKind) {a b : Limbs} {x y : Fin modulus}
    {m n : Nat} (ha : FieldRepr a x m) (hb : FieldRepr b y n) (hm : m ≤ 8) (hn : n ≤ 8) :
    product k a b = Field.mulWords a b :=
  (Product.words_eq _ _ _ (hb.mono hn) (ha.mono hm)).trans (mulWords_comm _ _)

theorem add_eq (p q : PointWords)
    (pBound : ∀ w ∈ [p.x, p.y, p.z], ∃ x, FieldRepr w x 1)
    (qBound : ∀ w ∈ [q.x, q.y, q.z], ∃ x, FieldRepr w x 1) :
    add p q = AddWords.add p q := by
  obtain ⟨_, px⟩ := pBound p.x (.head _)
  obtain ⟨_, py⟩ := pBound p.y (.tail _ (.head _))
  obtain ⟨_, pz⟩ := pBound p.z (.tail _ (.tail _ (.head _)))
  obtain ⟨_, qx⟩ := qBound q.x (.head _)
  obtain ⟨_, qy⟩ := qBound q.y (.tail _ (.head _))
  obtain ⟨_, qz⟩ := qBound q.z (.tail _ (.tail _ (.head _)))
  have rep {a b : Limbs} {x y : Fin modulus} {m n : Nat} (ha : FieldRepr a x m)
      (hb : FieldRepr b y n) (hm : m ≤ 8) (hn : n ≤ 8) :=
    mulWords_repr _ _ _ _ (ha.mono hm) (hb.mono hn)
  have xx := rep px qx (by decide) (by decide)
  have yy := rep py qy (by decide) (by decide)
  have zz := rep pz qz (by decide) (by decide)
  have pxy := sum_repr px py (by decide)
  have qxy := sum_repr qx qy (by decide)
  have pyz := sum_repr py pz (by decide)
  have qyz := sum_repr qy qz (by decide)
  have pxz := sum_repr px pz (by decide)
  have qxz := sum_repr qx qz (by decide)
  have xy := sum_repr (rep pxy qxy (by decide) (by decide))
    (negate_repr (sum_repr xx yy (by decide)) (by decide)) (by decide)
  have yz := sum_repr (rep pyz qyz (by decide) (by decide))
    (negate_repr (sum_repr yy zz (by decide)) (by decide)) (by decide)
  have xz := sum_repr (rep pxz qxz (by decide) (by decide))
    (negate_repr (sum_repr xx zz (by decide)) (by decide)) (by decide)
  have bzz := weak_repr (scale_repr 21 zz (by decide)) (by decide)
  have minus := sum_repr yy (negate_repr bzz (by decide)) (by decide)
  have plus := sum_repr yy bzz (by decide)
  have byz := weak_repr (scale_repr 3 (weak_repr (scale_repr 7 yz (by decide)) (by decide))
    (by decide)) (by decide)
  have xx3 := scale_repr 3 xx (by decide)
  have bxx := weak_repr (scale_repr 7 (weak_repr (scale_repr 9 xx (by decide)) (by decide))
    (by decide)) (by decide)
  simp only [add, AddWords.add, addWith, pairsWith,
    product_eq .xx px qx (by decide) (by decide), product_eq .yy py qy (by decide) (by decide),
    product_eq .zz pz qz (by decide) (by decide), product_eq .xy pxy qxy (by decide) (by decide),
    product_eq .yz pyz qyz (by decide) (by decide), product_eq .xz pxz qxz (by decide) (by decide),
    product_eq .xLeft xy minus (by decide) (by decide), product_eq .xRight byz xz (by decide) (by decide),
    product_eq .yLeft plus minus (by decide) (by decide), product_eq .yRight bxx xz (by decide) (by decide),
    product_eq .zLeft yz plus (by decide) (by decide), product_eq .zRight xx3 xy (by decide) (by decide)]

end K256.Proofs.Common.Point.AddWords.Raw
