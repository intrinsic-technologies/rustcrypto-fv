import K256.Proofs.Common.Point.DoubleWords.Model
import K256.Proofs.Common.Point.DoubleWords.ReplayCorrect.FinalProducts
import K256.Proofs.Common.Point.DoubleWords.ReplayCorrect.Linearity

namespace K256.Proofs.Common.Point.DoubleWords.Replay

open Field Field.Multiply Field.Multiply.SqrtSchedule AddWords

local macro "w[" i:num "]" : term =>
  `($(Lean.mkIdent (Lean.Name.mkSimple s!"w{i.getNat}"))
    $(Lean.mkIdent `p) $(Lean.mkIdent `yy) $(Lean.mkIdent `zz) $(Lean.mkIdent `sp))

set_option maxRecDepth 1500 in
set_option maxHeartbeats 1500000 in
theorem output_eq (p : PointWords) (sp : Word) {x y z : Fin modulus}
    (hx : FieldRepr p.x x 1) (hy : FieldRepr p.y y 1) (hz : FieldRepr p.z z 1) :
    output p (squareWords p.y) (squareWords p.z) sp = DoubleWords.double p := by
  let yy := squareWords p.y
  let zz := squareWords p.z
  let xy := mulWords p.x p.y
  let yyy := mulWords yy p.y
  let yyzz := mulWords yy zz
  let triple := weak (scale 21 zz)
  let nine := weak (scale 3 triple)
  let minus := sum yy (negate 1 nine)
  let plus := sum yy triple
  have hyy := squareWords_repr _ _ (hy.mono (by decide))
  have hzz := squareWords_repr _ _ (hz.mono (by decide))
  have hxy := mulWords_repr _ _ _ _ (hx.mono (by decide)) (hy.mono (by decide))
  have hyyy := mulWords_repr _ _ _ _ (hyy.mono (by decide)) (hy.mono (by decide))
  have hxy2 := scale_repr 2 hxy (by decide)
  have htriple := weak_repr (scale_repr 21 hzz (by decide)) (by decide)
  have hnine := weak_repr (scale_repr 3 htriple (by decide)) (by decide)
  have hminus := sum_repr hyy (negate_repr hnine (by decide)) (by decide)
  have hplus := sum_repr hyy htriple (by decide)
  have eXY := (xy_words p yy zz sp).trans
    ((Product.words_eq .reverseCarry _ _ (hy.mono (by decide)) (hx.mono (by decide))).trans
      (mulWords_comm p.y p.x))
  have eX2 := (xyDoubled p yy zz sp).trans (congrArg (scale 2) eXY)
  have eYYY := (yyy_words p yy zz sp).trans
    ((Product.words_eq .reverseCarry _ _ (hy.mono (by decide)) (hyy.mono (by decide))).trans
      (mulWords_comm p.y yy))
  have eYYZZ := (yyzz_words p yy zz sp).trans
    ((Product.words_eq .diagonal _ _ (hzz.mono (by decide)) (hyy.mono (by decide))).trans
      (mulWords_comm zz yy))
  have eZIn : #v[w[12], w[13], w[14], w[15], w[16]] = p.z := by
    apply Vector.ext
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with
      rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨eMinus, ePlus⟩ := doublingSources p yy zz sp
  have topX : w[388].toNat * w[368].toNat < 2^116 := by
    change (#v[w[374], w[375], w[378], w[386], w[388]])[4].toNat *
      (#v[w[326], w[339], w[349], w[363], w[368]])[4].toNat < 2^116
    rw [eX2, eMinus]
    exact top_product_lt (hxy2.mono (by decide)) (hminus.mono (by decide))
  have topZ : w[1050].toNat * w[16].toNat < 2^116 := by
    change (#v[w[1052], w[1053], w[1054], w[1055], w[1050]])[4].toNat *
      (#v[w[12], w[13], w[14], w[15], w[16]])[4].toNat < 2^116
    rw [eYYY, eZIn]
    exact top_product_lt (hyyy.mono (by decide)) (hz.mono (by decide))
  have eX := outX_words p yy zz sp topX
  rw [eMinus, eX2] at eX
  have xOut : (output p yy zz sp).x = mulWords (scale 2 xy) minus := eX.trans
    ((Product.words_eq .diagonal _ _ (hminus.mono (by decide)) (hxy2.mono (by decide))).trans
      (mulWords_comm minus (scale 2 xy)))
  have eY := outY_words p yy zz sp
  rw [ePlus, eMinus] at eY
  have yRaw : #v[w[1411], w[1451], w[1488], w[1521], w[1500]] = mulWords minus plus :=
    eY.trans ((Product.words_eq .diagonal _ _ (hplus.mono (by decide)) (hminus.mono (by decide))).trans
      (mulWords_comm plus minus))
  have eCorr := correctionWords p yy zz sp
  rw [eYYZZ] at eCorr
  have yOut : (output p yy zz sp).y =
      weak (sum (mulWords minus plus) (scale 7 (weak (scale 24 yyzz)))) := by
    rw [normalizedY, yRaw, eCorr]
  have eZ := outZ_words p yy zz sp topZ
  rw [eZIn, eYYY] at eZ
  have zRaw := eZ.trans
    ((Product.words_eq .diagonal _ _ (hz.mono (by decide)) (hyyy.mono (by decide))).trans
      (mulWords_comm p.z yyy))
  have zBound : w[1263].toNat < 2^61 := by
    change (#v[w[1167] &&& 0xfffffffffffff, w[1206] &&& 0xfffffffffffff,
      w[1244] &&& 0xfffffffffffff, w[1257] &&& 0xfffffffffffff, w[1263]])[4].toNat < _
    rw [zRaw]
    have h := (mulWords_repr _ _ _ _ (hyyy.mono (by decide)) (hz.mono (by decide))).1 (4 : Fin 5)
    change (mulWords yyy p.z)[4].toNat ≤ 2 * (2^48 - 1) at h
    omega
  have zOut : (output p yy zz sp).z = weak (scale 8 (mulWords yyy p.z)) := by
    rw [normalizedZ p yy zz sp zBound, zRaw]
  change PointWords.mk (output p yy zz sp).x (output p yy zz sp).y (output p yy zz sp).z = _
  rw [xOut, yOut, zOut]
  rfl

end K256.Proofs.Common.Point.DoubleWords.Replay
