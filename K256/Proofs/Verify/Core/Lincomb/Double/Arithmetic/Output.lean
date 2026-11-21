import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Words
import K256.Proofs.Common.Point.DoubleWords.ReplayCorrect.Output
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Repr

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open Common.Field Common.Point DoubleWords.Replay Generate.Generator.Multiply

private theorem maskEven (x : Word) (h : x.setWidth 1 = 0#1) :
    x &&& 0xffffffffffffe = x &&& 0xfffffffffffff := by
  have bit := congrArg (fun y : BitVec 1 => y.getLsbD 0) h
  change (x.setWidth 1).getLsbD 0 = false at bit
  simp only [BitVec.getLsbD_setWidth] at bit
  change x.getLsbD 0 = false at bit
  change _ = x &&& ((0xffffffffffffe : Word) ||| 1#64)
  rw [BitVec.and_or_distrib_left, BitVec.and_one_eq_setWidth_ofBool_getLsbD, bit]
  exact BitVec.or_zero.symm

private theorem xMask (p : PointWords) (yy zz : Limbs) (sp : Word) :
    w670 p yy zz sp &&& 0xffffffffffffe = w838 p yy zz sp := by
  apply maskEven
  have le : 1 ≤ 64 := by decide
  have half : (w373 p yy zz sp).setWidth 1 = 0#1 := by
    change BitVec.setWidth 1 (0x1ffffffffffffe : Word) = 0#1
    decide +kernel
  have factor : (w1 p yy zz sp).setWidth 1 = 0#1 := by
    change BitVec.setWidth 1 (0x1000003d10 : Word) = 0#1
    decide +kernel
  simp only [w670, w669, w659, w658, w653, w652, w647, w646, w642, w374, w375,
    w378, w386, BitVec.setWidth_add _ _ le, BitVec.setWidth_mul _ _ le, BitVec.setWidth_and,
    half, factor, BitVec.and_zero, BitVec.mul_zero, BitVec.zero_mul, BitVec.zero_add]

private theorem maskScaleEight (x : Word) :
    (x &&& 0xfffffffffffff) * 8 = (x <<< 3) &&& 0x7ffffffffffff8 := by
  change _ = (x <<< 3) &&& ((0xfffffffffffff : Word) <<< 3)
  rw [← BitVec.shiftLeft_and_distrib, BitVec.shiftLeft_eq_mul_twoPow]
  rfl

open Lean Meta Elab Tactic in
private partial def compareWords (left right : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  if left == right then return ← mkEqRefl left
  if let some h := (← get)[(left, right)]? then return h
  let proof ← if left.getAppFn.constName?.any (·.getPrefix ==
      `K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic) &&
      right.getAppFn.constName?.any (·.getPrefix == `K256.Proofs.Common.Point.DoubleWords.Replay) then do
    let some l ← unfoldDefinition? left true | throwError "expected a verify word"
    let some r ← unfoldDefinition? right true | throwError "expected a doubling word"
    let h ← compareWords l r
    mkExpectedTypeHint h (← mkEq left right)
  else if let (.app f x, .app g y) := (left, right) then do
    if f == g then mkCongrArg f (← compareWords x y)
    else if x == y then mkCongrFun (← compareWords f g) x
    else mkCongr (← compareWords f g) (← compareWords x y)
  else throwError "no word equality for {left} and {right}"
  modify (·.insert (left, right) proof)
  return proof

open Lean Meta Elab Tactic in
local elab "verify_word" : tactic => withMainContext do
  let some (_, lhs, rhs) := (← getMainTarget).eq? | throwError "expected a word equality"
  let mut known := {}
  for d in ← getLCtx do
    if let some (_, l, r) := d.type.eq? then
      known := known.insert (l, r) d.toExpr
  let h ← (compareWords lhs rhs).run' known
  (← getMainGoal).assign h

local macro "atWord " n:ident : term =>
  `($n $(Lean.mkIdent `p) $(Lean.mkIdent `yy) $(Lean.mkIdent `zz) $(Lean.mkIdent `sp))

private theorem limbsCongr {a b c d e f g h i j : Word}
    (ha : a = f) (hb : b = g) (hc : c = h) (hd : d = i) (he : e = j) :
    #v[a, b, c, d, e] = #v[f, g, h, i, j] := by
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  rfl

private theorem pointCongr {x y z x' y' z' : Limbs} (hx : x = x') (hy : y = y') (hz : z = z') :
    PointWords.mk x y z = PointWords.mk x' y' z' := by
  cases hx
  cases hy
  cases hz
  rfl

private theorem replayOutput (p : PointWords) (yy zz : Limbs) (sp : Word) :
    outputWords p yy zz sp = output p yy zz sp := by
  have h1548 : atWord v1548 = atWord w353 := by
    simp only [v1548, v1547, w353, w121, BitVec.ofNat_eq_ofNat, BitVec.zero_add, BitVec.add_comm]
  have h1553 : atWord v1553 = atWord w358 := by verify_word
  have h1556 : atWord v1556 = atWord w326 := by
    simp only [v1556, v1555, w326, w324, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have h1559 : atWord v1559 = atWord w338 := by
    simp only [v1559, v1558, w338, w337, w336, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_comm]
  have h1562 : atWord v1562 = atWord w362 := by
    simp only [v1562, w362, w337, w336, BitVec.ofNat_eq_ofNat, BitVec.mul_one, BitVec.add_comm]
  have h1566 : atWord v1566 = atWord w368 := by
    simp only [v1566, v1565, h1553, w368, w366, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have h1569 : atWord v1569 = atWord w610 := by
    simp only [v1569, v1568, w610, w121, BitVec.ofNat_eq_ofNat, BitVec.zero_add, BitVec.add_comm]
  have h1581 : atWord v1581 = atWord w27 := by
    change (-7 + 0xffffffffffff : Word) = 0xfffffffffff8
    decide +kernel
  have h1614 : atWord v1614 = atWord w670 := by verify_word
  have h1770 : atWord v1770 = atWord w838 := by
    simpa only [v1770, h1614, w666] using xMask p yy zz sp
  have h1791 : atWord v1791 = atWord w1267 := maskScaleEight (atWord w1167)
  have h1795 : atWord v1795 = atWord w1276 := maskScaleEight (atWord w1206)
  have h1799 : atWord v1799 = atWord w1281 := maskScaleEight (atWord w1244)
  have h1803 : atWord v1803 = atWord w1286 := maskScaleEight (atWord w1257)
  apply pointCongr <;> apply limbsCongr <;> verify_word

theorem outputWords_eq {w : PointWords} {p : Projective} (repr : Projective.WordsRepr w p)
    (sp : Word) :
    outputWords w (squareWords w.y) (squareWords w.z) sp = DoubleWords.double w :=
  (replayOutput w (squareWords w.y) (squareWords w.z) sp).trans (output_eq w sp repr.x repr.y repr.z)

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
