import K256.Proofs.Generate.Generator.Multiply.AddExecution.Arithmetic.Product

namespace K256.Proofs.Generate.Generator.Multiply.AddGraph

open K256.Proofs.Common.Field K256.Proofs.Common.Point K256.Proofs.Common.Point.AddWords
open K256.Proofs.Sec1.Serialize.Normalize

open Lean in
private def isFormulaWord (n : Name) : Bool :=
  n.getPrefix == `K256.Proofs.Generate.Generator.Multiply.AddGraph &&
    n.getString!.startsWith "w" && ((n.getString!.drop 1).toString.toNat?).isSome

open Lean Meta Elab Tactic in
private def generalizeFormulaWords (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let p ← getFVarFromUserName `p
  let q ← getFVarFromUserName `q
  let mut args := #[]
  let mut vars := #[]
  let mut replacements : Std.HashMap Expr Expr := {}
  for t in target.getUsedConstants do
    unless isFormulaWord t do continue
    let arg := mkApp2 (mkConst t) p q
    let var := mkFVar (← mkFreshFVarId)
    args := args.push arg
    vars := vars.push var
    replacements := replacements.insert arg var
  let mut type := (target.replace (replacements[·]?)).abstract vars
  for _ in args do
    type := .forallE `v (mkApp (mkConst ``BitVec) (mkNatLit 64)) type .default
  let proof ← mkFreshExprSyntheticOpaqueMVar type
  goal.assign (mkAppN proof args)
  return (← proof.mvarId!.introN args.size).2

open Lean Elab Tactic in
local elab "formula_atoms" : tactic => do
  replaceMainGoal [← generalizeFormulaWords (← getMainGoal)]

open Lean Meta Elab Tactic in
local elab "expand_formula_words" : tactic => withMainContext do
  let some (_, lhs, rhs) := (← instantiateMVars (← getMainTarget)).eq?
    | throwError "expected a word identity"
  let mut seen := rhs.getUsedConstants.foldl (init := ({} : Std.HashSet Name)) (·.insert ·)
  let mut pending := lhs.getUsedConstants
  let mut rules := #[]
  while let some n := pending.back? do
    pending := pending.pop
    if seen.contains n || !isFormulaWord n then continue
    seen := seen.insert n
    let .defnInfo d ← getConstInfo n | throwError "expected a graph definition"
    pending := pending ++ d.value.getUsedConstants
    rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident))
  evalTactic (← `(tactic| try simp only [$rules,*]))

private theorem limbs_eq {a b : Limbs}
    (h0 : a[0] = b[0]) (h1 : a[1] = b[1]) (h2 : a[2] = b[2])
    (h3 : a[3] = b[3]) (h4 : a[4] = b[4]) : a = b := by
  apply Vector.ext
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  all_goals assumption

private theorem scale21 (a : BitVec 64) : a + (a + a * 4) * 4 = a * 21 := by grind only

private theorem scale9 (a : BitVec 64) : a + a * 8 = a * 9 := by grind only

private theorem scale3 (a : BitVec 64) : a + a * 2 = a * 3 := by grind only

private theorem scale7 (a : BitVec 64) : a * 8 - a = a * 7 := by grind only

private theorem addScale7 (a b : BitVec 64) : b + a * 8 - a = b + a * 7 := by grind only

private theorem get0 (a b c d e : BitVec 64) : #v[a, b, c, d, e][0] = a := rfl

private theorem get1 (a b c d e : BitVec 64) : #v[a, b, c, d, e][1] = b := rfl

private theorem get2 (a b c d e : BitVec 64) : #v[a, b, c, d, e][2] = c := rfl

private theorem get3 (a b c d e : BitVec 64) : #v[a, b, c, d, e][3] = d := rfl

private theorem get4 (a b c d e : BitVec 64) : #v[a, b, c, d, e][4] = e := rfl

private theorem addLeftComm (a b c : BitVec 64) : a + (b + c) = b + (a + c) := by grind only

private def bzz (p q : PointWords) : Limbs :=
  #v[w1545 p q, w1552 p q, w1559 p q, w1564 p q, w1543 p q]

private def yz7 (p q : PointWords) : Limbs :=
  #v[w1599 p q, w1609 p q, w1615 p q, w1621 p q, w1597 p q]

private def xx9 (p q : PointWords) : Limbs :=
  #v[w1660 p q, w1666 p q, w1671 p q, w1676 p q, w1656 p q]

local macro "match_formula" : tactic =>
  `(tactic| (
    apply limbs_eq <;>
      simp only [leftInput, rightInput, outputLimbs, «output», bzz, yz7, xx9, sum, negate,
        weak, scale, first, carry, top, modulusWords, mask48, mask52, Fin.getElem_fin,
        Vector.getElem_ofFn, get0, get1, get2, get3, get4] <;>
      expand_formula_words <;> formula_atoms <;>
      (try simp only [scale21, scale9, scale3, scale7, addScale7, BitVec.mul_one,
        Nat.reduceAdd, Nat.reduceMul, BitVec.reduceOfNat, BitVec.reduceMul]) <;>
      (try simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_comm,
        addLeftComm, BitVec.add_assoc]) <;> first | rfl | grind only))

set_option maxHeartbeats 2000000 in
theorem output_eq_of_products (p q : PointWords)
    (products : ∀ k, outputLimbs k p q = Raw.product k (leftInput k p q) (rightInput k p q)) :
    «output» p q = Raw.add p q := by
  have bzz_eq :
    bzz p q = weak (scale 21 (outputLimbs .zz p q)) := by
    match_formula
  have yz7_eq :
    yz7 p q = weak (scale 7 (leftInput .zLeft p q)) := by
    match_formula
  have xx9_eq :
    xx9 p q = weak (scale 9 (outputLimbs .xx p q)) := by
    match_formula
  have xy_pair :
    leftInput .xLeft p q =
      sum (outputLimbs .xy p q) (negate 2 (sum (outputLimbs .xx p q) (outputLimbs .yy p q))) := by
    match_formula
  have yz_pair :
    leftInput .zLeft p q =
      sum (outputLimbs .yz p q) (negate 2 (sum (outputLimbs .yy p q) (outputLimbs .zz p q))) := by
    match_formula
  have xz_pair :
    rightInput .xRight p q =
      sum (outputLimbs .xz p q) (negate 2 (sum (outputLimbs .xx p q) (outputLimbs .zz p q))) := by
    match_formula
  have yy_minus_bzz :
    rightInput .xLeft p q = sum (outputLimbs .yy p q) (negate 1 (bzz p q)) := by
    match_formula
  have yy_plus_bzz :
    leftInput .yLeft p q = sum (outputLimbs .yy p q) (bzz p q) := by
    match_formula
  have scaled_yz :
    leftInput .xRight p q = weak (scale 3 (yz7 p q)) := by
    match_formula
  have scaled_xx :
    leftInput .yRight p q = weak (scale 7 (xx9 p q)) := by
    match_formula
  have triple_xx :
    leftInput .zRight p q = scale 3 (outputLimbs .xx p q) := by
    match_formula
  have output_x :
    («output» p q).x = weak (sum (outputLimbs .xLeft p q) (negate 1 (outputLimbs .xRight p q))) := by
    match_formula
  have output_y :
    («output» p q).y = weak (sum (outputLimbs .yLeft p q) (outputLimbs .yRight p q)) := by
    match_formula
  have output_z :
    («output» p q).z = weak (sum (outputLimbs .zLeft p q) (outputLimbs .zRight p q)) := by
    match_formula
  have leftXX : leftInput .xx p q = p.x := by apply limbs_eq <;> rfl
  have rightXX : rightInput .xx p q = q.x := by apply limbs_eq <;> rfl
  have leftYY : leftInput .yy p q = p.y := by apply limbs_eq <;> rfl
  have rightYY : rightInput .yy p q = q.y := by apply limbs_eq <;> rfl
  have leftZZ : leftInput .zz p q = p.z := by apply limbs_eq <;> rfl
  have rightZZ : rightInput .zz p q = q.z := by apply limbs_eq <;> rfl
  have leftXY : leftInput .xy p q = sum p.x p.y := by match_formula
  have rightXY : rightInput .xy p q = sum q.x q.y := by match_formula
  have leftYZ : leftInput .yz p q = sum p.y p.z := by match_formula
  have rightYZ : rightInput .yz p q = sum q.y q.z := by match_formula
  have leftXZ : leftInput .xz p q = sum p.x p.z := by match_formula
  have rightXZ : rightInput .xz p q = sum q.x q.z := by match_formula
  have yMinus : rightInput .yLeft p q = rightInput .xLeft p q := rfl
  have yPair : rightInput .yRight p q = rightInput .xRight p q := rfl
  have zPlus : rightInput .zLeft p q = leftInput .yLeft p q := rfl
  have zPair : rightInput .zRight p q = leftInput .xLeft p q := rfl
  change PointWords.mk («output» p q).x («output» p q).y («output» p q).z = _
  simp only [output_x, output_y, output_z, products, leftXX, rightXX, leftYY, rightYY,
    leftZZ, rightZZ, leftXY, rightXY, leftYZ, rightYZ, leftXZ, rightXZ, xy_pair,
    yz_pair, xz_pair, yy_minus_bzz, yy_plus_bzz, scaled_yz, scaled_xx, triple_xx,
    bzz_eq, yz7_eq, xx9_eq, yMinus, yPair, zPlus, zPair, Raw.add, addWith, pairsWith]

theorem output_eq_add (p q : PointWords)
    (pBound : ∀ w ∈ [p.x, p.y, p.z], ∃ x, FieldRepr w x 1)
    (qBound : ∀ w ∈ [q.x, q.y, q.z], ∃ x, FieldRepr w x 1) :
    «output» p q = AddWords.add p q := by
  refine (output_eq_of_products p q ?_).trans (Raw.add_eq p q pBound qBound)
  intro k
  cases k with
  | xx => exact xx_product p q
  | yy => exact yy_product p q
  | zz => exact zz_product p q
  | xy => exact xy_product p q
  | yz => exact yz_product p q
  | xz => exact xz_product p q
  | xLeft => exact xLeft_product p q
  | xRight => exact xRight_product p q
  | yLeft => exact yLeft_product p q
  | yRight => exact yRight_product p q
  | zLeft => exact zLeft_product p q
  | zRight => exact zRight_product p q

end K256.Proofs.Generate.Generator.Multiply.AddGraph
