import K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule.Value

namespace K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule

open X86Proofs K256.Proofs.Common.Field

theorem bit_of_byte (c : Bool) :
    (((if c then 1 else 0 : BitVec 8).setWidth 32).setWidth 64) = bit c := by
  cases c <;> decide

theorem bit_of_merge (c : Bool) : mergeGPR 8 (if c then 1 else 0) 0 = bit c := by
  cases c <;> decide

theorem addByteCarry (c : Bool) :
    (addSpec (if c then 1 else 0 : BitVec 8) 255).2.CF = c := by cases c <;> decide

theorem addCF_comm (x y : Word) : (addSpec x y).2.CF = (addSpec y x).2.CF := by
  change decide ((x+y).toNat ≠ _) = decide ((y+x).toNat ≠ _)
  rw [BitVec.add_comm x y, Nat.add_comm x.toNat y.toNat]

theorem adcCF_comm (c : Bool) (x y : Word) : (adcSpec c x y).2.CF = (adcSpec c y x).2.CF := by
  change decide ((x+y+_).toNat ≠ _) = decide ((y+x+_).toNat ≠ _)
  rw [BitVec.add_comm x y, Nat.add_comm x.toNat y.toNat]

theorem mulHi_comm (x y : Word) : (mulResult x y).2 = (mulResult y x).2 := by
  simp only [mulResult, Nat.mul_comm x.toNat y.toNat]

theorem compareCarry (c : Bool) (x y hi : Word) :
    (cmpSpec (hi + (mulResult x y).2 + bit c) hi).CF =
      (adcSpec c hi (mulResult x y).2).2.CF := by
  have hm := SquareValue.pair_mul x y
  have hxy := Nat.mul_le_mul (Nat.le_pred_of_lt x.isLt) (Nat.le_pred_of_lt y.isLt)
  change x.toNat * y.toNat ≤ 18446744073709551615 * 18446744073709551615 at hxy
  have hb : (bit c).toNat = c.toNat ∧ c.toNat ≤ 1 := by cases c <;> decide
  have hh := hi.isLt
  change decide ((hi + (mulResult x y).2 + bit c).toNat < hi.toNat) =
    decide ((hi + (mulResult x y).2 + bit c).toNat ≠ hi.toNat + (mulResult x y).2.toNat + c.toNat)
  rw [decide_eq_decide]
  simp only [pairNat, BitVec.toNat_add, hb.1, Nat.mod_add_mod, Nat.reducePow, Nat.reduceMul] at *
  omega

open K256.Proofs.Common.Field.Multiply

open Lean Meta in
private partial def proveWordEq (l r : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) (Option Expr)) MetaM (Option Expr) := do
  if let some h := (← get)[(l,r)]? then return h
  if l == r then return some (← mkEqRefl l)
  let h ← (do
    let la := l.getAppArgs
    let ra := r.getAppArgs
    if l.getAppFn != r.getAppFn || la.size != ra.size then return none
    if l.isAppOf ``GetElem.getElem || !l.hasFVar || !r.hasFVar || !l.isApp then
      if ← withReducible (isDefEq l r) then return some (← mkEqRefl l)
      return none
    let mut proof : Simp.Result := {expr := l.getAppFn}
    let mut ok := true
    for i in [:la.size] do
      if la[i]! == ra[i]! then
        proof ← Simp.mkCongrFun proof la[i]!
      else if !la[i]!.hasFVar && !ra[i]!.hasFVar then
        unless ← withDefault (isDefEq la[i]! ra[i]!) do
          ok := false
          break
        proof ← Simp.mkCongrFun proof la[i]!
      else
        let some p ← proveWordEq la[i]! ra[i]! | ok := false; break
        proof ← Simp.mkCongr proof {expr := ra[i]!, proof? := some p}
    if ok then return some (← proof.getProof)
    let swap? : Option (Name × Array Expr) ← do
      if l.isAppOfArity ``HAdd.hAdd 6 then
        pure (some (``BitVec.add_comm, la.extract 4 6))
      else if l.isAppOfArity ``HMul.hMul 6 then
        pure (some (``BitVec.mul_comm, la.extract 4 6))
      else if l.isAppOfArity ``Prod.snd 3 && l.appArg!.isAppOfArity ``mulResult 3 then
        pure (some (``mulHi_comm, l.appArg!.getAppArgs.extract 1 3))
      else if l.isAppOf ``StatusFlags.CF && l.appArg!.isAppOf ``Prod.snd then
        let p := l.appArg!.appArg!
        if p.isAppOf ``adcSpec then pure (some (``adcCF_comm, p.getAppArgs.extract 1 4))
        else if p.isAppOf ``addSpec then pure (some (``addCF_comm, p.getAppArgs.extract 1 3))
        else pure none
      else pure none
    let some (lemmaName, args) := swap? | return none
    if args[args.size-1]! == args[args.size-2]! then return none
    let ab ← mkAppM lemmaName args
    let some (_, _, swapped) := (← inferType ab).eq? | return none
    modify (·.insert (l,r) none)
    let some rest ← proveWordEq swapped r | return none
    return some (← mkEqTrans ab rest))
  modify (·.insert (l,r) h)
  return h

macro "match_product_words" : tactic => `(tactic| (
  have bitByte (c : Bool) :
      (if c then 1 else 0 : BitVec 8).setWidth 64 = bit c := by cases c <;> decide

  have compareByte (c : Bool) (x y hi : Word) :
      (if ((mulResult x y).2 + hi + BitVec.ofNat 64 c.toNat).toNat < hi.toNat then 1 else 0 : BitVec 8) =
        (if (adcSpec c hi (mulResult x y).2).2.CF then 1 else 0) := by
    have h := congrArg (fun f : Bool => if f then (1 : BitVec 8) else 0) (compareCarry c x y hi)
    change (if ((mulResult x y).2 + hi + bit c).toNat < hi.toNat then (1 : BitVec 8) else 0) = _
    simpa only [cmpSpec, subSpec, decide_eq_true_eq, BitVec.add_comm (mulResult x y).2 hi] using h

  have compareByte' (c : Bool) (x y hi : Word) :
      (if (hi + (mulResult x y).2 + BitVec.ofNat 64 c.toNat).toNat < hi.toNat then 1 else 0 : BitVec 8) =
        (if (adcSpec c hi (mulResult x y).2).2.CF then 1 else 0) := by
    rw [BitVec.add_comm hi (mulResult x y).2, compareByte]
  simp (config := {maxSteps := 1000000, failIfUnchanged := false}) only
    [machineProduct,first,three,four,last,addWide,wideMul,
     Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
     setWidth_mergeGPR8, bitByte, bit_of_byte, bit_of_merge, addByteCarry, compareByte, compareByte',
     BitVec.add_zero, BitVec.zero_add]
  all_goals simp (config := {failIfUnchanged := false}) only
    [bit, Fin.getElem_fin, K256.Proofs.Sec1.Affine.Uncompressed.arithmeticIndex]
  all_goals run_tac Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.Meta.whnfR (← Lean.instantiateMVars (← g.getType))
    let some (_, l, r) := target.eq? | throwError "expected a word equality"
    let some h ← (proveWordEq l r).run' {} | throwError "product expressions differ"
    g.assign h
    Lean.Elab.Tactic.replaceMainGoal []
  ))

end K256.Proofs.Generate.Generator.Multiply.Split.ProductSchedule
