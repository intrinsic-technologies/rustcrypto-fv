import K256.Proofs.Sec1.Sqrt.WordReads
import K256.Proofs.Common.Field.Multiply.Words

namespace K256.Proofs.Sec1.Sqrt.WordEquality

open Lean Meta Elab Tactic X86Proofs CFG Lift Refine Common.Field

partial def strip (defs : Array Name) (r : Expr) : MetaM Expr := do
  let r := r.headBeta
  if let .letE _ _ v b _ := r then return ← strip defs (b.instantiate1 v)
  if let some n := r.getAppFn.constName? then
    if defs.contains n || n == ``mulWords || n.getPrefix == (``Multiply.wideMul).getPrefix then
      if let some e ← withDefault (unfoldDefinition? r) then return ← strip defs e
  if r.isAppOfArity ``Prod.fst 3 || r.isAppOfArity ``Prod.snd 3 then
    let x ← strip defs r.appArg!
    if x.isAppOfArity ``Prod.mk 4 then return ← strip defs (x.getArg! (if r.isAppOf ``Prod.fst then 2 else 3))
  if r.isAppOfArity ``GetElem.getElem 8 then
    let args := r.getAppArgs
    let xs ← strip defs args[5]!
    if xs != args[5]! then
      if let some v ← CFG.Eval.getElem? (mkAppN r.getAppFn (args.set! 5 xs)) then return ← strip defs v
  return r

partial def compareWord (defs : Array Name) (l r : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  if let some h := (← get)[(l,r)]? then return h
  let rhs ← strip defs r
  if rhs.isAppOfArity ``HAdd.hAdd 6 then
    let a := rhs.getArg! 4
    let b := rhs.getArg! 5
    let a' ← strip defs a
    let b' ← strip defs b
    if !a'.hasFVar && (← Refine.Tactic.bvLit? a') == some 0 then
      let h ← compareWord defs l b
      return ← mkExpectedTypeHint (← mkEqTrans h (← mkEqSymm (← mkAppM ``BitVec.zero_add #[b]))) (← mkEq l r)
    if !b'.hasFVar && (← Refine.Tactic.bvLit? b') == some 0 then
      let h ← compareWord defs l a
      return ← mkExpectedTypeHint (← mkEqTrans h (← mkEqSymm (← mkAppM ``BitVec.add_zero #[a]))) (← mkEq l r)
  let h ← do
    if !l.hasFVar || !rhs.hasFVar || l.isFVar || rhs.isFVar || l.isAppOf ``GetElem.getElem then
      unless ← isDefEq l rhs do throwError "different operands {l} and {rhs}"
      mkEqRefl l
    else if l.getAppFn.constName? == rhs.getAppFn.constName? && l.getAppNumArgs == rhs.getAppNumArgs then
      let la := l.getAppArgs
      let ra := rhs.getAppArgs
      let mut rr : Simp.Result := { expr := l.getAppFn }
      for i in [:la.size] do
        let (x,y) := (la[i]!,ra[i]!)
        if x == y || !x.hasFVar then
          rr ← Simp.mkCongrFun rr x
        else
          let hh ← compareWord defs x y
          rr ← Simp.mkCongr rr {expr := y, proof? := some hh}
      rr.getProof
    else throwError "different word operations {l.getAppFn} and {rhs.getAppFn}"
  let h ← mkExpectedTypeHint h (← mkEq l r)
  modify (·.insert (l,r) h)
  return h

elab "lifted_word_eq" "[" names:ident,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← g.getType).eq? | throwError "expected a word equality"
  let defs ← names.getElems.mapM fun n => resolveGlobalConstNoOverload n
  let h ← (compareWord defs lhs rhs).run' {}
  g.assign h
  replaceMainGoal []

end K256.Proofs.Sec1.Sqrt.WordEquality
