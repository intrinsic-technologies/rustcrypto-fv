import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.WordSteps.Views
import Lean

namespace K256.Proofs.Sec1.Affine.Uncompressed

open Lean Meta Elab Tactic

private def reduceWordReads (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun t => do
    let (proj, args) := (t.getAppFn, t.getAppArgs)
    unless args.size == 2 && (proj.isConstOf ``ArithmeticState.regs ||
        proj.isConstOf ``ArithmeticState.slots) do return .continue
    unless args[1]!.rawNatLit?.isSome || args[1]!.isAppOf ``OfNat.ofNat do return .continue
    let field := if proj.isConstOf ``ArithmeticState.regs then 0 else 1
    let some f ← project? args[0]! field | return .continue
    let r := (mkApp f args[1]!).headBeta
    if let .reduced v ← reduceMatcher? r then return .visit v
    return .visit r)

private partial def nameWordValues (goal : MVarId) (e : Expr) : MetaM (MVarId × Expr) := goal.withContext do
  match e.consumeMData with
  | .letE n ty val body _ =>
    let val ← reduceWordReads val
    if let some localDecl := (← getLCtx).findFromUserName? n then
      if let some old := localDecl.value? then
        if ← isDefEq old val then
          return ← nameWordValues goal (body.instantiate1 localDecl.toExpr)
    let (v, goal) ← (← goal.define n ty val).intro1P
    nameWordValues goal (body.instantiate1 (mkFVar v))
  | e => return (goal, ← reduceWordReads e)

elab "word_checkpoint " result:ident proof:ident " := " t:term : tactic => withMainContext do
  let lhs ← instantiateMVars (← elabTerm t none)
  let some body ← unfoldDefinition? lhs (ignoreTransparency := true)
    | throwError "expected a word transition"
  let (goal, rhs) ← nameWordValues (← getMainGoal) body
  let (v, goal) ← goal.withContext do
    (← goal.define result.getId (← inferType lhs) rhs).intro1P
  let (_, goal) ← goal.withContext do
    goal.note proof.getId (← mkEqRefl lhs) (some (← mkEq lhs (mkFVar v)))
  replaceMainGoal [goal]

end K256.Proofs.Sec1.Affine.Uncompressed
