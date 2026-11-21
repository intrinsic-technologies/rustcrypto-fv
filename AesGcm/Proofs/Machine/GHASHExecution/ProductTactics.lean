import AesGcm.Proofs.Machine.GHASHExecution.ProductBits
import Lean.Meta.Tactic.AC

namespace AesGcm.Proofs.Machine.GHASHExecution

open AesGcm.Proofs.Machine.GHASH
open Lean Meta Elab Tactic

partial def flattenMaskedProduct (op : Name) (e : Expr) : Array Expr :=
  if e.getAppFn.isConstOf op && e.getAppNumArgs ≥ 2 then
    let a := e.getAppArgs
    flattenMaskedProduct op a[a.size - 2]! ++ flattenMaskedProduct op a[a.size - 1]!
  else #[e]

def maskedMul64Post (ctx : Simp.Context) (e : Expr) : SimpM Simp.Step := do
  if !e.getAppFn.isConstOf ``HOr.hOr || e.getAppNumArgs < 2 then return .continue
  let terms := flattenMaskedProduct ``HOr.hOr e
  if terms.size != 4 then return .continue
  if terms.any (fun t => !t.getAppFn.isConstOf ``HAnd.hAnd) then return .continue
  let term := terms[0]!.getAppArgs
  let parts := flattenMaskedProduct ``HXor.hXor term[term.size - 2]!
  if parts.size != 4 then return .continue
  let product := parts[0]!
  if !product.getAppFn.isConstOf ``HMul.hMul then return .continue
  let factors := product.getAppArgs
  let a := factors[factors.size - 2]!
  let b := factors[factors.size - 1]!
  if !a.getAppFn.isConstOf ``HAnd.hAnd || !b.getAppFn.isConstOf ``HAnd.hAnd then
    return .continue
  let aa := a.getAppArgs
  let bb := b.getAppArgs
  let target ← mkAppM ``maskedMul64 #[aa[aa.size - 2]!, bb[bb.size - 2]!]
  let goal ← mkFreshExprMVar (← mkEq e target)
  let expanded ← goal.mvarId!.withContext do
    let ty ← goal.mvarId!.getType
    let some (_, lhs, rhs) := ty.eq? | throwError "not equality"
    let some rhs ← unfoldDefinition? rhs true | throwError "not definition: {rhs}"
    let rhs ← zetaReduce rhs
    withTransparency .default <| goal.mvarId!.change (← mkEq lhs rhs)
  let (next, _) ← simpTarget expanded ctx
  if let some next := next then
    try AC.rewriteUnnormalizedRefl next
    catch err => throwError "product proof failed: {err.toMessageData}"
  let proof ← instantiateMVars goal
  return .done {expr := target, proof? := proof}

elab "ghash_fold_products" : tactic => withMainContext do
  let thms ← ({} : SimpTheorems).addConst ``BitVec.ofNat_eq_ofNat
  let ctx ← Simp.mkContext (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems) (config := Simp.neutralConfig)
  let goal ← getMainGoal
  let ty ← goal.getType
  let (r, _) ← Simp.main ty ctx (methods := {post := maskedMul64Post ctx})
  let next ← applySimpResultToTarget goal ty r
  replaceMainGoal [next]


end AesGcm.Proofs.Machine.GHASHExecution
