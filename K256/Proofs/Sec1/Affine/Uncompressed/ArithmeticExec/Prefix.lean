import K256.Proofs.Common.CFG.Eval

namespace K256.Proofs.Sec1.Affine.Uncompressed

open Lean Meta Simp Elab Tactic K256.Proofs.CFG K256.Proofs.CFG.Eval

private def evalPrefix (e : Expr) : SimpM (Option Simp.Result) := do
  let_expr Block.eval opTy label value ram signature results dialect _ entry scope memory ← e
    | return none
  let some entryName ← definitionHead? entry | return none
  let some body ← unfoldDefinition? entry (ignoreTransparency := true) | return none
  let some elems ← valueElements? scope | return none
  elems.forM markSimplified
  markSimplified memory
  let common := #[opTy, label, value, ram, signature, results, dialect]
  let mut facts : Facts := {
    Value := value, values := elems, regs := #[scope],
    sizes := #[elems.size], pre := #[mkApp3 (mkConst ``Values.Prefix.refl) value
      (mkNatLit elems.size) scope] }
  let mut block := body
  let mut store := memory
  let mut steps : Array Ran := #[]
  while block.isAppOfArity ``Block.letOp 9 do
    let k := steps.size
    let a := block.getAppArgs
    let (n, arity, op, indices, next) := (a[4]!, a[5]!, a[6]!, a[7]!, a[8]!)
    let some (f, args, selected) ← facts.select k indices arity | return none
    facts := f
    let call := mkAppN (mkConst ``Dialect.eval) #[opTy, value, ram, dialect, arity, op, args, store]
    let r ← simpOperation call (((← vectorElements? args).getD #[]).push store)
    let some out := opResult? r.expr | throwError "could not reduce operation {n} of {entryName}"
    steps := steps.push {
      n, arity, op, operands := indices, next, scope := facts.regs[k]!,
      store, args, hargs := selected, proof := ← r.getProof, result := out }
    match out with
    | .stuck => throwError "operation {n} of {entryName} is stuck"
    | .ok v m | .guarded _ _ v m =>
      markSimplified v
      markSimplified m
      let size := facts.sizes[k]!
      let regs := mkApp4 (mkConst ``Vector.push [0]) value (mkNatLit size) facts.regs[k]! v
      facts := { facts with
        values := facts.values.push v, regs := facts.regs.push regs,
        sizes := facts.sizes.push (size + 1), pre := facts.pre.push (mkAppN (mkConst ``Values.Prefix.push)
          #[value, mkNatLit elems.size, mkNatLit size, scope, facts.regs[k]!, facts.pre[k]!, v]) }
      block := next
      store := m
  if steps.isEmpty then return none
  let k := steps.size
  let mut t := mkAppN (mkConst ``Block.eval)
    (common ++ #[mkNatLit facts.sizes[k]!, block, facts.regs[k]!, store])
  let mut h ← mkEqRefl t
  let stuck := mkAppN (mkConst ``Transfer.stuck) #[value, ram, label, signature, results]
  let transfer ← inferType e
  for x in steps.reverse do
    let args := common ++ #[x.n, x.arity, x.op, x.operands, x.next, x.scope, x.store, x.args]
    match x.result with
    | .ok v m => h := mkAppN (mkConst ``Block.eval_letOp_some) (args ++ #[v, m, t, x.hargs, x.proof, h])
    | .guarded c inst v m =>
      h := mkAppN (mkConst ``Block.eval_letOp_ite) (args ++ #[c, inst, v, m, t, x.hargs, x.proof, h])
      t := mkApp5 (mkConst ``ite [1]) transfer c inst t stuck
    | .stuck => unreachable!
  return some { expr := t, proof? := some h }

syntax "arithmetic_prefix" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| arithmetic_prefix $[[$ls,*]]?) => withMainContext do
    let ls := ls.map (·.getElems) |>.getD #[]
    let stx ← `(tactic| simp only [cfg_eval, ↓reduceIte, ↓reduceDIte, reduceCtorEq, Nat.reduceDiv,
      Nat.reduceLeDiff, Nat.reduceEqDiff, BitVec.reduceEq, BitVec.reduceNe, BitVec.reduceToNat,
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, $ls,*])
    let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
    let ctx ← ctx.setConfig { ctx.config with maxSteps := 10000000, bitVecOfNat := false }
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let some (_, lhs, rhs) := target.eq? | throwError "expected a block evaluation equation"
    let (some r, _) ← SimpM.run ctx {} (Simp.mkDefaultMethodsCore simprocs) (evalPrefix lhs)
      | throwError "expected a named instruction prefix"
    let tail ← mkFreshExprMVar (← mkEq r.expr rhs)
    goal.assign (← mkEqTrans (← r.getProof) tail)
    replaceMainGoal [tail.mvarId!]


simproc_decl arithmeticRead ((_ : Vector _ _)[_]) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ xs i _ := e | return .continue
  let some j ← indexValue? (← withTransparency .all (whnf i)) | return .continue
  let rec read (v : Expr) (fuel : Nat) : MetaM (Option (Expr × Expr)) := do
    match fuel with
    | 0 => return none
    | fuel + 1 =>
      let_expr Vector.push α n old x := v | do
        let some size ← vectorSize? v | return none
        let x ← elementAt v j size
        return some (x, ← mkEqRefl x)
      let some size ← (evalNat n).run | return none
      if j = size then
        return some (x, mkAppN (mkConst ``Values.getElem_push_self) #[α, n, old, x])
      let some (y, h) ← read old fuel | return none
      return some (y, mkAppN (mkConst ``Values.getElem_push_of_lt)
        #[α, n, old, x, y, i, ltProof j size, h])
  unless xs.isAppOfArity ``Vector.push 4 do return .continue
  let some size ← vectorSize? xs | return .continue
  let some (y, h) ← read xs size | return .continue
  return .visit { expr := y, proof? := some h }

end K256.Proofs.Sec1.Affine.Uncompressed
