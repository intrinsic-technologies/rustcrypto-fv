import K256.Proofs.Common.CFG.Eval
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.StackSlots

namespace K256.Proofs.Sec1.Affine.Uncompressed

open Lean Meta Elab Tactic
open X86Proofs K256.Proofs.Lift K256.Proofs.CFG.Eval

private structure SlotAddress where
  index : Option Nat
  zeroEq : Option Expr := none

private def slotAddress? (sp addr : Expr) : MetaM (Option SlotAddress) := do
  let addr := addr.consumeMData
  if sp == addr then return some ⟨some 0, none⟩
  let args := addr.getAppArgs
  unless args.size == 6 && args[4]! == sp do return none
  let some ⟨64, offset⟩ ← getBitVecValue? args[5]! | return none
  if addr.isAppOf ``HSub.hSub && offset.toNat == 8 then
    return some ⟨none, none⟩
  unless addr.isAppOf ``HAdd.hAdd && offset.toNat % 8 == 0 && offset.toNat < 200 do
    return none
  let eq ← if offset.toNat == 0 then
    some <$> mkEqSymm (← mkAppM ``BitVec.add_zero #[sp])
  else pure none
  return some ⟨some (offset.toNat / 8), eq⟩

private def atAddress (addr : SlotAddress) (proof : Expr)
    (motive : Expr → MetaM Expr) : MetaM Expr := do
  let some eq := addr.zeroEq | return proof
  withLocalDeclD `addr (mkApp (mkConst ``BitVec) (mkNatLit 64)) fun a => do
    mkEqNDRec (← mkLambdaFVars #[a] (← motive a)) proof eq

private def stackHyp? : MetaM (Option (Expr × Array Expr)) := do
  let some decl := (← getLCtx).findFromUserName? `stack | return none
  let ty ← instantiateMVars decl.type
  unless ty.isAppOfArity ``SlotState 5 do return none
  return some (decl.toExpr, ty.getAppArgs)

private structure StackProof where
  proof : Expr
  args : Array Expr
  writes : Array (Nat × Expr) := #[]

private partial def stackProof? (stack : Expr) (base : Array Expr) (ram : Expr) :
    MetaM (Option StackProof) := do
  let ram := ram.consumeMData
  if ram == base[2]! then return some ⟨stack, base, #[]⟩
  let_expr memStore σ inst previous addr bits word := ram | return none
  unless (← (evalNat bits).run) == some 64 do return none
  let some address ← slotAddress? base[3]! addr | return none
  let some parent ← stackProof? stack base previous | return none
  let (proof, writes) ← match address.index with
  | none =>
    pure (mkAppN (mkConst ``SlotState.push) (parent.args ++ #[parent.proof, word]), parent.writes)
  | some i => do
    let p := mkAppN (mkConst ``SlotState.write)
      (parent.args ++ #[parent.proof, mkNatLit i, ltProof i 25, word])
    let ty ← inferType p
    let args := ty.getAppArgs
    let proof ← atAddress address p fun a =>
      pure <| mkAppN (mkConst ``SlotState)
        (args.set! 2 (mkAppN (mkConst ``memStore) #[σ, inst, previous, a, bits, word]))
    pure (proof, parent.writes.push (i, word))
  return some ⟨proof, (← inferType proof).getAppArgs, writes⟩

simproc_decl slotRead (memLoad _ _ _) := fun e => do
  let_expr memLoad σ inst ram addr bits := e | return .continue
  unless (← (evalNat bits).run) == some 64 do return .continue
  let some (stack, base) ← stackHyp? | return .continue
  let some address ← slotAddress? base[3]! addr | return .continue
  let some i := address.index | return .continue
  let some state ← stackProof? stack base ram | return .continue
  let rhs := (state.writes.findRev? (·.1 == i)).map Prod.snd
    |>.getD ((mkApp base[4]! (mkNatLit i)).headBeta)
  if rhs == e then return .continue
  let p := mkAppN (mkConst ``SlotState.load)
    (state.args ++ #[state.proof, mkNatLit i, ltProof i 25])
  let p ← atAddress address p fun a =>
    mkEq (mkAppN (mkConst ``memLoad) #[σ, inst, ram, a, bits])
      (mkApp state.args[4]! (mkNatLit i))
  return .visit { expr := rhs, proof? := some p }

private def slotGuardProof (target : Expr) : MetaM Expr := do
  let some (stack, base) ← stackHyp? | throwError "expected a SlotState hypothesis named stack"
  let args := target.getAppArgs
  if target.isAppOfArity ``LoadOk 3 then
    let some address ← slotAddress? base[3]! args[1]! | throwError "expected a stack load address"
    let some i := address.index | throwError "expected a numbered stack slot"
    let some state ← stackProof? stack base args[0]! | throwError "expected a stack memory"
    let p := mkAppN (mkConst ``SlotState.loadOk)
      (state.args ++ #[state.proof, mkNatLit i, ltProof i 25])
    atAddress address p fun a => pure <| mkAppN (mkConst ``LoadOk) (args.set! 1 a)
  else if target.isAppOfArity ``StoreOk 6 then
    let some address ← slotAddress? base[3]! args[2]! | throwError "expected a stack store address"
    let some state ← stackProof? stack base args[1]! | throwError "expected a stack memory"
    let cover := (← getLocalDeclFromUserName `cover).toExpr
    let (thm, slotArgs) := match address.index with
      | none => (``SlotState.pushOk, #[])
      | some i => (``SlotState.storeOk, #[mkNatLit i, ltProof i 25])
    let p := mkAppN (mkConst thm)
      (state.args ++ #[state.proof] ++ slotArgs ++ #[cover, args[4]!, args[5]!])
    let proof := mkApp p (← mkDecideProof (← inferType p).bindingDomain!)
    atAddress address proof fun a => pure <| mkAppN (mkConst ``StoreOk) (args.set! 2 a)
  else
    throwError "expected a LoadOk or StoreOk goal"

elab "slot_guard" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let proof ← slotGuardProof target
  unless ← isDefEq target (← inferType proof) do
    throwError "stack guard does not match the goal"
  goal.assign proof
  replaceMainGoal []

elab "slot_state" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``SlotState 5 do throwError "expected a SlotState goal"
  let some (stack, base) ← stackHyp? | throwError "expected a SlotState hypothesis named stack"
  let some state ← stackProof? stack base target.getAppArgs[2]! | throwError "expected a stack memory"
  unless ← withAssignableSyntheticOpaque (isDefEq target (← inferType state.proof)) do
    throwError "stack state does not match the goal"
  goal.assign state.proof
  replaceMainGoal []

end K256.Proofs.Sec1.Affine.Uncompressed
