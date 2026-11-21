import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Copied.X86Proofs.Refine.Tactic
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open Lean Meta Elab Tactic

private def runtimeMemoryNames
    (initial : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM
    (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  let mut names := initial
  for d in ← getLCtx do
    if d.userName == `hbase || d.userName == `hstack ||
        (d.isLet && (← isDefEq d.type (mkConst ``X86.Machine.Ram))) then
      let n := mkIdent d.userName
      names := names.push (← `(Lean.Parser.Tactic.simpLemma| $n:ident))
  return names

private partial def runtimeRegionOn (lemma : Name) (h : Expr) (original target : Expr) : MetaM
  (Option Expr) := do
  if original == target || (← withReducible (isDefEq original target)) then return some h
  if target.isFVar then
    let d ← target.fvarId!.getDecl
    if let some value := d.value? then
      return ← runtimeRegionOn lemma h original value
  if target.isAppOfArity ``memStore 6 then
    let some hp ← runtimeRegionOn lemma h original (target.getArg! 2) | return none
    return some (← mkAppM lemma #[hp, target.getArg! 3, target.getArg! 5])
  return none

private def runtimeExactGuard (g : MVarId) : MetaM Bool := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``StoreOk 6 do return false
  let code := ty.getArg! 0
  let mem := ty.getArg! 1
  let a := ty.getArg! 2
  let n := ty.getArg! 3
  let p := ty.getArg! 4
  let k := ty.getArg! 5
  let some nv ← (Lean.Meta.evalNat n).run | return false
  let some pv ← Refine.Tactic.bvLit? p | return false
  let some kv ← (Lean.Meta.evalNat k).run | return false
  let fa ← Refine.Tactic.addrOf a
  let hhelperApart := (← getLocalDeclFromUserName `hhelperApart).toExpr
  let (pcStart, helperLen) ← forallTelescope (← instantiateMVars (← inferType
    hhelperApart)).consumeMData fun _ conclusion => do
    let conclusion := conclusion.consumeMData
    unless conclusion.isAppOfArity ``RangeApart 4 do
      throwError "runtime_guard: expected a concrete helper code range"
    let some pcStart ← Refine.Tactic.bvLit? (conclusion.getArg! 2) |
      throwError "runtime_guard: expected a literal helper entry"
    let some helperLen ← (Lean.Meta.evalNat (conclusion.getArg! 3)).run |
      throwError "runtime_guard: expected a literal helper size"
    return (pcStart, helperLen)
  unless pcStart ≤ pv && pv + kv ≤ pcStart + helperLen do return false
  let off := mkNatLit (pv - pcStart)
  let bound ← mkDecideProof (← mkAppM ``LE.le
    #[← mkAppM ``HAdd.hAdd #[off, k], mkNatLit helperLen])
  for d in ← getLCtx do
    let dt := (← instantiateMVars d.type).consumeMData
    unless dt.isAppOfArity ``Writable 4 do continue
    unless ← isDefEq (dt.getArg! 0) code do continue
    let fb ← Refine.Tactic.addrOf (dt.getArg! 2)
    unless fb.base == fa.base || (← withReducible (isDefEq fb.base fa.base)) do continue
    let some len ← (Lean.Meta.evalNat (dt.getArg! 3)).run | continue
    let distance := Refine.Tactic.dist fa.val fb.val
    unless distance + nv ≤ len do continue
    let some h ← runtimeRegionOn ``Writable.memStore d.toExpr (dt.getArg! 1) mem | continue
    let subTy ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd
      #[← mkAppM ``BitVec.toNat #[← mkAppM ``HSub.hSub #[fa.off, fb.off]], n], dt.getArg! 3]
    let hs ← mkAppM ``Writable.of_offsets #[h, fa.eq, fb.eq, ← mkDecideProof subTy]
    let hap ← mkAppM' hhelperApart #[hs]
    let hap ← mkAppOptM ``RangeApart.right_sub
      #[none, none, none, none, some hap, some off, some k, some bound]
    let result ← mkAppM ``storeOk_of_writable #[hs, hap]
    if ← isDefEq (← inferType result) ty then
      g.assign result
      return true
  return false

private def runtimeLoadGuard (g : MVarId) : MetaM Bool := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``LoadOk 3 do return false
  let mem := ty.getArg! 0
  let a := ty.getArg! 1
  let n := ty.getArg! 2
  let some nv ← (Lean.Meta.evalNat n).run | return false
  let fa ← Refine.Tactic.addrOf a
  for d in ← getLCtx do
    let dt := (← instantiateMVars d.type).consumeMData
    unless dt.isAppOfArity ``Readable 3 do continue
    let fb ← Refine.Tactic.addrOf (dt.getArg! 1)
    unless fb.base == fa.base || (← withReducible (isDefEq fb.base fa.base)) do continue
    let some len ← (Lean.Meta.evalNat (dt.getArg! 2)).run | continue
    unless Refine.Tactic.dist fa.val fb.val + nv ≤ len do continue
    let some h ← runtimeRegionOn ``Readable.memStore d.toExpr (dt.getArg! 0) mem |
      continue
    let subTy ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd
      #[← mkAppM ``BitVec.toNat #[← mkAppM ``HSub.hSub #[fa.off, fb.off]], n], dt.getArg! 2]
    let result ← mkAppM ``LoadOk.of_offsets #[h, fa.eq, fb.eq, ← mkDecideProof subTy]
    if ← isDefEq (← inferType result) ty then
      g.assign result
      return true
  return false

private def runtimeAccessGuard (g : MVarId) : MetaM Bool := do
  if ← runtimeExactGuard g then return true
  runtimeLoadGuard g

elab "runtime_guard" : tactic => do
  let S ← Refine.Tactic.Shared.new (← runtimeMemoryNames #[])
  let gs ← Refine.Tactic.runOn (← getMainGoal)
    (evalTactic (← `(tactic| repeat' refine And.intro ?_ ?_)))
  for g in gs do
    if ← runtimeAccessGuard g then continue
    if ← Refine.Tactic.closeGuard S g then continue
    let some g ← Refine.Tactic.normGoal S g | continue
    unless (← g.assumptionCore) || (← runtimeAccessGuard g) do throwError "runtime_guard: unresolved guard"
  replaceMainGoal []

elab "runtime_context" "[" ns:ident,* "]" : tactic => withMainContext do
  Refine.Tactic.registerNames .rewrite (ns.getElems.map fun n => n.getId)

private def runtimeFinishGoal (S : Refine.Tactic.Shared) (g : MVarId) : TacticM (List MVarId) :=
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if ty.isAppOfArity ``RamWriteFrame 3 then
      let some g ← Refine.Tactic.normGoal S g | return []
      let closed ← g.withContext do
        let ty := (← instantiateMVars (← g.getType)).consumeMData
        let mut base := ty.getArg! 1
        while base.isAppOfArity ``memStore 6 do base := base.getArg! 2
        unless ← withReducible (isDefEq (ty.getArg! 0) base) do return false
        let some proof ← Refine.Tactic.frameProof? S base (ty.getArg! 1) (ty.getArg! 2) |
          return false
        g.assign proof
        return true
      return if closed then [] else [g]
    else
      Refine.Tactic.closeAtom S g

syntax "runtime_finish" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
syntax "runtime_finish_all" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| runtime_finish [$ls,*]) => withMainContext do
    let S ← Refine.Tactic.Shared.new (← runtimeMemoryNames ls.getElems)
    replaceMainGoal (← runtimeFinishGoal S (← getMainGoal))
  | `(tactic| runtime_finish_all [$ls,*]) => withMainContext do
    let S ← Refine.Tactic.Shared.new (← runtimeMemoryNames ls.getElems)
    let mut remaining := []
    for g in ← getGoals do
      unless ← g.isAssigned do
        remaining := remaining ++ (← runtimeFinishGoal S g)
    setGoals remaining

elab "runtime_guards " stop:ident : tactic => withMainContext do
  let S ← Refine.Tactic.Shared.new (← runtimeMemoryNames #[])
  let mut g ← getMainGoal
  for _ in [:200] do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq? | throwError "runtime_guards: expected equation"
    let head ← whnf lhs
    let jumpBranch ← if head.isAppOfArity ``ite 5 then do
      let positive ← whnf (head.getArg! 3)
      let negative ← whnf (head.getArg! 4)
      pure (positive.isAppOf ``Transfer.jump && negative.isAppOf ``Transfer.jump)
    else pure false
    let finished := match stop.getId.toString with
      | "branch" => jumpBranch
      | "returned" => head.isAppOf ``Outcome.done || head.isAppOf ``Transfer.returned
      | "next" => head.isAppOf ``Outcome.next || head.isAppOf ``Outcome.done
      | "call" => head.isAppOf ``Transfer.call
      | "transfer" => head.isAppOf ``Transfer.call || head.isAppOf ``Transfer.jump ||
          head.isAppOf ``Transfer.returned
      | _ => false
    if finished then break
    let some conditional := lhs.find? (fun e => e.isAppOfArity ``ite 5) | break
    let saved ← saveState
    let condition := conditional.getArg! 1
    let access := (condition.find? fun e =>
      e.isAppOf ``StoreOk || e.isAppOf ``LoadOk).isSome
    let mut unresolved := false
    let hp ← mkFreshExprSyntheticOpaqueMVar condition
    let gs ← Refine.Tactic.runOn hp.mvarId!
      (evalTactic (← `(tactic| repeat' refine And.intro ?_ ?_)))
    for gg in gs do
      if ← runtimeAccessGuard gg then continue
      if ← Refine.Tactic.closeGuard S gg then continue
      let some gg ← Refine.Tactic.normGoal S gg | continue
      unless (← gg.assumptionCore) || (← runtimeAccessGuard gg) do
        if stop.getId == `branch && !access then
          unresolved := true
          break
        throwError "runtime_guards: unresolved guard {← gg.getType}"
    if unresolved then
      saved.restore
      break
    let ht ← mkAppOptM ``ite_eq_left #[some (conditional.getArg! 1), some (conditional.getArg! 2),
      some hp,
      some (conditional.getArg! 0), some (conditional.getArg! 3), some (conditional.getArg! 4)]
    let f ← withLocalDeclD `transfer (conditional.getArg! 0) fun x => do
      mkLambdaFVars #[x] (lhs.replace fun e => if e == conditional then some x else none)
    let heq ← mkAppM ``congrArg #[f, ht]
    let actualTy ← inferType heq
    let some (_, _, actualRhs) := actualTy.eq? | throwError "expected lifted equation"
    let reduced := actualRhs.headBeta
    let next ← mkFreshExprSyntheticOpaqueMVar (← mkEq reduced rhs)
    g.assign (← mkAppM ``Eq.trans #[heq, next])
    g := next.mvarId!
  replaceMainGoal [g]


set_option hygiene false in
elab "runtime_typed" : tactic => do
  evalTactic (← `(tactic| (
    intro r
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
        r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
      have := r.isLt
      omega
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | exact hTypes 0
      | exact hTypes 1
      | exact hTypes 2
      | exact hTypes 3
      | exact hTypes 4
      | exact hTypes 5
      | exact hTypes 6
      | exact hTypes 7
      | exact hTypes 8
      | exact hTypes 9
      | exact hTypes 10
      | exact hTypes 11
      | exact hTypes 12
      | exact hTypes 13
      | exact hTypes 14
      | exact hTypes 15
  )))

private partial def runtimeSuccessMap (project : Expr → MetaM Expr) (e : Expr) : MetaM Expr := do
  match e with
  | .letE n t v b nd => return .letE n t v (← runtimeSuccessMap project b) nd
  | .mdata _ b => runtimeSuccessMap project b
  | _ =>
    if e.isAppOfArity ``ite 5 then runtimeSuccessMap project (e.getArg! 3)
    else project e

def runtimeSuccessOutput (e : Expr) : MetaM Expr :=
  runtimeSuccessMap (fun terminal => do
    unless terminal.getAppFn.isConstOf ``X86Proofs.CFG.Transfer.returned do
      throwError "unexpected success node {terminal.getAppFn}"
    return terminal.getAppArgs.back!) e

def runtimeSuccessRam (e : Expr) : MetaM Expr :=
  runtimeSuccessMap (fun terminal => do
    unless terminal.getAppFn.isConstOf ``X86Proofs.CFG.Transfer.returned do
      throwError "unexpected success node {terminal.getAppFn}"
    let output := terminal.getAppArgs.back!
    unless output.getAppFn.isConstOf ``X86Proofs.CFG.Output.mk do
      throwError "unexpected output {output}"
    return output.getAppArgs.back!) e

def runtimeSuccessCallee (e : Expr) : MetaM Expr :=
  runtimeSuccessMap (fun terminal => do
    unless terminal.getAppFn.isConstOf ``X86Proofs.CFG.Transfer.call do
      throwError "unexpected success node {terminal.getAppFn}"
    let args := terminal.getAppArgs
    return args[args.size - 2]!) e

open Lean Meta Elab Command in
elab "runtime_callee_def " n:ident " from " th:ident : command => do
  liftTermElabM do
    let info ← getConstInfo th.getId
    forallTelescope info.type fun xs ty => do
      let some (_, _, rhs) := ty.eq? | throwError "not equality"
      let value ← mkLambdaFVars xs (← runtimeSuccessCallee rhs)
      let type ← inferType value
      addDecl (.defnDecl { name := n.getId, levelParams := [], type, value, hints := .abbrev, safety := .safe })
      enableRealizationsForConst n.getId

open Lean Meta Elab Command in
elab "runtime_ram_def " n:ident " from " th:ident : command => do
  liftTermElabM do
    let info ← getConstInfo th.getId
    forallTelescope info.type fun xs ty => do
      let some (_, _, rhs) := ty.eq? | throwError "not equality"
      let body ← runtimeSuccessRam rhs
      let value ← mkLambdaFVars xs body
      let type ← inferType value
      addDecl (.defnDecl { name := n.getId, levelParams := [], type, value, hints := .abbrev, safety := .safe })
      enableRealizationsForConst n.getId


open Lean Meta Elab Tactic in
partial def runtimeReturnedStore (g : MVarId) (hid : FVarId) : TacticM Unit := g.withContext do
  let hty ← hid.getType
  let some (_, lhs, _) := hty.eq? | throwError "expected returned equality"
  let rec peel (e : Expr) : Expr :=
    match e with
    | .letE _ _ v b _ => peel (b.instantiate1 v)
    | .mdata _ b => peel b
    | _ => e
  let e := peel lhs
  if e.isAppOfArity ``ite 5 then
    let a := e.getAppArgs
    let (pos, neg) ← g.byCasesDec a[1]! a[2]! `runtimeGuard
    for (branch, lemma) in [(pos, ``if_pos), (neg, ``if_neg)] do
      let (id, next) ← branch.mvarId.withContext do
        let eqif := mkAppN (mkConst lemma [Level.one])
          #[a[1]!, a[2]!, mkFVar branch.fvarId, a[0]!, a[3]!, a[4]!]
        let q ← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[eqif], mkFVar hid]
        let next ← branch.mvarId.assert `runtimeNext (← inferType q) q
        let (id, next) ← next.intro1
        let next ← next.clear hid
        pure (id, next)
      runtimeReturnedStore next id
  else
    setGoals [g]
    let hname := mkIdent (← hid.getUserName)
    evalTactic (← `(tactic| cases $hname:ident <;> rfl))

open Lean Elab Tactic in
elab "runtime_returned_store " h:ident : tactic => do
  runtimeReturnedStore (← getMainGoal) (← getFVarId h)

syntax "runtime_local_memory_norm" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| runtime_local_memory_norm [$ls,*]) => withMainContext do
    let names ← runtimeMemoryNames ls.getElems
    let shared ← X86Proofs.Refine.Tactic.Shared.new names
    let mut current := some (← getMainGoal)
    for _ in [:64] do
      if let some g := current then
        let before ← g.withContext g.getType
        current ← X86Proofs.Refine.Tactic.normGoal shared g
        if let some next := current then
          let after ← next.withContext next.getType
          if before == after then break
    replaceMainGoal current.toList


macro "runtime_local_memory_norm" : tactic => `(tactic| runtime_local_memory_norm [])

open Lean Meta Elab Tactic in
partial def runtimeFrameProof (shared : X86Proofs.Refine.Tactic.Shared)
    (original memory regions : Expr) : TacticM Expr := do
  if original == memory then return ← mkAppM ``RamWriteFrame.refl #[original, regions]
  if memory.isFVar then
    let d ← memory.fvarId!.getDecl
    if let some value := d.value? then return ← runtimeFrameProof shared original value regions
  unless memory.isAppOfArity ``memStore 6 do throwError "expected concrete memory store"
  let prior ← runtimeFrameProof shared original (memory.getArg! 2) regions
  let address := memory.getArg! 3
  let width := memory.getArg! 4
  let inclusion ← mkAppM ``InRegions #[regions, address, ← mkAppM ``HDiv.hDiv #[width, mkNatLit 8]]
  let goal ← mkFreshExprSyntheticOpaqueMVar inclusion
  if let some remaining ← X86Proofs.Refine.Tactic.normGoal shared goal.mvarId! then
    let some proof ← X86Proofs.Refine.Tactic.proveArith shared (← remaining.getType)
      | throwError "store inclusion remains {← remaining.getType}"
    remaining.assign proof
  let inside ← instantiateMVars goal
  mkAppM ``RamWriteFrame.memStore #[prior, memory.getArg! 5, inside]

open Lean Meta Elab Tactic in
elab "runtime_local_frame" : tactic => withMainContext do
  let names ← runtimeMemoryNames #[]
  let shared ← X86Proofs.Refine.Tactic.Shared.new names
  let goal ← getMainGoal
  let type := (← goal.getType).consumeMData
  unless type.isAppOfArity ``RamWriteFrame 3 do throwError "expected memory frame {type.getAppFn}"
  goal.assign (← runtimeFrameProof shared (type.getArg! 0) (type.getArg! 1) (type.getArg! 2))
  replaceMainGoal []



open Lean Meta Elab Command in
elab "runtime_output_def " n:ident " from " th:ident : command => do
  liftTermElabM do
    let info ← getConstInfo th.getId
    forallTelescope info.type fun xs ty => do
      let some (_, _, rhs) := ty.eq? | throwError "not equality"
      let value ← mkLambdaFVars xs (← runtimeSuccessOutput rhs)
      let type ← inferType value
      addDecl (.defnDecl { name := n.getId, levelParams := [], type, value, hints := .abbrev, safety := .safe })
      enableRealizationsForConst n.getId

private theorem runtimeTransfer_ite {α β : Type} (k : α → β) (c : Prop) [Decidable c]
    (h : c) (t f : β) (out : α) (ht : t = k out) :
    (if c then t else f) = k out := by
  simpa only [ite_eq_left h] using ht

private theorem runtimeTransfer_branches {α β : Type} (k : α → β) (c : Prop) [Decidable c]
    (a b : α) : (if c then k a else k b) = k (if c then a else b) := by
  split <;> rfl

open Lean Meta Elab Tactic in
partial def runtimeAccessProof (ty : Expr) : TacticM (Option Expr) := do
  let ty := ty.consumeMData
  let idx ← if ty.isAppOfArity ``LoadOk 3 then pure 0
    else if ty.isAppOfArity ``StoreOk 6 then pure 1 else return none
  let args := ty.getAppArgs
  let mut mem := args[idx]!.consumeMData
  while mem.isFVar do
    let d ← mem.fvarId!.getDecl
    if let some v := d.value? then mem := v.consumeMData else break
  if mem.isAppOfArity ``memStore 6 then
    let priorTy := mkAppN ty.getAppFn (args.set! idx (mem.getArg! 2))
    let some prior ← runtimeAccessProof priorTy | return none
    if idx == 0 then
      return some (mkAppN (mkConst ``loadOk_memStore)
        #[mem.getArg! 2, args[1]!, args[2]!, prior, mem.getArg! 3,
          mem.getArg! 4, mem.getArg! 5])
    else
      return some (mkAppN (mkConst ``storeOk_memStore)
        #[args[0]!, mem.getArg! 2, args[2]!, args[4]!, args[3]!, args[5]!,
          prior, mem.getArg! 3, mem.getArg! 4, mem.getArg! 5])
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if d.type.getAppFn == ty.getAppFn then
        if ← isDefEq d.type ty then return some (mkFVar d.fvarId)
  return none
open Lean Meta Elab Tactic in
elab "runtime_access" : tactic => withMainContext do
  let g ← getMainGoal
  let some p ← runtimeAccessProof (← g.getType) | throwError "not access"
  g.assign p
  replaceMainGoal []
open Lean Meta Elab Tactic in
partial def runtimeTransferWitness (ctor : Name) (e : Expr) : TacticM (Expr × Expr) := do
  match e with
  | .mdata _ b => runtimeTransferWitness ctor b
  | .letE n t v b _ =>
    let fresh ← mkFreshUserName n
    withLetDecl fresh t v fun x => do
      let (out, proof) ← runtimeTransferWitness ctor (b.instantiate1 x)
      return (← mkLetFVars #[x] out, ← mkLetFVars #[x] proof)
  | _ =>
    if e.isAppOfArity ``ite 5 then
      let a := e.getAppArgs
      let k := mkAppN (mkConst ctor) (← inferType e).getAppArgs
      if a[3]!.getAppFn.isConstOf ctor && a[4]!.getAppFn.isConstOf ctor then
        let positive := a[3]!.getAppArgs.back!
        let negative := a[4]!.getAppArgs.back!
        let out ← mkAppM ``ite #[a[1]!, positive, negative]
        let proof ← mkAppM ``runtimeTransfer_branches #[k, a[1]!, positive, negative]
        return (out, proof)
      let guard ← mkFreshExprSyntheticOpaqueMVar a[1]!
      setGoals [guard.mvarId!]
      if let some p ← runtimeAccessProof a[1]! then
        guard.mvarId!.assign p
      else if ctor == ``Transfer.returned && a[1]!.isAppOfArity ``And 2 then
        let p := a[1]!.getArg! 0
        let q := a[1]!.getArg! 1
        let some load ← runtimeAccessProof p | throwError "final return load guard not proved"
        let ret ← getFVarId (mkIdent `hretFinal)
        guard.mvarId!.assign (mkAppN (mkConst ``And.intro) #[p, q, load, mkFVar ret])
      else if ctor == ``Transfer.jump && (← runtimeAccessGuard guard.mvarId!) then
        pure ()
      else
        let mut names : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
        for d in ← getLCtx do
          if d.userName == `hbase || d.userName == `hstackBase ||
              (d.isLet && (← isDefEq d.type (mkConst ``Ram))) then
            let n := mkIdent d.userName
            names := names.push (← `(Lean.Parser.Tactic.simpLemma| $n:ident))
        let shared ← X86Proofs.Refine.Tactic.Shared.new names
        let mut current := some guard.mvarId!
        for _ in [:16] do
          if let some g := current then
            let before ← g.getType
            current ← X86Proofs.Refine.Tactic.normGoal shared g
            if let some next := current then
              if let some p ← next.withContext (runtimeAccessProof (← next.getType)) then
                next.assign p
                current := none
              else if ctor == ``Transfer.jump && (← next.withContext (runtimeAccessGuard next)) then
                current := none
              else if before == (← next.getType) then break
        if let some g := current then
          let ty ← g.getType
          throwError "runtime guard remains {ty}"
      unless ← guard.mvarId!.isAssigned do throwError "guard unproved {a[1]!}"
      let (out, proof) ← runtimeTransferWitness ctor a[3]!
      return (out, ← mkAppM ``runtimeTransfer_ite
        #[k, a[1]!, ← instantiateMVars guard, a[3]!, a[4]!, out, proof])
    else if e.getAppFn.isConstOf ctor then
      let out := e.getAppArgs.back!
      let eq ← mkEqRefl e
      return (out, eq)
    else throwError "unexpected transfer {e.getAppFn}"
open Lean Meta Elab Tactic in
private def runtimeTransferExistsTactic (ctor : Name) (th : Ident) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let code ← getFVarId (mkIdent `code)
  let args ← getFVarId (mkIdent `args)
  let mem ← getFVarId (mkIdent `mem)
  let thName ← realizeGlobalConstNoOverloadWithInfo th
  let eval := mkAppN (mkConst thName) #[mkFVar code, mkFVar args, mkFVar mem]
  let some (_, _, rhs) := (← inferType eval).eq? | throwError "not eq"
  let (out, proof) ← runtimeTransferWitness ctor rhs
  let proof ← mkAppM ``Eq.trans #[eval, proof]
  let target ← whnf (← g.getType)
  if target.isAppOfArity ``Eq 3 then
    g.assign proof
    replaceMainGoal []
  else
    unless target.isAppOfArity ``Exists 2 do throwError "expected existential transfer"
    let body := target.getArg! 1
    let ty := (body.beta #[out]).consumeMData
    let value ← mkFreshExprSyntheticOpaqueMVar ty
    let mut rest := []
    if ty.isAppOfArity ``And 2 then
      let tail ← mkFreshExprSyntheticOpaqueMVar (ty.getArg! 1)
      value.mvarId!.assign (← mkAppM ``And.intro #[proof, tail])
      rest := [tail.mvarId!]
    else value.mvarId!.assign proof
    g.assign (← mkAppOptM ``Exists.intro #[some (target.getArg! 0), some body, some out, some value])
    replaceMainGoal rest


elab "runtime_return_exists " th:ident : tactic =>
  runtimeTransferExistsTactic ``Transfer.returned th

elab "runtime_jump_exists " th:ident : tactic =>
  runtimeTransferExistsTactic ``Transfer.jump th

end AesGcm.Proofs.Machine.Runtime
