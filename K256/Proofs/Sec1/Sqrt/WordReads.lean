import K256.Proofs.Sec1.Tactic.Core

namespace K256.Proofs.Sec1.Sqrt.WordReads

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Lean Meta Elab.Tactic

structure Input where
  store : Expr
  addr : Expr
  value : Expr
  proof : Expr

structure Env where
  shared : Refine.Tactic.Shared
  inputs : Array Input
  bases : Array Expr

def canonical (env : Env) (addr : Expr) : MetaM Expr := do
  let base := (← Refine.Tactic.addrOf addr).base
  for b in env.bases do
    if ← isDefEq base b then return addr.replace fun e => if e == base then some b else none
  return addr

def read (env : Env) (e : Expr) : MetaM Simp.Result := do
  let args := e.getAppArgs
  let (b, w) := (args[3]!, args[4]!)
  unless w.nat? == some 64 do throwError "expected a 64-bit load"
  let load (m : Expr) := mkAppN (mkConst ``memLoad) #[args[0]!, args[1]!, m, b, w]
  let ty := mkApp (mkConst ``BitVec) w
  let bc ← canonical env b
  let trans (p? : Option Expr) (lhs rhs : Expr) (q : Expr) : Expr := match p? with
    | none => q
    | some p => mkApp6 (mkConst ``Eq.trans [.one]) ty e lhs rhs p q
  let eight := mkNatLit 8
  let h0 := mkApp2 (mkConst ``Eq.refl [.one]) (mkConst ``Nat) (mkNatLit 0)
  let bound := CFG.Eval.leProof 64 128
  let mut cur := args[2]!
  let mut proof? : Option Expr := none
  repeat
    unless cur.isAppOfArity ``memStore 6 do break
    let (m, a, n, v) := (cur.getArg! 2, cur.getArg! 3, cur.getArg! 4, cur.getArg! 5)
    unless n.nat? == some 64 do throwError "unexpected store width {n}"
    let ac ← canonical env a
    if let some hab ← Refine.Tactic.sameAddr? ac bc then
      let q := mkAppN (mkConst ``memLoad_memStore_eq) #[m, a, b, n, v, hab, h0, bound]
      return { expr := v, proof? := trans proof? (load cur) v q }
    let prop := mkApp4 (mkConst ``RangeApart) ac eight bc eight
    let some hap ← Refine.Tactic.dischargeProp env.shared prop | throwError "memory alias at {a}, {b}"
    let q := mkAppN (mkConst ``memLoad_memStore_of_rangeApart) #[m, a, b, n, v, w, hap]
    proof? := some (trans proof? (load cur) (load m) q)
    cur := m
  for i in env.inputs do
    unless ← isDefEq cur i.store do continue
    if let some h ← Refine.Tactic.sameAddr? bc (← canonical env i.addr) then
      let atAddr (x : Expr) := mkAppN (mkConst ``memLoad) #[args[0]!, args[1]!, cur, x, w]
      let f ← withLocalDeclD `addr ty fun x => mkLambdaFVars #[x] (atAddr x)
      let q ← Meta.mkCongrArg f h
      let p := trans proof? (load cur) (atAddr i.addr) q
      return { expr := i.value, proof? := trans (some p) (atAddr i.addr) i.value i.proof }
  throwError "unknown input read {b}"

partial def normalize (env : Env) (e : Expr) :
    StateRefT (Std.HashMap Expr Simp.Result) MetaM Simp.Result := do
  unless e.hasFVar do return {expr := e}
  if let some r := (← get)[e]? then return r
  let r ← do
    if e.isAppOfArity ``memLoad 5 then
      let r ← read env e
      r.mkEqTrans (← normalize env r.expr)
    else if let .app f a := e then
      let rf ← normalize env f
      let ra ← normalize env a
      Simp.mkCongr rf ra
    else pure {expr := e}
  modify (·.insert e r)
  return r

def inputOf (d : LocalDecl) : MetaM Input := do
  let some (_, lhs, value) := d.type.eq? | throwError "expected a word equality at {d.userName}"
  unless lhs.isAppOfArity ``memLoad 5 && (lhs.getArg! 4).nat? == some 64 do
    throwError "expected a 64-bit load at {d.userName}"
  return ⟨lhs.getArg! 2, lhs.getArg! 3, value, d.toExpr⟩

def wordGoals (g : MVarId) : MetaM (List MVarId) := do
  let target ← instantiateMVars (← g.getType)
  if target.isAppOfArity ``Eq 3 then return [g]
  unless target.isAppOfArity ``WordsAt 5 do throwError "expected WordsAt or a word equality"
  let args := target.getAppArgs
  let some n ← (evalNat args[3]!).run | throwError "expected a literal word count"
  let mut proof := mkAppN (mkConst ``WordsAt.from_end) args
  let mut gs := []
  for k in (List.range n).reverse do
    let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit k, args[3]!])
    let f := mkAppN (mkConst ``WordsAt.from_succ) (args ++ #[mkNatLit k, hk])
    let word ← mkFreshExprSyntheticOpaqueMVar (← inferType f).bindingDomain!
    gs := word.mvarId! :: gs
    proof := mkApp2 f word proof
  g.assign (mkAppN (mkConst ``WordsAt.of_from) (args.push proof))
  return gs

def registerVector? (xs : Expr) : MetaM (Option (Array Expr)) := do
  let mut v := xs
  for _ in [:5] do
    if let some elems ← CFG.Eval.vectorElements? v then return some elems
    if v.isAppOf ``Vector.cast then
      v := v.appArg!
    else if v.isAppOf ``CFG.Location.arguments && v.appArg!.isAppOf ``CFG.Location.mk then
      v := v.appArg!.getArg! 5
    else
      let some e ← withDefault (unfoldDefinition? v) | return none
      v := e
  return none

def exposeLimb (e : Expr) : MetaM Simp.Result := do
  if e.isAppOfArity ``memLoad 5 then
    let args := e.getAppArgs
    let m := args[2]!
    if m.isAppOf ``CFG.Location.store && m.appArg!.isAppOf ``CFG.Location.mk then
      return {expr := mkAppN e.getAppFn (args.set! 2 m.appArg!.appArg!)}
  if e.isAppOfArity ``Value.get 2 && e.appArg!.isAppOfArity ``GetElem.getElem 8 then
    let read := e.appArg!.getAppArgs
    let some i ← CFG.Eval.indexValue? read[6]! | return {expr := e}
    let some elems ← registerVector? read[5]! | return {expr := e}
    let some value := elems[i]? | return {expr := e}
    if value.isAppOfArity ``Value.mk 2 && (← isDefEq (value.getArg! 0) (e.getArg! 0)) then
      return {expr := value.appArg!, proof? := mkApp2 (mkConst ``BitVec.setWidth_eq) (e.getArg! 0) value.appArg!}
  return {expr := e}

elab "lifted_word_reads" "[" names:ident,* "]" : tactic => withMainContext do
  let shared ← Refine.Tactic.Shared.new #[]
  let inputs ← names.getElems.mapM fun n => do inputOf (← getLocalDeclFromUserName n.getId)
  let regions ← Refine.Tactic.regions
  let env := {shared, inputs, bases := regions.map (·.addr.base) : Env}
  let mut cache := {}
  let mut left := #[]
  for g in ← wordGoals (← getMainGoal) do
    let some g ← Refine.Tactic.simpShallow shared.words g | continue
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq? | throwError "expected a word equality"
    let head ← exposeLimb lhs
    let (r, cache') ← (normalize env head.expr).run cache
    let r ← head.mkEqTrans r
    cache := cache'
    let pureGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq r.expr rhs)
    g.assign (← mkEqTrans (← r.getProof) pureGoal)
    left := left.push pureGoal.mvarId!
  replaceMainGoal left.toList

elab "lifted_registers" "[" names:ident,* "]" : tactic => withMainContext do
  let mut g ← getMainGoal
  for name in names.getElems do
    g ← g.withContext do
      let h ← getLocalDeclFromUserName name.getId
      let some (_, lhs, rhs) := h.type.eq? | throwError "expected a register equality"
      unless lhs.isAppOfArity ``Value.get 2 do throwError "expected Value.get"
      let read := lhs.getArg! 1
      unless read.isAppOfArity ``GetElem.getElem 8 do throwError "expected a register array read"
      let xs := read.getArg! 5
      let some j ← CFG.Eval.indexValue? (read.getArg! 6) | throwError "expected a literal index"
      let some n ← CFG.Eval.vectorSize? xs | throwError "expected a register array"
      let reg ← CFG.Eval.elementAt xs j n
      let val := mkApp2 (mkConst ``Value.get) (lhs.getArg! 0) reg
      g.replaceLocalDeclDefEq h.fvarId (← mkEq val rhs)
  replaceMainGoal [g]

end K256.Proofs.Sec1.Sqrt.WordReads
