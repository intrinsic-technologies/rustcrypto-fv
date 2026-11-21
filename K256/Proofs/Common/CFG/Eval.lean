import K256.Proofs.Common.CFG.EvalAttr
import K256.Proofs.Common.CFG.Lemma.IR
namespace K256.Proofs.CFG

attribute [cfg_eval] Program.step Block.eval Terminator.eval Transfer.next Edge.eval Cont.eval StackFrame.resume StackFrame.Accepts Dialect.ofPure Dialect.pureOp Option.map Transfer.next_ite
open Lean Meta Simp Elab Tactic

namespace Eval

def isVectorLiteral (e : Expr) : Bool :=
  e.isAppOfArity ``Vector.mk 4 && e.appFn!.appArg!.isAppOfArity ``List.toArray 2

partial def listElements? (l : Expr) (acc : Array Expr := #[]) : Option (Array Expr) :=
  if l.isAppOfArity ``List.cons 3 then listElements? l.appArg! (acc.push l.appFn!.appArg!)
  else if l.isAppOfArity ``List.nil 1 then some acc
  else none

partial def hasLiteralSpine (v : Expr) : Bool :=
  isVectorLiteral v ||
    (v.isAppOfArity ``Vector.push 4 && hasLiteralSpine v.appFn!.appArg!) ||
    (v.isAppOf ``Values.select && hasLiteralSpine v.appArg!) ||
    (v.isAppOfArity ``HAppend.hAppend 6 && hasLiteralSpine v.appFn!.appArg! &&
      hasLiteralSpine v.appArg!) ||
    (v.isAppOfArity ``Vector.cast 5 && hasLiteralSpine v.appArg!)

partial def vectorElements? (v : Expr) : MetaM (Option (Array Expr)) := do
  if isVectorLiteral v then
    if let some elems := listElements? v.appFn!.appArg!.appArg! then
      return some (elems.map (·.headBeta))
  if v.isAppOfArity ``HAppend.hAppend 6 then
    if let some xs ← vectorElements? v.appFn!.appArg! then
      if let some ys ← vectorElements? v.appArg! then return some (xs ++ ys)
  unless hasLiteralSpine v do return none
  let l ← try mkAppM ``Vector.toList #[v] catch _ => return none
  go l #[]
where
  go (l : Expr) (acc : Array Expr) : MetaM (Option (Array Expr)) := do
    let l ← whnfD l
    match_expr l with
    | List.nil _ => return some acc
    | List.cons _ a t => go t (acc.push a.headBeta)
    | _ => return none

def mkVectorLiteral (α n : Expr) (elems : Array Expr) : MetaM Expr := do
  let u ← getDecLevel α
  let list ← mkListLit α elems.toList
  let array := mkApp2 (mkConst ``List.toArray [u]) α list
  let size := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) n
  return mkApp4 (mkConst ``Vector.mk [u]) α n array size

def vectorLiteral? (e : Expr) : MetaM (Option Expr) := do
  if isVectorLiteral e then return none
  let ty ← whnfR (← inferType e)
  let_expr Vector α n ← ty | return none
  let some elems ← vectorElements? e | return none
  return some (← mkVectorLiteral α n elems)

def indexValue? (i : Expr) : MetaM (Option Nat) := do
  let i ← instantiateMVars i
  match_expr i with
  | Fin.mk _ v _ => evalNat v |>.run
  | Fin.last n => evalNat n |>.run
  | Fin.ofNat n _ k =>
    let some n ← (evalNat n).run | return none
    let some k ← (evalNat k).run | return none
    return if n = 0 then none else some (k % n)
  | OfNat.ofNat ty k _ =>
    let some k ← (evalNat k).run | return none
    match_expr ← whnfR ty with
    | Fin m =>
      let some m ← (evalNat (← whnfD m)).run | return none
      return if m = 0 then none else some (k % m)
    | _ => return some k
  | _ => evalNat i |>.run

def getElem? (e : Expr) : MetaM (Option Expr) := do
  let_expr GetElem.getElem _ _ _ _ _ xs i _ ← e | return none
  let ty ← whnfR (← inferType xs)
  unless ty.isAppOfArity ``Vector 2 do return none
  let some k ← indexValue? i | return none
  let some elems ← vectorElements? xs | return none
  return elems[k]?

end Eval

dsimproc [cfg_eval] reduceSelect (Values.select _ _) := fun e => do
  let some e' ← Eval.vectorLiteral? e | return .continue
  return .visit e'

dsimproc [cfg_eval] reducePush (Vector.push _ _) := fun e => do
  let some e' ← Eval.vectorLiteral? e | return .continue
  return .visit e'

dsimproc [cfg_eval] reduceAppend ((_ : Vector _ _) ++ (_ : Vector _ _)) := fun e => do
  let some e' ← Eval.vectorLiteral? e | return .continue
  return .visit e'

dsimproc [cfg_eval] reduceCast (Vector.cast _ _) := fun e => do
  let some e' ← Eval.vectorLiteral? e | return .continue
  return .visit e'

dsimproc [cfg_eval] reduceToList (Vector.toList _) := fun e => do
  let_expr Vector.toList α _ xs ← e | return .continue
  let some elems ← Eval.vectorElements? xs | return .continue
  return .visit (← mkListLit α elems.toList)

dsimproc [cfg_eval] reduceGetElem ((_ : Vector _ _)[_]) := fun e => do
  let some e' ← Eval.getElem? e | return .continue
  return .visit e'

dsimproc [cfg_eval] reduceGetElemFin ((_ : Vector _ _)[(_ : Fin _)]) := fun e => do
  let some e' ← Eval.getElem? e | return .continue
  return .visit e'

namespace Eval

def whnfEval (e : Expr) : SimpM Expr := do
  let thms ← Simp.getSimpTheorems
  let env ← getEnv
  withTransparency .default <| withCanUnfoldPred (fun cfg info => do
      if thms.isDeclToUnfold info.name || isMatcherCore env info.name ||
          cfgBlockAttr.hasTag env info.name then
        return true
      canUnfoldDefault { cfg with transparency := .instances } info) <|
    whnf e

def lookupBlock (program : Option Name) (blocks : Expr) : SimpM Expr := do
  let thms ← Simp.getSimpTheorems
  let env ← getEnv
  withTransparency .default <| withCanUnfoldPred (fun cfg info => do
      if info.type.isAppOf ``Block then return false
      if program == some info.name || thms.isDeclToUnfold info.name ||
          isMatcherCore env info.name || cfgBlockAttr.hasTag env info.name then
        return true
      canUnfoldDefault { cfg with transparency := .instances } info) <|
    whnf blocks

def definitionHead? (e : Expr) : MetaM (Option Name) := do
  let .const name _ := e.getAppFn | return none
  let some (.defnInfo _) := (← getEnv).find? name | return none
  return some name

inductive OpResult where

  | ok (v store : Expr)

  | guarded (cond inst v store : Expr)

  | stuck

def opResult? (r : Expr) : Option OpResult :=
  let pair? (o : Expr) : Option (Expr × Expr) :=
    if o.isAppOfArity ``Option.some 2 && o.appArg!.isAppOfArity ``Prod.mk 4 then
      some (o.appArg!.appFn!.appArg!, o.appArg!.appArg!)
    else none
  if let some (v, s) := pair? r then some (.ok v s)
  else if r.isAppOfArity ``Option.none 1 then some .stuck
  else if r.isAppOfArity ``ite 5 && r.appArg!.isAppOfArity ``Option.none 1 then
    let args := r.getAppArgs
    (pair? args[3]!).map fun (v, s) => .guarded args[1]! args[2]! v s
  else none

def markSimplified (e : Expr) : SimpM Unit :=
  modify fun s => (if e.isApp then e.getAppArgs.push e else #[e]).foldl (init := s) fun s x =>
    if s.cache.contains x then s
    else { s with cache := s.cache.insert x { expr := x }, dsimpCache := s.dsimpCache.insert x x }

structure Ran where
  n : Expr
  arity : Expr
  op : Expr
  operands : Expr
  next : Expr
  scope : Expr
  store : Expr
  args : Expr
  hargs : Expr
  proof : Expr
  result : OpResult

def leProof (m j : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit m) (mkNatLit j)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

def ltProof (j n : Nat) : Expr := leProof (j + 1) n

def vectorSize? (v : Expr) : MetaM (Option Nat) := do
  let_expr Vector _ n := ← whnfR (← inferType v) | return none
  if let some k ← (evalNat n).run then return some k
  (evalNat (← whnfD n)).run

def elementAt (v : Expr) (j k : Nat) : MetaM Expr := do
  let_expr Vector α n := ← whnfR (← inferType v)
    | throwError "elementAt: not a vector{indentExpr v}"
  let u ← getDecLevel α
  let vector := mkApp2 (mkConst ``Vector [u]) α n
  let nat := mkConst ``Nat
  let valid := mkLambda `xs .default vector <| mkLambda `i .default nat <|
    mkApp4 (mkConst ``LT.lt [0]) nat (mkConst ``instLTNat) (mkBVar 0) n
  return mkAppN (mkConst ``GetElem.getElem [u, 0, u])
    #[vector, nat, α, valid, mkApp2 (mkConst ``Vector.instGetElemNatLt [u]) α n, v, mkNatLit j,
      ltProof j k]

partial def valueElements? (v : Expr) : MetaM (Option (Array Expr)) := do
  if let some elems ← vectorElements? v then return some elems
  if v.isAppOfArity ``HAppend.hAppend 6 then
    let some xs ← valueElements? v.appFn!.appArg! | return none
    let some ys ← valueElements? v.appArg! | return none
    return some (xs ++ ys)
  let some k ← vectorSize? v | return none
  return some (← (List.range k).toArray.mapM (elementAt v · k))

def valuesOf? (scope : Expr) : SimpM (Option (Expr × Array Expr)) := do
  if let some elems ← vectorElements? scope then return some (scope, elems)
  let scope ← Simp.dsimp scope
  return (← valueElements? scope).map (scope, ·)

partial def literalRead (v : Expr) (j : Nat) : MetaM (Option Expr) := do
  let some n ← vectorSize? v | return none
  if v.isAppOfArity ``HAppend.hAppend 6 then
    let α := (← whnfR (← inferType v)).appFn!.appArg!
    let (xs, ys) := (v.appFn!.appArg!, v.appArg!)
    let some m ← vectorSize? xs | return none
    let k := n - m
    if j < m then
      let some h ← literalRead xs j | return none
      return some (← mkEqTrans (mkAppN (mkConst ``Vector.getElem_append_left [0])
        #[α, mkNatLit m, mkNatLit k, mkNatLit j, xs, ys, ltProof j m]) h)
    let some h ← literalRead ys (j - m) | return none
    return some (← mkEqTrans (mkAppN (mkConst ``Vector.getElem_append_right [0])
      #[α, mkNatLit m, mkNatLit k, mkNatLit j, xs, ys, ltProof j n, leProof m j]) h)
  if isVectorLiteral v then
    if let some x := (listElements? v.appFn!.appArg!.appArg!).bind (·[j]?) then
      return some (← mkEqRefl x.headBeta)
  return some (← mkEqRefl (← elementAt v j n))

structure Facts where
  Value : Expr
  values : Array Expr
  regs : Array Expr
  sizes : Array Nat
  pre : Array Expr
  args : Std.HashMap Nat Expr := {}
  facts : Std.HashMap Nat (Nat × Expr) := {}

def Facts.read (F : Facts) (k j : Nat) : MetaM (Facts × Expr) := do
  let n₀ := F.sizes[0]!
  if j < n₀ then
    let (F, base) ← match F.args[j]? with
      | some b => pure (F, b)
      | none =>
        let b ← match ← literalRead F.regs[0]! j with
          | some b => pure b
          | none => mkEqRefl F.values[j]!
        pure ({ F with args := F.args.insert j b }, b)
    return (F, mkAppN (mkConst ``Values.Prefix.read)
      #[F.Value, mkNatLit n₀, mkNatLit F.sizes[k]!, F.regs[0]!, F.regs[k]!, F.pre[k]!, mkNatLit j,
        ltProof j n₀, ltProof j F.sizes[k]!, F.values[j]!, base])
  let (k₀, p₀) := F.facts[j]?.getD (j - n₀ + 1, mkAppN (mkConst ``Values.getElem_push_self)
    #[F.Value, mkNatLit j, F.regs[j - n₀]!, F.values[j]!])
  let mut p := p₀
  for t in [k₀:k] do
    p := mkAppN (mkConst ``Values.getElem_push_of_lt)
      #[F.Value, mkNatLit F.sizes[t]!, F.regs[t]!, F.values[F.sizes[t]!]!, F.values[j]!,
        mkNatLit j, ltProof j F.sizes[t]!, p]
  return ({ F with facts := F.facts.insert j (k, p) }, p)

def Facts.select (F : Facts) (k : Nat) (operands size : Expr) :
    MetaM (Option (Facts × Expr × Expr)) := do
  let some idx ← vectorElements? operands | return none
  let mut F := F
  let mut vals := #[]
  let mut proofs := #[]
  for i in idx do
    let some j ← indexValue? i | return none
    let some x := F.values[j]? | return none
    let (F', p) ← F.read k j
    F := F'
    vals := vals.push x
    proofs := proofs.push p
  let args ← mkVectorLiteral F.Value size vals
  let mut list ← mkEqRefl (mkApp (mkConst ``List.nil [0]) F.Value)
  for p in proofs.reverse do
    list ← mkCongr (← mkCongrArg (mkApp (mkConst ``List.cons [0]) F.Value) p) list
  let n := mkNatLit F.sizes[k]!
  return some (F, args, mkAppN (mkConst ``Values.select_eq)
    #[F.Value, n, size, F.regs[k]!, operands, args, list])

def Facts.selectOf (F : Facts) (k : Nat) (v : Expr) : SimpM (Option (Facts × Expr × Expr)) := do
  let_expr Vector _ size := ← whnfR (← inferType v) | return none
  let r ← Simp.simp v
  let some (F, a, h) ← F.select k r.expr size | return none
  match r.proof? with
  | none => return some (F, a, h)
  | some p =>
    let select := mkApp4 (mkConst ``Values.select) F.Value (mkNatLit F.sizes[k]!) size F.regs[k]!
    return some (F, a, ← mkEqTrans (← mkCongrArg select p) h)

def Facts.option (F : Facts) (k : Nat) (opt : Expr) : SimpM (Option (Facts × Expr)) := do
  let opt := (← Simp.simp opt).expr
  if opt.isAppOfArity ``Option.none 1 then
    return some (F, ← mkEqRefl (mkApp (mkConst ``Option.none [0]) F.Value))
  unless opt.isAppOfArity ``Option.some 2 do return none
  let some j ← indexValue? opt.appArg! | return none
  let (F, p) ← F.read k j
  return some (F, ← mkCongrArg (mkApp (mkConst ``Option.some [0]) F.Value) p)

def edgeFields? (edge : Expr) : SimpM (Option (Expr × Expr)) := do
  let_expr Edge.mk _ _ _ target arguments := ← whnfEval edge | return none
  return some (target, arguments)

def arityProof (arity : Expr) : MetaM Expr := do
  let some (_, lhs, rhs) := (← inferType arity).eq? | return arity
  if ← isDefEq lhs rhs then mkEqRefl lhs else return arity

partial def deepParts (e : Expr) (depth : Nat) (parts : Std.HashMap Expr Nat × Array Expr) :
    Std.HashMap Expr Nat × Array Expr :=
  if !e.hasFVar || !e.isApp then parts
  else if depth = 0 then
    if parts.1.contains e || !e.getAppArgs.any (fun a => a.isApp && a.hasFVar) then parts
    else (parts.1.insert e parts.2.size, parts.2.push e)
  else e.getAppArgs.foldl (fun parts a => deepParts a (depth - 1) parts) parts

def simpOperation (call : Expr) (operands : Array Expr) : SimpM Simp.Result := do
  let (index, parts) := operands.foldl (fun parts o => deepParts o 2 parts) ({}, #[])
  if parts.isEmpty then return ← Simp.simp call
  let types ← parts.mapM fun p => inferType p
  withLocalDeclsDND (types.map (`part, ·)) fun fvars => do
    let call := call.replace fun e => index[e]?.map (fvars[·]!)
    let r ← Simp.simp call
    let back (e : Expr) : SimpM Expr := return (← instantiateMVars e).replaceFVars fvars parts
    return { expr := ← back r.expr, proof? := ← r.proof?.mapM back }

def evalTerminator (common : Array Expr) (F : Facts) (k : Nat) (n t store : Expr) :
    SimpM (Option Expr) := do
  let t ← whnfEval t
  let pre := common ++ #[n, F.regs[k]!, store]
  let pf? ← do
    if t.isAppOfArity ``Terminator.br 5 then
      let some (target, arguments) ← edgeFields? t.appArg! | pure none
      let some (_, a, h) ← F.selectOf k arguments | pure none
      pure (some (mkAppN (mkConst ``Terminator.eval_br) (pre ++ #[target, arguments, a, h])))
    else if t.isAppOfArity ``Terminator.condBr 7 then
      let args := t.getAppArgs
      let some j ← indexValue? args[4]! | pure none
      let some (t₁, arguments₁) ← edgeFields? args[5]! | pure none
      let some (t₂, arguments₂) ← edgeFields? args[6]! | pure none
      let (F, hc) ← F.read k j
      let some (F, a₁, h₁) ← F.selectOf k arguments₁ | pure none
      let some (_, a₂, h₂) ← F.selectOf k arguments₂ | pure none
      pure (some (mkAppN (mkConst ``Terminator.eval_condBr) (pre ++
        #[args[4]!, t₁, t₂, arguments₁, arguments₂, F.values[j]!, a₁, a₂, hc, h₁, h₂])))
    else if t.isAppOfArity ``Terminator.call 6 then
      let args := t.getAppArgs
      let some (target, arguments) ← edgeFields? args[4]! | pure none
      let_expr Cont.mk _ _ _ _ size resume kept arity guard := ← whnfEval args[5]! | pure none
      let some (F, a, h) ← F.selectOf k arguments | pure none
      let some (F, values, hk) ← F.selectOf k kept | pure none
      let some (_, hg) ← F.option k guard | pure none
      let g := (← inferType hg).appArg!
      pure (some (mkAppN (mkConst ``Terminator.eval_call) (pre ++
        #[target, arguments, size, resume, kept, arity, guard, a, values, g, ← arityProof arity, h,
          hk, hg])))
    else if t.isAppOfArity ``Terminator.ret 6 then
      let args := t.getAppArgs
      let some (F, a, h) ← F.selectOf k args[4]! | pure none
      let some (_, hg) ← F.option k args[5]! | pure none
      let g := (← inferType hg).appArg!
      pure (some (mkAppN (mkConst ``Terminator.eval_ret) (pre ++ #[args[4]!, args[5]!, a, g, h, hg])))
    else pure none
  let some pf := pf? | return none
  let some (_, _, rhs) := (← inferType pf).eq? | return none
  let r ← Simp.simp rhs
  return some (← mkEqTrans pf (← r.getProof))

def evalBlock (e : Expr) : SimpM (Option Simp.Result) := do
  let_expr Block.eval Op Label Value Store signature results dialect _ block scope store ← e
    | return none
  let transfer ← inferType e
  let some (scope, elems0) ← valuesOf? (← whnfEval scope) | return none
  let store ← whnfEval store
  elems0.forM markSimplified
  markSimplified store
  let common := #[Op, Label, Value, Store, signature, results, dialect]
  let mut F : Facts := { Value, values := elems0, regs := #[scope], sizes := #[elems0.size],
                         pre := #[mkApp3 (mkConst ``Values.Prefix.refl) Value
                           (mkNatLit elems0.size) scope] }
  let mut store := store
  let mut block ← whnfEval block
  let mut ran : Array Ran := #[]
  let mut final? : Option Expr := none
  repeat
    let k := ran.size
    if block.isAppOfArity ``Block.letOp 9 then
      let a := block.getAppArgs
      let (n, arity, op, operands, next) := (a[4]!, a[5]!, a[6]!, a[7]!, a[8]!)
      let some (F', args, hargs) ← F.select k operands arity | return none
      F := F'
      let call := mkAppN (mkConst ``Dialect.eval) #[Op, Value, Store, dialect, arity, op, args, store]
      let r ← simpOperation call ((← vectorElements? args).getD #[] |>.push store)
      let some out := opResult? r.expr | return none
      ran := ran.push { n, arity, op, operands, next, scope := F.regs[k]!, store, args, hargs,
                        result := out, proof := ← r.getProof }
      match out with
      | .stuck => break
      | .ok v s | .guarded _ _ v s =>
        markSimplified v
        markSimplified s
        let size := F.sizes[k]!
        let regs := mkApp4 (mkConst ``Vector.push [0]) Value (mkNatLit size) F.regs[k]! v
        F := { F with values := F.values.push v, regs := F.regs.push regs,
                      sizes := F.sizes.push (size + 1),
                      pre := F.pre.push (mkAppN (mkConst ``Values.Prefix.push)
                        #[Value, mkNatLit elems0.size, mkNatLit size, scope, F.regs[k]!,
                          F.pre[k]!, v]) }
        store := s
        block ← whnfEval next
    else if block.isAppOfArity ``Block.terminate 6 then
      let a := block.getAppArgs
      let some pf ← evalTerminator common F k a[4]! a[5]! store | return none
      final? := some pf
      break
    else
      return none
  let lemmaArgs (x : Ran) : Array Expr :=
    common ++ #[x.n, x.arity, x.op, x.operands, x.next, x.scope, x.store, x.args]
  let stuck := mkAppN (mkConst ``Transfer.stuck) #[Value, Store, Label, signature, results]
  let (t0, proof0) ← match final?, ran.back? with
    | some pf, _ =>
      let some (_, _, t) := (← inferType pf).eq? | return none
      pure (t, pf)
    | none, some x =>
      ran := ran.pop
      pure (stuck, mkAppN (mkConst ``Block.eval_letOp_none) (lemmaArgs x ++ #[x.hargs, x.proof]))
    | none, none => return none
  let mut t := t0
  let mut proof := proof0
  for x in ran.reverse do
    match x.result with
    | .ok v s =>
      proof := mkAppN (mkConst ``Block.eval_letOp_some)
        (lemmaArgs x ++ #[v, s, t, x.hargs, x.proof, proof])
    | .guarded c inst v s =>
      if t.isAppOf ``Transfer.stuck then
        proof := mkAppN (mkConst ``Block.eval_letOp_ite_stuck)
          (lemmaArgs x ++ #[c, inst, v, s, x.hargs, x.proof, proof])
      else
        proof := mkAppN (mkConst ``Block.eval_letOp_ite)
          (lemmaArgs x ++ #[c, inst, v, s, t, x.hargs, x.proof, proof])
        t := mkApp5 (mkConst ``ite [1]) transfer c inst t stuck
    | .stuck => unreachable!
  return some { expr := t, proof? := some proof }

end Eval

dsimproc ↓ [cfg_eval] reduceRunBlock (Program.runBlock _ _ _) := fun e => do
  let_expr Program.runBlock Op Label Value Store signature results program dialect location ← e
    | return .continue
  let location ← Eval.whnfEval location
  let_expr Location.mk _ _ _ _ label arguments store := location | return .continue
  let blocks := mkAppN (mkConst ``Program.blocks) #[Op, Label, signature, results, program, label]
  let block ← Eval.lookupBlock (← Eval.definitionHead? program) blocks
  return .visit (mkAppN (mkConst ``Block.eval) #[Op, Label, Value, Store, signature, results,
    dialect, mkApp signature label, block, arguments, store])

simproc ↓ [cfg_eval] reduceBlockEval (Block.eval _ _ _ _) := fun e => do
  let some r ← Eval.evalBlock e | return .continue
  return .done r

namespace Eval

def isStep (e : Expr) : Bool :=
  e.isAppOfArity ``Program.runBlock 9 || e.isAppOfArity ``Program.step 9

def stepDefinitions (step : Expr) : MetaM (Array Name) := do
  unless isStep step do return #[]
  let args := step.getAppArgs
  let (dialect, location) := (args[7]!, args[8]!)
  let mut names := #[]
  if let some name ← definitionHead? location then names := names.push name
  let value := (← unfoldDefinition? dialect).getD dialect
  if value.isAppOf ``Dialect.ofPure then
    if let some name ← definitionHead? dialect then names := names.push name
    for arg in value.getAppArgs do
      if let some name ← definitionHead? arg.eta then names := names.push name
  return names

partial def collectSteps (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (seen, acc) => (seen.insert e, acc)
  if isStep e && !e.hasLooseBVars then
    modify fun (seen, acc) => (seen, acc.push e)
    return
  match e with
  | .app f a => do collectSteps f; collectSteps a
  | .lam _ t b _ | .forallE _ t b _ => do collectSteps t; collectSteps b
  | .letE _ t v b _ => do collectSteps t; collectSteps v; collectSteps b
  | .mdata _ b | .proj _ _ b => collectSteps b
  | _ => return

def steps (e : Expr) : Array Expr :=
  ((collectSteps e).run ({}, #[])).2.2

def abstractClosed (e s : Expr) : MetaM Expr := do
  withLocalDeclD `x (← inferType s) fun x =>
    return (e.replace fun u => if u == s then some x else none).abstract #[x]

def evalSteps (ctx : Simp.Context) (simprocs : SimprocsArray) (e : Expr) :
    MetaM (Option Simp.Result) := do
  let e ← instantiateMVars e
  let found := steps e
  if found.isEmpty then return none
  let mut r : Simp.Result := { expr := e }
  for step in found do
    let mut theorems := ctx.simpTheorems
    let mut first := theorems[0]!
    for name in ← stepDefinitions step do
      first ← first.addDeclToUnfold name
    theorems := theorems.set! 0 first
    let (rs, _) ← Simp.main step (ctx.setSimpTheorems theorems)
      (methods := Simp.mkDefaultMethodsCore simprocs)
    let body ← abstractClosed r.expr step
    unless body.hasLooseBVars do continue
    let motive := mkLambda `x .default (← inferType step) body
    let proof? ← rs.proof?.mapM fun h => Meta.mkCongrArg motive h
    r ← r.mkEqTrans { expr := body.instantiate1 rs.expr, proof? }
  return some r

end Eval

syntax (name := cfgEval) "cfg_eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| cfg_eval $[[$ls,*]]? $[$loc]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    let stx ← `(tactic| simp only [cfg_eval, ↓reduceIte, ↓reduceDIte, reduceCtorEq, Nat.reduceDiv,
      Nat.reduceLeDiff, Nat.reduceEqDiff, BitVec.reduceEq, BitVec.reduceNe, BitVec.reduceToNat,
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, $ls,*])
    let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)

    let ctx ← ctx.setConfig { ctx.config with maxSteps := 10000000, bitVecOfNat := false }
    withLocation (expandOptLocation (mkOptionalNode loc))
      (atLocal := fun fvarId => withMainContext do
        let some r ← Eval.evalSteps ctx simprocs (← fvarId.getType)
          | throwError "cfg_eval: no `Program.runBlock` or `Program.step` in the hypothesis"
        match ← applySimpResultToLocalDecl (← getMainGoal) fvarId r (mayCloseGoal := false) with
        | some (_, g) => replaceMainGoal [g]
        | none => replaceMainGoal [])
      (atTarget := withMainContext do
        let some r ← Eval.evalSteps ctx simprocs (← getMainTarget)
          | throwError "cfg_eval: no `Program.runBlock` or `Program.step` in the goal"
        replaceMainGoal [← applySimpResultToTarget (← getMainGoal) (← getMainTarget) r])
      (failed := fun _ =>
        throwError "cfg_eval: no `Program.runBlock` or `Program.step` to evaluate")

namespace Eval

partial def stores (σ : Expr) (e : Expr) : MetaM (Array Expr) := do
  let rec visit (e : Expr) : StateT (Std.HashSet Expr × Array Expr) MetaM Unit := do
    if (← get).1.contains e || e.hasLooseBVars then return
    modify fun (seen, out) => (seen.insert e, out)
    match e with
    | .app f a =>
      visit f
      visit a
      if (← inferType e) == σ then modify fun (seen, out) => (seen, out.push e)
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ b | .proj _ _ b => visit b
    | _ => pure ()
  return ((← (visit e).run ({}, #[])).2).2

def nameStores (σ : Expr) (e : Expr) : MetaM Expr := do
  let e := ShareCommon.shareCommon' e
  let stores ← Eval.stores σ e
  let rec go (i : Nat) (names : Std.HashMap Expr Expr) (xs : Array Expr) : MetaM Expr := do
    if h : i < stores.size then
      let s := stores[i]
      let value := s.replace fun u => if u == s then none else names[u]?
      withLetDecl (.mkSimple s!"mem{(i + 1).toSubscriptString}") σ value fun x =>
        go (i + 1) (names.insert s x) (xs.push x)
    else
      mkLetFVars xs (e.replace fun u => names[u]?)
  go 0 {} #[]

end Eval

elab "cfg_name_stores" : tactic => withMainContext do
  let g ← getMainGoal
  let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
    | throwError "cfg_name_stores: the goal is not an equation"
  let_expr Transfer _ σ _ _ _ := ← whnfR (← inferType lhs)
    | throwError "cfg_name_stores: the left side is not a transfer"
  replaceMainGoal [← g.replaceTargetDefEq (← mkEq (← Eval.nameStores σ lhs) rhs)]

syntax "cfg_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| cfg_close $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| first
      | rfl
      | (split <;> cfg_close [$ls,*])
      | (exfalso; simp_all [$ls,*]; done)
      | (exfalso; omega))

syntax "cfg_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (" at " ident)? : tactic

syntax "cfg_invert " ident : tactic

macro_rules
  | `(tactic| cfg_invert $h) => `(tactic| first
      | cases $h:ident
      | (split at $h:ident <;> cfg_invert $h))

macro_rules
  | `(tactic| cfg_step $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      try dsimp only [$ls,*]
      cfg_eval [$ls,*]
      cfg_close [$ls,*]))
  | `(tactic| cfg_step $[[$ls,*]]? at $h) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      cfg_eval [$ls,*] at $h:ident
      cfg_invert $h))

end K256.Proofs.CFG
