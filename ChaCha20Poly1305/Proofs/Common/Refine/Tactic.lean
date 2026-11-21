import ChaCha20Poly1305.Proofs.Common.Refine.Simulation
import ChaCha20Poly1305.Proofs.Common.Refine.Frame
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Store
import ChaCha20Poly1305.Proofs.Common.Refine.Lemma.Norm
import ChaCha20Poly1305.Proofs.Common.Lift.Generated.Values

namespace ChaCha20Poly1305.Proofs.Refine
open X86Proofs

open Lean Meta Elab Tactic
open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift Prelude

syntax "refine_ext" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| refine_ext [$_,*]) => `(tactic| fail "refine_ext: no extension applies")

syntax "refine_post" " [" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| refine_post [$_,*] $[$_]?) => `(tactic| skip)

namespace Tactic

partial def reduceLayoutField (e : Expr) (labelIdx : Option Nat) : MetaM (Option Expr) := do
  let args := e.getAppArgs
  let some L := args[10]? | return none
  let .const lname _ := L.getAppFn | return none
  let some (.defnInfo _) := (← getEnv).find? lname | return none
  if let some i := labelIdx then
    let some l := args[i]? | return none
    let l ← whnfR l
    let .const ln _ := l.getAppFn | return none
    let some (.ctorInfo _) := (← getEnv).find? ln | return none
  let some Lv ← withDefault (unfoldDefinition? L) | return none

  if let .const cn _ := Lv.getAppFn then
    if let some (.defnInfo _) := (← getEnv).find? cn then
      let some fn := e.getAppFn.constName? | return none
      let some info ← getProjectionFnInfo? fn | return none
      let some mk ← withDefault (unfoldDefinition? Lv) | return none
      let some f := mk.getAppArgs[info.numParams + info.i]? | return none
      let r := (mkAppN f (args.extract (info.numParams + 1) args.size)).headBeta
      if let some fn' := r.getAppFn.constName? then
        if (← getProjectionFnInfo? fn').isSome && r.getAppNumArgs > 10 then
          if let some r' ← reduceLayoutField r labelIdx then return some r'
      return some r
  let e' := mkAppN e.getAppFn (args.set! 10 Lv)
  let r ← withReducible (whnf e')
  if r == e' then return none
  if let .proj sn i x := r then
    if let some f := (getStructureFields (← getEnv) sn)[i]? then
      return some (← mkAppM (sn ++ f) #[x])
  return some r

dsimproc [refine_layout] layoutStart (Layout.start _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutParams (Layout.Params _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutArgs (Layout.args _ _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutStore (Layout.store _ _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutAtoms (Layout.atoms _ _ _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutOutput (Layout.output _ _) := fun e => do
  return match ← reduceLayoutField e none with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutDone (Layout.done _ _ _) := fun e => do
  return match ← reduceLayoutField e none with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutRetAddr (Layout.retAddr _ _) := fun e => do
  return match ← reduceLayoutField e none with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutOriginal (Layout.original _ _) := fun e => do
  return match ← reduceLayoutField e none with | some r => .visit r | none => .continue
dsimproc [refine_layout] layoutRegions (Layout.regions _ _) := fun e => do
  return match ← reduceLayoutField e none with | some r => .visit r | none => .continue

dsimproc [refine_layout] coreStart (LayoutCore.start _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] coreParams (LayoutCore.Params _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] coreArgs (LayoutCore.args _ _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] coreStore (LayoutCore.store _ _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] coreAtoms (LayoutCore.atoms _ _ _ _ _) := fun e => do
  return match ← reduceLayoutField e (some 11) with | some r => .visit r | none => .continue
dsimproc [refine_layout] coreOutput (LayoutCore.output _ _) := fun e => do
  return match ← reduceLayoutField e none with | some r => .visit r | none => .continue
dsimproc [refine_layout] coreDone (LayoutCore.done _ _ _ _) := fun e => do
  return match ← reduceLayoutField e none with | some r => .visit r | none => .continue
dsimproc [refine_layout] coreFootprint (LayoutCore.footprint _ _ _) := fun e => do
  return match ← reduceLayoutField e none with | some r => .visit r | none => .continue

attribute [refine_layout] reduceGetElemFin reduceGetElem Value.mk.injEq heq_eq_eq true_and
  and_true

simproc [refine_norm] reduceGetElemSet
    (@GetElem.getElem (Vector _ _) Nat _ _ _ (Vector.set _ _ _ _) _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ xs j hj := e | return .continue
  let some jv ← Eval.indexValue? j | return .continue
  let read (v : Expr) : Expr := mkAppN e.getAppFn (e.getAppArgs.set! 5 v)
  let mut cur := xs
  let mut proof? : Option Expr := none
  repeat
    let_expr Vector.set α n ys i x hi := cur | break
    let some iv ← Eval.indexValue? i | break
    if iv == jv then
      let q ← mkAppOptM ``Vector.getElem_set_self
        #[some α, some n, some ys, some i, some x, some hi]
      let p ← match proof? with | none => pure q | some p => mkEqTrans p q
      return .visit { expr := x, proof? := p }
    let hne ← mkDecideProof (← mkAppM ``Ne #[i, j])
    let q ← mkAppOptM ``Vector.getElem_set_ne
      #[some α, some n, some i, some j, some ys, some x, some hi, some hj, some hne]
    proof? ← match proof? with | none => pure q | some p => mkEqTrans p q
    cur := ys
  match proof? with
  | none => return .continue
  | some p => return .visit { expr := read cur, proof? := p }

def readVectors (g : MVarId) : MetaM MVarId := g.withContext do
  let t ← Meta.transform (← instantiateMVars (← g.getType))
    (pre := fun e => do return if ← isProof e then .done e else .continue)
    (post := fun e => do
      return match ← Eval.getElem? e with | some x => .visit x | none => .continue)
  g.replaceTargetDefEq t

abbrev SimpArgs := Array (TSyntax ``Lean.Parser.Tactic.simpLemma)

def simpArg (n : Name) : TacticM (TSyntax ``Lean.Parser.Tactic.simpLemma) :=
  `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)

def runOn (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [g]
  try
    withoutRecover tac
    getGoals
  finally
    setGoals saved

def tryClose (g : MVarId) (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← runOn g tac
    if gs.isEmpty then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

def tryRun (g : MVarId) (tac : TacticM Unit) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  try
    return some (← runOn g tac)
  catch _ =>
    s.restore
    return none

def applyLemma (g : MVarId) (n : Name) : MetaM (List MVarId) := g.withContext do
  let f ← mkConstWithFreshMVarLevels n
  let (ms, bis, concl) ← forallMetaTelescope (← inferType f)
  unless ← isDefEq concl (← g.getType) do throwError "x86_refine: `{n}` does not apply"
  g.assign (mkAppN f ms)
  let mut out := []
  for m in ms, bi in bis do
    if bi.isExplicit && !(← m.mvarId!.isAssigned) then
      m.mvarId!.setKind .syntheticOpaque
      out := out ++ [m.mvarId!]
  return out

def assignProof (g : MVarId) (p? : Option Expr) : MetaM Bool := do
  let some p := p? | return false
  g.assign p
  return true

partial def conjuncts (e : Expr) : MetaM (Array Expr) := do
  let ty ← whnfR (← instantiateMVars (← inferType e))
  if ty.isAppOfArity ``And 2 then
    return (← conjuncts (← mkAppM ``And.left #[e])) ++ (← conjuncts (← mkAppM ``And.right #[e]))
  else return #[e]

def dataFields? (ty : Expr) : MetaM (Option (Array Name)) := do
  let ty ← whnfD ty
  let .const n _ := ty.getAppFn | return none
  let env ← getEnv
  unless isStructure env n do return none
  let fields := getStructureFields env n
  let ctor := getStructureCtor env n
  let mut t ← instantiateForall (← inferType (mkConst ctor.name ty.getAppFn.constLevels!))
    ty.getAppArgs
  let mut data := 0
  for _ in fields do
    let .forallE _ d b _ := t | break
    unless ← isProp d do data := data + 1
    t := b
  if data < 2 then return none
  return some fields

def hypsWithHead (n : Name) : MetaM (Array LocalDecl) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf n then out := out.push d
  return out

def freshName (pre : String) : MetaM Name := do
  let lctx ← getLCtx
  let mut k := 0
  while (lctx.findFromUserName? (Name.mkSimple s!"{pre}{k}")).isSome do k := k + 1
  return Name.mkSimple s!"{pre}{k}"

def layoutParts? (r : Expr) : Option (Expr × Expr × Expr) :=
  if r.isAppOf ``Layout.Rel || r.isAppOf ``Layout.RetRel || r.isAppOf ``Layout.MatchedBy ||
      r.isAppOf ``Layout.Resumes then
    let args := r.getAppArgs
    if args.size < 13 then none else some (args[10]!, args[11]!, args[12]!)
  else none

def layoutDialect (L : Expr) : MetaM Expr := do
  let ty ← whnfR (← inferType L)
  return ty.getArg! 7

def constDefs (e : Expr) : MetaM (Array Name) := do
  let .const n _ := e.getAppFn | return #[]
  let mut names := #[n]
  let some (.defnInfo info) := (← getEnv).find? n | return names
  for arg in info.value.getAppArgs do
    if let .const m _ := arg.eta.getAppFn then
      if let some (.defnInfo d) := (← getEnv).find? m then
        unless d.type.isSort do names := names.push m
  return names

def regVars (pre : String) : Array Ident :=
  (List.range Reg.count).toArray.map fun i => mkIdent (Name.mkSimple s!"{pre}{i}")

inductive Role where
  | rewrite
  | frame

initialize introduced : IO.Ref (Std.HashMap FVarId Role) ← IO.mkRef {}

def registerNames (role : Role) (names : Array Name) : MetaM Unit := do
  let lctx ← getLCtx
  let ids := names.filterMap fun n => (lctx.findFromUserName? n).map (·.fvarId)
  introduced.modify fun m => ids.foldl (fun m i => m.insert i role) m

structure Shared where
  lemmas : SimpArgs
  arith : Simp.Context
  arithProcs : Simp.SimprocsArray
  bv : Simp.Context
  bvProcs : Simp.SimprocsArray
  norm : Simp.Context
  normProcs : Simp.SimprocsArray
  layout : Simp.Context × Simp.SimprocsArray
  words : Simp.Context × Simp.SimprocsArray
  resume : Simp.Context × Simp.SimprocsArray
  normCache : IO.Ref (Array FVarId × Option Simp.Context)
  proofs : IO.Ref (Std.HashMap Expr (Expr × Array FVarId))
  stores : IO.Ref (Std.HashMap Expr (Simp.Result × Array FVarId))

def Shared.new (lemmas : SimpArgs) : TacticM Shared := do
  let arith ← mkSimpContext (← `(tactic| simp -failIfUnchanged only [InRegions, InRegion, Outside,
    RegionsWithin, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    exists_eq_or_imp, exists_eq_left, $lemmas,*])) (eraseLocal := false)
  let bv ← mkSimpContext (← `(tactic| simp -implicitDefEqProofs -failIfUnchanged only
    [bitvec_to_nat, toInt_eq_biased, decide_eq_true_eq, decide_eq_false_iff_not]))
    (eraseLocal := false)
  let norm ← mkSimpContext (← `(tactic|
    simp (config := { bitVecOfNat := false, maxSteps := 10000000, failIfUnchanged := false })
      only [refine_layout, refine_norm, Lift.reduceAddOffset, Lift.reduceSubOffset,
    Lift.reduceAddNeg, Lift.reduceSubNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceMul,
    BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceToNat, BitVec.reduceSetWidth,
    BitVec.reduceOfNat, Nat.reduceDiv,
    add_zero_lit, sub_zero_lit, BitVec.setWidth_eq, Value.get_mk_setWidth,
    Bool.not_true, Bool.not_false, Classical.not_not, $lemmas,*])) (eraseLocal := false)
  let layout ← mkSimpContext (← `(tactic| simp -failIfUnchanged only [refine_layout,
    Option.some.injEq])) (eraseLocal := false)
  let words ← mkSimpContext (← `(tactic|
    simp (config := { bitVecOfNat := false, failIfUnchanged := false }) only [wordAddr,
      Nat.reduceDiv, Nat.reduceMul, BitVec.reduceOfNat, add_zero_lit, Lift.reduceAddOffset,
      Lift.reduceSubOffset]))
    (eraseLocal := false)
  let resume ← mkSimpContext (← `(tactic| simp -failIfUnchanged only [StackFrame.resume, cfg_eval,
    refine_layout, decide_eq_true_eq])) (eraseLocal := false)
  return { lemmas, arith := arith.ctx, arithProcs := arith.simprocs, bv := bv.ctx,
           bvProcs := bv.simprocs, norm := norm.ctx, normProcs := norm.simprocs,
           layout := (layout.ctx, layout.simprocs), words := (words.ctx, words.simprocs),
           resume := (resume.ctx, resume.simprocs), normCache := ← IO.mkRef (#[], none),
           proofs := ← IO.mkRef {}, stores := ← IO.mkRef {} }

def cached (S : Shared) (ty : Expr) (prove : MetaM (Option Expr)) : MetaM (Option Expr) := do
  let ty ← instantiateMVars ty
  let lctx ← getLCtx
  if let some (p, fvs) := (← S.proofs.get)[ty]? then
    if fvs.all lctx.contains then return some p
  let some p ← prove | return none
  let p ← instantiateMVars p
  unless p.hasMVar do
    let fvs := ((CollectFVars.main p) {}).fvarIds
    S.proofs.modify (·.insert ty (p, fvs))
  return some p

def arithArgs? (e : Expr) : Option (List Nat) :=
  match e.getAppFn.constName? with
  | some ``HAdd.hAdd | some ``HSub.hSub | some ``HMul.hMul | some ``HDiv.hDiv
  | some ``HMod.hMod | some ``HPow.hPow | some ``HShiftLeft.hShiftLeft | some ``HAnd.hAnd =>
    some [4, 5]
  | some ``LE.le | some ``LT.lt | some ``GE.ge | some ``GT.gt | some ``min | some ``max => some [2, 3]
  | some ``Eq | some ``Ne => some [1, 2]
  | some ``Or | some ``And | some ``Iff => some [0, 1]
  | some ``Not => some [0]
  | some ``BitVec.toNat | some ``BitVec.toInt | some ``BitVec.ofNat | some ``BitVec.msb => some [1]
  | some ``Neg.neg => some [2]
  | some ``Nat.succ => some [0]
  | some ``OfNat.ofNat => some []
  | _ => none

partial def arithAtoms (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let e := e.consumeMData
  if e.isRawNatLit || e.isSort || e.hasLooseBVars then return acc
  if let .forallE _ d b _ := e then
    if b.hasLooseBVars then return acc
    return ← arithAtoms b (← arithAtoms d acc)
  if let some is := arithArgs? e then
    let args := e.getAppArgs
    let mut acc := acc
    for i in is do
      if let some a := args[i]? then acc ← arithAtoms a acc
    return acc
  if e.isConst || e.isLit then return acc
  return if acc.contains e then acc else acc.push e

def focusedOmega (S : Shared) (g : MVarId) (extra : Array Expr := #[]) : MetaM Bool := do
  let s ← saveState
  try
    g.withContext do
      let mut atoms : Std.HashSet Expr := {}
      for a in ← arithAtoms (← instantiateMVars (← g.getType)) do atoms := atoms.insert a
      for x in extra do
        for a in ← arithAtoms (← instantiateMVars x) do atoms := atoms.insert a
      let mut facts : Array (FVarId × Array Expr) := #[]
      let mut props : Array FVarId := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        unless ← isProp t do continue
        props := props.push d.fvarId
        if (arithArgs? t).isSome then facts := facts.push (d.fvarId, ← arithAtoms t)
      let mut keep : Std.HashSet FVarId := {}
      let mut changed := true
      while changed do
        changed := false
        for (f, as) in facts do
          if keep.contains f || !as.any atoms.contains then continue
          keep := keep.insert f
          changed := true
          for a in as do atoms := atoms.insert a
      let g ← g.tryClearMany (props.filter (!keep.contains ·))
      let kept ← g.withContext do
        return (← getLCtx).foldl (init := #[]) fun acc d =>
          if keep.contains d.fvarId then acc.push d.fvarId else acc
      let (r, _) ← simpGoal g S.bv S.bvProcs (fvarIdsToSimp := kept)
      let some (_, g) := r | return true
      let some g ← g.falseOrByContra | return true
      g.withContext do Omega.omega (← getLocalHyps).toList g {}
      return true
  catch _ =>
    s.restore
    return false

def closeArith (S : Shared) (g : MVarId) (extra : Array Expr := #[]) : MetaM Bool := do
  let s ← saveState
  try
    let (r, _) ← simpTarget g S.arith S.arithProcs
    let some g := r | return true
    if ← focusedOmega S g extra then return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

def proveArith (S : Shared) (p : Expr) : MetaM (Option Expr) := do
  let g ← mkFreshExprMVar p
  if ← closeArith S g.mvarId! then return some (← instantiateMVars g) else return none

def decideClosed? (p : Expr) : MetaM (Option Expr) := do
  if p.hasFVar || p.hasMVar then return none
  try
    let d ← mkDecide p
    let r ← withAtLeastTransparency .default <| whnf d
    if r.isConstOf ``true then return some (← mkDecideProof p) else return none
  catch _ => return none

def bvLit? (e : Expr) : MetaM (Option Nat) := do
  let some ⟨n, v⟩ ← getBitVecValue? e | return none
  return if n == 64 then some v.toNat else none

structure Addr where
  base : Expr
  off : Expr
  val : Nat
  eq : Expr

def addrOf (a : Expr) : MetaM Addr := do
  let a ← instantiateMVars a
  let mk (eq : Expr) (val : Nat) : MetaM Addr := do
    let some (_, _, rhs) := (← inferType eq).eq? | throwError "addrOf"
    return { base := rhs.appFn!.appArg!, off := rhs.appArg!, val, eq }
  if let some k ← bvLit? a then return ← mk (mkApp (mkConst ``addr_lit) a) k
  if a.isAppOfArity ``HAdd.hAdd 6 then
    if let some k ← bvLit? a.appArg! then return ← mk (← mkEqRefl a) k
  if a.isAppOfArity ``HSub.hSub 6 then
    if let some k ← bvLit? a.appArg! then
      return ← mk (mkApp2 (mkConst ``addr_sub) a.appFn!.appArg! a.appArg!) ((2 ^ 64 - k) % 2 ^ 64)
  mk (mkApp (mkConst ``addr_self) a) 0

def dist (x y : Nat) : Nat := (x + 2 ^ 64 - y) % 2 ^ 64

structure Region where
  hyp : Expr
  type : Expr
  writable : Bool
  mem : Expr
  addr : Addr
  start : Expr
  lenE : Expr
  len : Option Nat
  low : Expr

def regions : MetaM (Array Region) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let (writable, args) :=
      if ty.isAppOfArity ``Writable 4 then (true, ty.getAppArgs.extract 1 4)
      else if ty.isAppOfArity ``Readable 3 then (false, ty.getAppArgs)
      else (false, #[])
    let some mem := args[0]? | continue
    let len ← (evalNat args[2]!).run
    let r ← if writable then mkAppM ``Writable.readable #[d.toExpr] else pure d.toExpr
    out := out.push { hyp := d.toExpr, type := ty, writable, mem, addr := ← addrOf args[1]!,
                      start := args[1]!, lenE := args[2]!, len,
                      low := ← mkAppM ``Readable.low #[r] }
  return out

def regionOf? (rs : Array Region) (a : Addr) (n : Nat) (writable := false) : Option Region :=
  rs.find? fun r => (r.writable || !writable) && r.addr.base == a.base &&
    r.len.any (dist a.val r.addr.val + n ≤ ·)

def mkAdd' (x y : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[x, y]
def mkLe' (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
def toNatE (x : Expr) : MetaM Expr := mkAppM ``BitVec.toNat #[x]
def subToNat (x y : Expr) : MetaM Expr := do toNatE (← mkAppM ``HSub.hSub #[x, y])

def insideProp (a : Addr) (r : Region) (n : Expr) : MetaM Expr := do
  mkLe' (← mkAdd' (← subToNat a.off r.addr.off) n) r.lenE

def apartProp (r s : Region) : MetaM Expr := do
  let rn ← toNatE r.start
  let sn ← toNatE s.start
  return mkOr (← mkLe' (← mkAdd' rn r.lenE) sn) (← mkLe' (← mkAdd' sn s.lenE) rn)

def apartProof? (S : Shared) (a n b k : Expr) : MetaM (Option Expr) := do
  let some nv ← (evalNat n).run | return none
  let some kv ← (evalNat k).run | return none
  let fa ← addrOf a
  let fb ← addrOf b
  if fa.base == fb.base then
    unless nv ≤ dist fb.val fa.val && kv ≤ dist fa.val fb.val do return none
    let h ← mkDecideProof (mkAnd (← mkLe' n (← subToNat fb.off fa.off))
      (← mkLe' k (← subToNat fa.off fb.off)))
    return some (← mkAppM ``RangeApart.of_offsets #[fa.eq, fb.eq, h])
  let rs ← regions
  let some ra := regionOf? rs fa nv | return none
  let some rb := regionOf? rs fb kv | return none
  let some hap ← cached S (← apartProp ra rb) do proveArith S (← apartProp ra rb) | return none
  let hin ← mkDecideProof (mkAnd (← insideProp fa ra n) (← insideProp fb rb k))
  return some (← mkAppM ``RangeApart.of_regions
    #[fa.eq, ra.addr.eq, fb.eq, rb.addr.eq, ra.low, rb.low, hap, hin])

def dischargeProp (S : Shared) (p : Expr) : MetaM (Option Expr) := do
  let p ← instantiateMVars p
  if p.hasExprMVar then return none
  cached S p do
    if let some h ← decideClosed? p then return some h
    if !p.hasFVar && (p.isAppOfArity ``LE.le 4 || p.isAppOfArity ``LT.lt 4) then return none
    if p.isAppOfArity ``RangeApart 4 then
      let args := p.getAppArgs
      if let some h ← apartProof? S args[0]! args[1]! args[2]! args[3]! then return some h
      let mut f := mkAppN (mkConst ``RangeApart.of_toNat) #[args[0]!, args[2]!, args[1]!, args[3]!]
      let mut ty ← inferType f
      for _ in [0:3] do
        let .forallE _ q b _ := ty | return none
        let some h ← cached S q (proveArith S q) | return none
        f := mkApp f h
        ty := b.instantiate1 h
      return some f
    proveArith S p

def discharger (S : Shared) : Simp.Discharge := fun e => dischargeProp S e

def frameInto? (m : Expr) : MetaM (Option LocalDecl) := do
  for d in ← hypsWithHead ``RamWriteFrame do
    if (← instantiateMVars d.type).getArg! 1 == m then return some d
  return none

partial def regionOn (S : Shared) (r : Region) (m : Expr) : MetaM (Option Expr) := do
  if m == r.mem then return some r.hyp
  let args := r.type.getAppArgs
  let ty := mkAppN r.type.getAppFn (args.set! (if r.writable then 1 else 0) m)
  cached S ty do
    if m.isAppOfArity ``memStore 6 then
      let some h ← regionOn S r (m.getArg! 2) | return none
      let lem := if r.writable then ``Writable.memStore else ``Readable.memStore
      return some (← mkAppM lem #[h, m.getArg! 3, m.getArg! 5])
    if let some hf ← frameInto? m then
      let some h ← regionOn S r ((← instantiateMVars hf.type).getArg! 0) | return none
      let lem := if r.writable then ``Writable.of_frame else ``Readable.of_frame
      return some (← mkAppM lem #[h, hf.toExpr])
    return none

inductive Part where
  | offsets (r : Region) (h : Expr) (a : Addr) (hin : Expr)
  | bounds (r : Region) (h : Expr) (h₁ h₂ : Expr)

def partOf? (S : Shared) (m a n : Expr) (writable : Bool) : MetaM (Option Part) := do
  let fa ← addrOf a
  let rs ← regions
  if let some nv ← (evalNat n).run then
    if let some r := regionOf? rs fa nv writable then
      if let some h ← regionOn S r m then
        return some (.offsets r h fa (← mkDecideProof (← insideProp fa r n)))
  let an ← toNatE a
  let (same, other) := rs.partition (·.addr.base == fa.base)
  for r in same ++ other do
    unless r.writable || !writable do continue
    let bn ← toNatE r.start
    let t₁ ← mkLe' bn an
    let some h₁ ← cached S t₁ (proveArith S t₁) | continue
    let t₂ ← mkLe' (← mkAdd' an n) (← mkAdd' bn r.lenE)
    let some h₂ ← cached S t₂ (proveArith S t₂) | continue
    let some h ← regionOn S r m | continue
    return some (.bounds r h h₁ h₂)
  return none

def loadProof? (S : Shared) (m a n : Expr) : MetaM (Option Expr) := do
  let readable (r : Region) (h : Expr) : MetaM Expr :=
    if r.writable then mkAppM ``Writable.readable #[h] else pure h
  match ← partOf? S m a n false with
  | some (.offsets r h fa hin) =>
    return some (← mkAppM ``LoadOk.of_offsets #[← readable r h, fa.eq, r.addr.eq, hin])
  | some (.bounds r h h₁ h₂) => return some (← mkAppM ``LoadOk.of_region #[← readable r h, h₁, h₂])
  | none => return none

def storeProof? (S : Shared) (m a n p k : Expr) : MetaM (Option Expr) := do
  let some part ← partOf? S m a n true | return none
  let apartTy ← mkAppM ``RangeApart #[a, n, p, k]
  let some hap ← dischargeProp S apartTy | return none
  match part with
  | .offsets r h fa hin =>
    return some (← mkAppM ``StoreOk.of_offsets #[h, fa.eq, r.addr.eq, hin, hap])
  | .bounds _ h h₁ h₂ => return some (← mkAppM ``StoreOk.of_region #[h, h₁, h₂, hap])

simproc_decl memLoadKeys (memLoad _ _ _) := fun _ => return .continue
simproc_decl memStoreKeys (memStore _ _ _) := fun _ => return .continue

def sameAddr? (a b : Expr) : MetaM (Option Expr) := do
  if a == b then return some (← mkEqRefl a)
  let fa ← addrOf a
  let fb ← addrOf b
  unless fa.base == fb.base && fa.val == fb.val do return none
  return some (← mkAppM ``addr_eq_of_offsets
    #[fa.eq, fb.eq, ← mkDecideProof (← mkAppM ``Eq #[fa.off, fb.off])])

def callFrameInto? (m : Expr) : MetaM (Option LocalDecl) := do
  let reg ← introduced.get
  for d in ← hypsWithHead ``RamWriteFrame do
    if let some .frame := reg[d.fvarId]? then
      if (← instantiateMVars d.type).getArg! 1 == m then return some d
  return none

def within? (m a n v b w : Expr) (wv nv : Nat) : MetaM (Option (Nat × Expr)) := do
  let fa ← addrOf a
  let fb ← addrOf b
  unless fa.base == fb.base do return none
  let off := dist fb.val fa.val
  unless off + wv / 8 ≤ nv / 8 do return none
  let offE ← mkAppM ``BitVec.ofNat #[mkNatLit 64, mkNatLit off]
  let hoff ← mkDecideProof (← mkAppM ``Eq #[← mkAppM ``HSub.hSub #[fb.off, fa.off], offE])
  let hb ← mkAppM ``addr_add_of_offsets #[fa.eq, fb.eq, hoff]
  let hw ← mkDecideProof (← mkAppM ``Eq #[← mkAppM ``HMod.hMod #[w, mkNatLit 8], mkNatLit 0])
  let hin ← mkDecideProof (← mkLe' (← mkAdd' (mkNatLit off) (← mkAppM ``HDiv.hDiv #[w, mkNatLit 8]))
    (← mkAppM ``HDiv.hDiv #[n, mkNatLit 8]))
  let h128 ← mkDecideProof (← mkLe' n (mkNatLit 128))
  return some (off, mkAppN (mkConst ``memLoad_memStore_within)
    #[m, a, b, n, v, w, mkNatLit off, hb, hw, hin, h128])

def forwardLoad (S : Shared) : Simp.Simproc := fun e => do
  unless e.isAppOfArity ``memLoad 5 do return .continue
  let args := e.getAppArgs
  let (b, w) := (args[3]!, args[4]!)
  let some wv ← (evalNat w).run | return .continue
  let ty ← inferType e
  let load (m : Expr) := mkAppN (mkConst ``memLoad) #[args[0]!, args[1]!, m, b, w]
  let trans (p? : Option Expr) (lhs rhs : Expr) (q : Expr) : Expr := match p? with
    | none => q
    | some p => mkApp6 (mkConst ``Eq.trans [Level.one]) ty e lhs rhs p q
  let mut cur := args[2]!
  let mut proof? : Option Expr := none
  repeat
    if cur.isAppOfArity ``memStore 6 then
      let (m', a, n, v) := (cur.getArg! 2, cur.getArg! 3, cur.getArg! 4, cur.getArg! 5)
      let some nv ← (evalNat n).run | break
      if nv == wv then
        if let some hab ← sameAddr? a b then
          let h8 ← mkDecideProof
            (← mkAppM ``Eq #[← mkAppM ``HMod.hMod #[n, mkNatLit 8], mkNatLit 0])
          let h128 ← mkDecideProof (← mkLe' n (mkNatLit 128))
          let q := mkAppN (mkConst ``memLoad_memStore_eq) #[m', a, b, n, v, hab, h8, h128]
          return .visit { expr := v, proof? := trans proof? (load cur) v q }
      else if wv < nv && nv ≤ 128 && wv % 8 == 0 then
        if let some (off, q) ← within? m' a n v b w wv nv then
          let x := mkApp4 (mkConst ``BitVec.extractLsb') n (mkNatLit (8 * off)) w v
          return .visit { expr := x, proof? := trans proof? (load cur) x q }
      let some hap ← dischargeProp S
          (mkApp4 (mkConst ``RangeApart) a (mkNatLit (nv / 8)) b (mkNatLit (wv / 8))) | break
      let q := mkAppN (mkConst ``memLoad_memStore_of_rangeApart) #[m', a, b, n, v, w, hap]
      proof? := some (trans proof? (load cur) (load m') q)
      cur := m'
    else if let some hf ← callFrameInto? cur then
      let t ← instantiateMVars hf.type
      let (o, regs) := (t.getArg! 0, t.getArg! 2)
      let some hout ← dischargeProp S (mkApp3 (mkConst ``Outside) regs b (mkNatLit (wv / 8)))
        | break
      let q := mkAppN (mkConst ``RamWriteFrame.memLoad_eq) #[o, cur, regs, hf.toExpr, b, w, hout]
      proof? := some (trans proof? (load cur) (load o) q)
      cur := o
    else break
  match proof? with
  | none => return .continue
  | some p => return .visit { expr := load cur, proof? := p }

def skipStores : Simp.Simproc := fun e => return .done { expr := e }

def skipStoresProcs : MetaM Simp.Simprocs := do
  let some keys ← Simp.getSimprocDeclKeys? ``memStoreKeys | throwError "skipStores"
  return ({} : Simp.Simprocs).addCore keys ``memStoreKeys false (.inl skipStores)

def normStores (S : Shared) : Simp.Simproc := fun e => do
  unless e.isAppOfArity ``memStore 6 do return .continue
  let lctx ← getLCtx
  let stores ← S.stores.get
  let mut chain : Array Expr := #[]
  let mut cur := e
  let mut r : Simp.Result := { expr := e }
  let mut fvs : Array FVarId := #[]
  repeat
    if let some (c, cfvs) := stores[cur]? then
      if cfvs.all lctx.contains then
        (r, fvs) := (c, cfvs)
        break
    unless cur.isAppOfArity ``memStore 6 do
      r := { expr := cur }
      break
    chain := chain.push cur
    cur := cur.getArg! 2
  for st in chain.reverse do
    let args := st.getAppArgs
    let ra ← Simp.simp args[3]!
    let f := mkApp2 st.getAppFn args[0]! args[1]!
    let rm ← Simp.mkCongrArg f r
    let rs ← Simp.mkCongr rm ra
    r ← Simp.mkCongrFun (← Simp.mkCongrFun rs args[4]!) args[5]!
    let used := ra.proof?.elim {} (CollectFVars.main · {}) |> CollectFVars.main ra.expr
    fvs := used.fvarIds.foldl (fun fvs x => if fvs.contains x then fvs else fvs.push x) fvs
    S.stores.modify (·.insert st (r, fvs))
  return .done r

def simpShallow (set : Simp.Context × Simp.SimprocsArray) (g : MVarId) (hs : Array FVarId := #[]) :
    MetaM (Option MVarId) := g.withContext do
  let (r, _) ← simpGoal g set.1 (set.2.push (← skipStoresProcs)) (simplifyTarget := hs.isEmpty)
    (fvarIdsToSimp := hs)
  return r.map (·.2)

def normContext (S : Shared) : MetaM Simp.Context := do
  let reg ← introduced.get
  let mut hs : Array (LocalDecl × Role) := #[]
  for d in ← getLCtx do
    if let some role := reg[d.fvarId]? then hs := hs.push (d, role)
  let ids := hs.map (·.1.fvarId)
  let (ids', ctx?) ← S.normCache.get
  if let some ctx := ctx? then
    if ids' == ids then return ctx
  let mut extra : SimpTheorems := {}
  for (d, role) in hs do
    match role with
    | .rewrite =>
      if (← instantiateMVars d.type).isAppOfArity ``Eq 3 then
        extra ← extra.add (.fvar d.fvarId) #[] d.toExpr
    | .frame => pure ()
  let ctx := S.norm.setSimpTheorems (S.norm.simpTheorems.push extra)
  S.normCache.set (ids, some ctx)
  S.stores.set {}
  return ctx

def normGoal (S : Shared) (g : MVarId) (h? : Option FVarId := none) :
    TacticM (Option MVarId) := g.withContext do
  let ctx ← normContext S
  let some loadKeys ← Simp.getSimprocDeclKeys? ``memLoadKeys | throwError "forwardLoad"
  let some storeKeys ← Simp.getSimprocDeclKeys? ``memStoreKeys | throwError "normStores"
  let procs : Simp.Simprocs := ({} : Simp.Simprocs)
    |>.addCore loadKeys ``memLoadKeys true (.inl (forwardLoad S))
    |>.addCore storeKeys ``memStoreKeys false (.inl (normStores S))
  let (r, _) ← simpGoal g ctx (S.normProcs.push procs) (discharge? := some (discharger S))
    (simplifyTarget := h?.isNone) (fvarIdsToSimp := h?.toArray)
  let some (fvs, g') := r | return none
  let post ← g'.withContext do
    match fvs[0]? with
    | some h => `(tactic| refine_post [$(S.lemmas),*] at $(mkIdent (← h.getUserName)):ident)
    | none => `(tactic| refine_post [$(S.lemmas),*])
  match ← runOn g' (evalTactic post) with
  | [] => return none
  | g'' :: _ => return some g''

def splitValue (x : Name) : TacticM Unit := withMainContext do
  let some d := (← getLCtx).findFromUserName? x | return
  if let some fields ← dataFields? d.type then
    let ids := fields.map fun f => mkIdent f
    evalTactic (← `(tactic| rcases $(mkIdent x):ident with ⟨$[$ids],*⟩))
  else
    let ty ← whnfD d.type
    unless ty == d.type do
      replaceMainGoal [← (← getMainGoal).replaceLocalDeclDefEq d.fvarId ty]

def introAtoms (hd : FVarId) (pre : String) : TacticM (Array Name) := withMainContext do
  let parts ← conjuncts (mkFVar hd)
  let mut hyps : Array Hypothesis := #[]
  let mut words : Array Hypothesis := #[]
  let mut k := 0
  for e in parts do
    let t ← instantiateMVars (← inferType e)
    if t.isConstOf ``True then continue
    let add (hyps : Array Hypothesis) (e : Expr) (k : Nat) : MetaM (Array Hypothesis × Nat) := do
      let et ← inferType e
      let nm := Name.mkSimple s!"{pre}{k}"
      return (hyps.push { userName := nm, type := et, value := e }, k + 1)
    (hyps, k) ← add hyps e k
    if t.isAppOf ``Writable || t.isAppOf ``Readable then
      let r ← if t.isAppOf ``Writable then mkAppM ``Writable.readable #[e] else pure e
      (hyps, k) ← add hyps (← mkAppM ``Readable.low #[r]) k
    if t.isAppOf ``WordsAt then
      let nv := t.getArg! 3
      let some n := (← instantiateMVars nv).nat? | continue
      for i in [0:n] do
        let hi ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, nv])
        let v := mkApp2 e (mkNatLit i) hi
        let vt ← inferType v
        let nm := Name.mkSimple s!"word{words.size}"
        words := words.push { userName := nm, type := vt, value := v }
  let g ← getMainGoal
  let (_, g) ← g.assertHypotheses (hyps ++ words)
  let g ← g.clear hd
  replaceMainGoal [g]
  for w in words do
    let wI := mkIdent w.userName
    evalTactic (← `(tactic| try simp (config := { bitVecOfNat := false }) only [wordAddr,
      Nat.reduceDiv, Nat.reduceMul, BitVec.reduceOfNat, add_zero_lit, Lift.reduceAddOffset,
      Lift.reduceSubOffset, Fin.getElem_fin, refine_layout] at $wI:ident))
  return hyps.map (·.userName) ++ words.map (·.userName)

def substRegs (pre : String) (hyps : Array Name) : TacticM Unit := do
  for h in hyps do
    withMainContext do
      let some d := (← getLCtx).findFromUserName? h | return
      let ty ← instantiateMVars d.type
      let some (_, lhs, _) := ty.eq? | return
      let .fvar x := lhs | return
      let some xd := (← getLCtx).find? x | return
      unless xd.userName.toString.startsWith pre do return
      try
        let g ← getMainGoal
        let (_, g) ← substCore g d.fvarId (symm := false) (tryToSkip := true)
        replaceMainGoal [g]
      catch _ => pure ()
  for h in hyps do
    withMainContext do
      let some d := (← getLCtx).findFromUserName? h | return
      let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | return
      unless lhs.isAppOfArity ``Value.mk 2 && rhs.isAppOfArity ``Value.mk 2 do return
      let hI := mkIdent h
      try
        evalTactic (← `(tactic| replace $hI:ident := Value.eq_bits $hI:ident))
        evalTactic (← `(tactic| first | subst $hI:ident | skip))
      catch _ => pure ()

def closeAccess (S : Shared) (g : MVarId) : TacticM Bool := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return true
  let a := ty.getAppArgs
  if ty.isAppOfArity ``LoadOk 3 then return ← assignProof g (← loadProof? S a[0]! a[1]! a[2]!)
  if ty.isAppOfArity ``StoreOk 6 then
    return ← assignProof g (← storeProof? S a[1]! a[2]! a[3]! a[4]! a[5]!)
  return false

def closeGuard (S : Shared) (g : MVarId) : TacticM Bool := g.withContext do
  if ← closeAccess S g then return true
  let s ← saveState
  let some g' ← normGoal S g | return true
  let closed ← g'.withContext do
    if ← closeAccess S g' then return true
    if ← tryClose g' (evalTactic (← `(tactic| with_reducible assumption))) then return true
    if ← assignProof g' (← decideClosed? (← instantiateMVars (← g'.getType))) then return true
    if ← closeArith S g' then return true
    tryClose g' (evalTactic (← `(tactic| refine_ext [$(S.lemmas),*])))
  unless closed do s.restore
  return closed

def closeGuards (S : Shared) (g : MVarId) : TacticM (List MVarId) := do
  let gs ← runOn g (evalTactic (← `(tactic| repeat' refine And.intro ?_ ?_)))
  let mut left := []
  for g' in gs do
    unless ← closeGuard S g' do left := left ++ [g']
  return left

partial def matchLiterals (a b : Expr) : MetaM Bool := do
  let a ← whnfR a
  let b ← whnfR b
  if a.isAppOfArity ``Output.mk 5 && b.isAppOfArity ``Output.mk 5 then
    return ← matchLiterals (a.getArg! 2) (b.getArg! 2) <&&>
      isDefEq (a.getArg! 3) (b.getArg! 3) <&&> isDefEq a.appArg! b.appArg!
  if let some xs ← Eval.vectorElements? a then
    if let some ys ← Eval.vectorElements? b then
      unless xs.size == ys.size do return false
      for x in xs, y in ys do
        unless ← isDefEq x y do return false
      return true
  isDefEq a b

def isActivation (ty : Expr) : Bool :=
  ty.isConstOf ``Activation ||
    ty.isAppOfArity ``Prod 2 && (ty.getArg! 0).isConstOf ``Activation

partial def mvarsOf (ty : Expr) : MetaM Expr := do
  let ty' ← whnfD ty
  if (← dataFields? ty').isSome then
    let .const sn us := ty'.getAppFn | return ← mkFreshExprMVar ty
    let ctor := getStructureCtor (← getEnv) sn
    let mut q := mkAppN (mkConst ctor.name us) ty'.getAppArgs
    for _ in [0:ctor.numFields] do
      let .forallE _ d _ _ ← whnf (← inferType q) | break
      let d' ← whnfD d
      q := mkApp q (← if isActivation d' then mvarsOf d else mkFreshExprMVar d)
    return q
  mkFreshExprMVar ty

def solveFor (L : Expr) (fieldName : Name) (label? : Option Expr) (target : Expr) :
    MetaM Expr := do
  let fn ← match label? with
    | some l => mkAppM fieldName #[L, l]
    | none => mkAppM fieldName #[L]
  let some fv ← reduceLayoutField fn (if label?.isSome then some 11 else none)
    | throwError "x86_refine: cannot read the layout's {fieldName}"
  let .forallE _ pty _ _ ← whnf (← inferType fv) | throwError "x86_refine: {fieldName}"
  let p ← mvarsOf pty
  let rhs ← Meta.transform (fv.beta #[p]) (post := fun e => return .done (← whnfR e))
  unless ← matchLiterals target rhs do
    throwError "x86_refine: the UIR values do not match the layout{indentExpr target}{indentExpr rhs}"

  let p ← instantiateMVars p
  if p.isMVar && (← whnfD (← inferType p)).isConstOf ``PUnit then
    let _ ← isDefEq p (mkConst ``PUnit.unit [Level.one])
  instantiateMVars p

def closeValue (S : Shared) (g : MVarId) : TacticM Bool := do
  if ← tryClose g (evalTactic (← `(tactic| first
      | with_reducible rfl | with_reducible ac_rfl | with_reducible assumption))) then
    return true
  if ← assignProof g (← decideClosed? (← instantiateMVars (← g.getType))) then return true
  closeArith S g

def closeWordsEach (S : Shared) (g : MVarId) : TacticM Bool := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``WordsAt 5 do return false
  let args := ty.getAppArgs
  let some n := (← instantiateMVars args[3]!).nat? | return false
  if n == 0 || n > 64 then return false
  let s ← saveState
  let mut proof := mkAppN (mkConst ``WordsAt.from_end) args
  let mut words := #[]
  for k in (List.range n).reverse do
    let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit k, args[3]!])
    let f := mkAppN (mkConst ``WordsAt.from_succ) (args ++ #[mkNatLit k, hk])
    let w ← mkFreshExprSyntheticOpaqueMVar (← inferType f).bindingDomain!
    words := words.push w.mvarId!
    proof := mkApp2 f w proof
  g.assign (mkAppN (mkConst ``WordsAt.of_from) (args.push proof))
  for w in words.reverse do
    let closed ← do
      let some w ← simpShallow S.words w | pure true
      let some w ← normGoal S w | pure true
      closeValue S w
    unless closed do
      s.restore
      return false
  return true

partial def closeWords (S : Shared) (g : MVarId) (top := true) : TacticM Bool := g.withContext do
  if ← tryClose g (evalTactic (← `(tactic| with_reducible assumption))) then return true
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOf ``WordsAt do return false
  let st := ty.getArg! 0
  let vals := ty.appArg!

  let before (s : Tactic.SavedState) (g1 : MVarId) : TacticM Bool := do
    if ← closeWords S g1 (top := false) then return true
    s.restore
    if top then closeWordsEach S g else return false
  if st.isAppOfArity ``memStore 6 then

    let word ← do
      let some sw ← (evalNat (st.getArg! 4)).run | pure false
      pure ((← (evalNat (ty.getArg! 2)).run) == some sw)
    if word && vals.isAppOf ``Vector.set then
      let s ← saveState
      if let some gs ← tryRun g (evalTactic (← `(tactic|
          refine WordsAt.write_set' ?_ ?_ ?_ ?_ (by decide) (by decide) (by decide) ?_))) then

        let gs ← match gs with
          | [g1, gj, g2, g3, g4] =>
            if ← tryClose gj (evalTactic (← `(tactic| first | decide | omega))) then
              pure [g1, g2, g3, g4]
            else pure gs
          | gs => pure gs
        match gs with
        | [g1, g2, g3, g4] =>
          let g2s := (← simpShallow S.words g2).toList
          let g3s := (← normGoal S g3).toList
          if ← (g2s ++ g3s).allM (closeValue S) <&&> closeValue S g4 then return ← before s g1
          s.restore
        | _ => s.restore
    let s ← saveState
    if let some gs ← tryRun g (evalTactic (← `(tactic| refine WordsAt.write_apart ?_ _ _ ?_))) then
      match gs with
      | [g1, g2] =>
        if ← g2.withContext do assignProof g2 (← dischargeProp S (← g2.getType)) then
          return ← before s g1
        s.restore
      | _ => s.restore
  else if let some hf ← frameInto? st then
    let hfs ← Term.exprToSyntax hf.toExpr
    let s ← saveState
    if let some gs ← tryRun g (evalTactic (← `(tactic|
        refine WordsAt.of_frame ?_ $hfs (by decide) ?_))) then
      match gs with
      | [g1, g2] =>
        if ← closeValue S g2 then return ← before s g1
        s.restore
      | _ => s.restore
  closeWordsEach S g

def regionAtom? (S : Shared) (ty : Expr) : MetaM (Option Expr) := do
  let (writable, m, a, n) ←
    if ty.isAppOfArity ``Writable 4 then pure (true, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3)
    else if ty.isAppOfArity ``Readable 3 then pure (false, ty.getArg! 0, ty.getArg! 1, ty.getArg! 2)
    else return none
  let readable (r : Region) (h : Expr) : MetaM Expr :=
    if r.writable && !writable then mkAppM ``Writable.readable #[h] else pure h
  match ← partOf? S m a n writable with
  | some (.offsets r h fa hin) =>
    let lem := if writable then ``Writable.of_offsets else ``Readable.of_offsets
    return some (← mkAppM lem #[← readable r h, fa.eq, r.addr.eq, hin])
  | some (.bounds r h h₁ h₂) =>
    let lem := if writable then ``Writable.sub else ``Readable.sub
    return some (← mkAppM lem #[← readable r h, h₁, h₂])
  | none => return none

def closeAtom (S : Shared) (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  if ty.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return []
  if ← tryClose g (evalTactic (← `(tactic| with_reducible assumption))) then return []
  let some g' ← normGoal S g | return []
  let ty := (← instantiateMVars (← g'.getType)).consumeMData
  let ext : TacticM Bool := tryClose g' (evalTactic (← `(tactic| refine_ext [$(S.lemmas),*])))
  if ty.isAppOf ``Readable || ty.isAppOf ``Writable then
    return if ← (do assignProof g' (← regionAtom? S ty)) <||> ext then [] else [g']
  if ty.isAppOf ``WordsAt then
    return if ← closeWords S g' <||> ext then [] else [g']
  return if ← closeValue S g' <||> ext then [] else [g']

partial def frameProof? (S : Shared) (o m regions : Expr) : MetaM (Option Expr) := do
  if o == m then return some (← mkAppM ``RamWriteFrame.refl #[o, regions])
  for d in ← hypsWithHead ``RamWriteFrame do
    let t ← instantiateMVars d.type
    if t.getArg! 1 == m then
      if ← withReducible (isDefEq t (← mkAppM ``RamWriteFrame #[o, m, regions])) then
        return some d.toExpr
  if m.isAppOfArity ``memStore 6 then
    let some h ← frameProof? S o (m.getArg! 2) regions | return none
    let n := m.getArg! 4
    let inTy ← mkAppM ``InRegions #[regions, m.getArg! 3, ← mkAppM ``HDiv.hDiv #[n, mkNatLit 8]]
    let some hin ← cached S inTy (proveArith S inTy) | return none
    return some (← mkAppM ``RamWriteFrame.memStore #[h, m.getArg! 5, hin])
  if let some hf ← frameInto? m then
    let t ← instantiateMVars hf.type
    let some h ← frameProof? S o (t.getArg! 0) regions | return none
    let wTy ← mkAppM ``RegionsWithin #[t.getArg! 2, regions]
    let some hw ← cached S wTy (proveArith S wTy) | return none
    return some (← mkAppM ``RamWriteFrame.trans #[h, hf.toExpr, hw])
  return none

def closeFrame (S : Shared) (g : MVarId) : TacticM (List MVarId) := do
  let some g ← normGoal S g | return []
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if ty.isAppOfArity ``RamWriteFrame 3 then
      if ← assignProof g (← frameProof? S (ty.getArg! 0) (ty.getArg! 1) (ty.getArg! 2)) then
        return []
    return [g]

def closeAtomsFrame (S : Shared) (ga gf : MVarId) : TacticM (List MVarId) := do
  let mut left := []
  if let some ga ← simpShallow S.layout ga then
    for g' in ← runOn ga (evalTactic (← `(tactic| repeat' refine And.intro ?_ ?_))) do
      left := left ++ (← closeAtom S g')
  if let some gf ← simpShallow S.layout gf then
    left := left ++ (← closeFrame S gf)
  return left

def closeRel (S : Shared) (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let some (L, _, _) := layoutParts? ty | return [g]
  let u ← whnfR (ty.getArg! 13)
  unless u.isAppOfArity ``Location.mk 7 do return [g]
  let p ← solveFor L ``Layout.args (some (u.getArg! 4)) (u.getArg! 5)
  let ps ← Term.exprToSyntax p
  let gs ← runOn g (evalTactic (← `(tactic| refine ⟨rfl, ⟨$ps, rfl, rfl, ?_⟩, ?_⟩)))
  match gs with
  | [ga, gf] => closeAtomsFrame S ga gf
  | gs => return gs

def closeRet (S : Shared) (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let some (L, _, _) := layoutParts? ty | return [g]
  let r ← solveFor L ``Layout.output none (ty.getArg! 13)
  let rs ← Term.exprToSyntax r
  let gs ← runOn g (evalTactic (← `(tactic| refine ⟨?_, ⟨$rs, rfl, ?_⟩, ?_⟩)))
  match gs with
  | [gt, ga, gf] =>
    let mut left := []
    for g' in (← simpShallow S.layout gt).toList do
      left := left ++ (← closeAtom S g')
    return left ++ (← closeAtomsFrame S ga gf)
  | gs => return gs

def projReduce (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let .const fn _ := e.getAppFn | return .continue
    let some info ← getProjectionFnInfo? fn | return .continue
    if info.fromClass then return .continue
    let args := e.getAppArgs
    let some x := args[info.numParams]? | return .continue
    let x ← whnfR (← instantiateMVars x)
    unless x.isAppOf info.ctorName do return .continue
    let some f := x.getAppArgs[info.numParams + info.i]? | return .continue
    return .visit (mkAppN f (args.extract (info.numParams + 1) args.size)))

partial def inherit (x c : Expr) : MetaM Unit := do
  let x ← instantiateMVars x
  let .const cn _ := x.getAppFn | return
  let some (.ctorInfo ci) := (← getEnv).find? cn | return
  unless isStructure (← getEnv) ci.induct do return
  let fields := getStructureFields (← getEnv) ci.induct
  let args := x.getAppArgs
  let np := args.size - fields.size
  for i in [0:fields.size] do
    let y ← instantiateMVars args[np + i]!
    let cy ← mkAppM (ci.induct ++ fields[i]!) #[c]
    if y.isMVar then
      let _ ← isDefEq y cy
    else
      inherit y cy

def solveContext (L c u l : Expr) : MetaM Expr := do
  let Ctx ← inferType c
  let c' ← mvarsOf Ctx
  let u ← whnfR u
  let p ← solveFor L ``Layout.args (some (u.getArg! 4)) (u.getArg! 5)
  let l ← whnfR l
  let (args, st) := (l.getArg! 5, l.getArg! 6)
  let some elems ← Eval.vectorElements? args | throwError "x86_refine: the callee's registers"

  if let some orig ← reduceLayoutField (← mkAppM ``Layout.original #[L, c']) none then
    let _ ← isDefEq (← whnfR orig) st
  let some atoms ← reduceLayoutField (← mkAppM ``Layout.atoms #[L, u.getArg! 4, c', p]) (some 11)
    | throwError "x86_refine: the callee's atoms"
  let unassigned : MetaM Nat := return (← getMVars (← instantiateMVars c')).size
  let mut before := (← unassigned) + 1
  while (← unassigned) < before do
    before ← unassigned
    let mut a ← whnfD atoms
    repeat
      let .app (.app (.app (.const ``List.cons _) _) hd) tl := a | break
      let hd ← projReduce (← whnfR (← instantiateMVars hd))
      match_expr hd with
      | Atom.reg r v =>
        if let some k ← Eval.indexValue? r then
          if let some x := elems[k]? then
            let _ ← isDefEq v (← whnfR x)
      | Atom.low r w v =>
        if let some k ← Eval.indexValue? r then
          if let some x := elems[k]? then
            let x ← whnfR x
            if x.isAppOfArity ``Value.mk 2 then
              let _ ← isDefEq v (← mkAppM ``BitVec.setWidth #[w, x.appArg!])
      | Atom.mem addr w v =>
        if (← instantiateMVars v).getAppFn.isMVar then
          let _ ← isDefEq v (← mkAppM ``memLoad #[st, ← projReduce (← instantiateMVars addr), w])
      | _ => pure ()
      a ← whnfD tl

  inherit c' c
  instantiateMVars c'

def introReturn (S : Shared) : TacticM Unit := do
  let qs := regVars "q"
  let hf ← withMainContext (freshName "hframe")
  let (hfI, rI, hdoneI, lvalsI, lmemI, rflI) := (mkIdent hf, mkIdent `r, mkIdent `hdone,
    mkIdent `lvals, mkIdent (← withMainContext (freshName "rmem")), mkIdent `rfl)
  let htagI := mkIdent `htag
  evalTactic (← `(tactic| (
    intro uo lo hret hacc
    clear hacc
    obtain ⟨$htagI:ident, hres, $hfI:ident⟩ := hret
    obtain ⟨$rI:ident, $rflI:ident, $hdoneI:ident⟩ := hres
    obtain ⟨$lvalsI:ident, ltag, $lmemI:ident⟩ := lo
    dsimp only at $htagI:ident $hdoneI:ident $hfI:ident)))
  withMainContext do
    let hs ← [`htag, hf].mapM fun n => return (← getLocalDeclFromUserName n).fvarId
    replaceMainGoal (← simpShallow S.layout (← getMainGoal) hs.toArray).toList
  evalTactic (← `(tactic| (
    subst $htagI:ident
    revert $hdoneI:ident
    refine args_cases (fun $[$qs]* => ?_) $lvalsI:ident
    clear $lvalsI:ident
    intro $hdoneI:ident)))
  splitValue `r
  withMainContext do
    let h ← getLocalDeclFromUserName `hdone
    replaceMainGoal (← simpShallow S.layout (← getMainGoal) #[h.fvarId]).toList
  withMainContext (registerNames .frame #[hf])
  withMainContext do
    let some hd := (← getLCtx).findFromUserName? `hdone | return
    let names ← introAtoms hd.fvarId "done"
    substRegs "q" names
    withMainContext (registerNames .rewrite names)

def closeCall (S : Shared) (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let_expr Exists _ body := ty | return [g]
  let .lam _ _ b _ := body | return [g]
  let_expr And rel _ := b | return [g]
  let some (L, _, _) := layoutParts? rel | return [g]
  let resumes := b.appArg!.consumeMData
  let c ← match layoutParts? resumes with
    | some _ => pure (resumes.getArg! 13)
    | none => throwError "x86_refine: not a call goal"
  let mvc ← mkFreshExprMVar (← inferType c)
  let rel' := (rel.instantiate1 mvc)
  let u := rel'.getArg! 13
  let l := rel'.getArg! 14
  let c' ← solveContext L c u l
  let cs ← Term.exprToSyntax c'
  let gs ← runOn g (evalTactic (← `(tactic| refine ⟨$cs, ?_, ?_⟩)))
  match gs with
  | [grel, gres] =>
    let left ← closeRel S grel
    let gress ← runOn gres (evalTactic (← `(tactic| try unfold Layout.Resumes)))
    let mut out := left
    for gr in gress do
      let gs' ← runOn gr (do
        introReturn S
        evalTactic (← `(tactic| refine ⟨?_, ?_⟩)))
      match gs' with
      | [gacc, grel'] =>
        for ga in (← simpShallow S.resume gacc).toList do
          if let some ga' ← normGoal S ga then out := out ++ [ga']
        for gr' in (← simpShallow S.resume grel').toList do
          out := out ++ (← closeRel S gr')
      | gs' => out := out ++ gs'
    return out
  | gs => return gs

def closeTarget? (S : Shared) (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  g.headBetaType
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  if ty.isAppOf ``Layout.Rel then return some (← closeRel S g)
  if ty.isAppOf ``Layout.RetRel then return some (← closeRet S g)
  if ty.isAppOfArity ``Exists 2 then
    if let .lam _ _ b _ := ty.appArg! then
      if b.isAppOfArity ``And 2 && (layoutParts? b.appFn!.appArg!).isSome then
        return some (← closeCall S g)
  return none

inductive RunKind where
  | jump | call | ret

def runGoal? (ty : Expr) : Option (RunKind × Expr × Expr) :=
  let ty := ty.consumeMData
  if ty.isAppOfArity ``Ahead 4 then
    let E := ty.getArg! 2
    let l := ty.getArg! 3
    let kind := match E with
      | .lam _ _ b _ =>
        if b.isAppOf ``CallTo then RunKind.call
        else if b.isAppOf ``ReturnOf then RunKind.ret
        else RunKind.jump
      | _ => RunKind.jump
    some (kind, E, l)
  else none

def atTarget (E l : Expr) : MetaM Bool := do
  let some (L, _, _) := layoutParts? E | return false
  let u ← whnfR (E.getArg! 13)
  unless u.isAppOfArity ``Location.mk 7 do return false
  let some st ← reduceLayoutField (← mkAppM ``Layout.start #[L, u.getArg! 4]) (some 11) |
    return false
  let l ← whnfR (← instantiateMVars l)
  unless l.isAppOfArity ``Location.mk 7 do return false
  return (← whnfD st) == (← whnfD (l.getArg! 4))

def blockDefs (lifted l : Expr) : MetaM (Array Name) := do
  let l ← whnfR (← instantiateMVars l)
  unless l.isAppOfArity ``Location.mk 7 do return #[]
  let blocks ← mkAppM ``Program.blocks #[← mkAppM ``Lifted.program #[lifted], l.getArg! 4]
  let b ← withTransparency .default <| withCanUnfoldPred (fun cfg info => do
      if info.type.isAppOf ``Block then return false
      canUnfoldDefault cfg info) <| whnf blocks
  let env ← getEnv
  let isBlockDef (n : Name) : Bool := match env.find? n with
    | some (.defnInfo d) => d.type.isAppOf ``Block && !cfgBlockAttr.hasTag env n
    | _ => false
  let .const n _ := b.getAppFn | return #[]
  unless isBlockDef n do return #[]
  let mut out := #[n]
  let mut todo := #[n]
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    let some (.defnInfo d) := env.find? m | continue
    for k in d.value.getUsedConstants do
      if isBlockDef k && !out.contains k then
        out := out.push k
        todo := todo.push k
  return out

def runDepth : Nat := 16

structure Leaves where
  targets : List MVarId := []
  left : List MVarId := []

instance : Append Leaves := ⟨fun a b => ⟨a.targets ++ b.targets, a.left ++ b.left⟩⟩

def branchContradicts (S : Shared) (g : MVarId) : TacticM (Option MVarId) := g.withContext do
  let some hc := (← getLCtx).findFromUserName? `hc | return some g
  let some g ← normGoal S g hc.fvarId | return none
  let s ← saveState
  let closed ← g.withContext do
    let some hc := (← getLCtx).findFromUserName? `hc | return false
    closeArith S (← g.exfalso) #[← instantiateMVars hc.type]
  if closed then return none
  s.restore
  return some g

mutual

partial def runLifted (S : Shared) (fdefs : SimpArgs) (depth : Nat) (first : Bool) (g : MVarId) :
    TacticM Leaves := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (kind, E, l) := runGoal? ty | return { left := [g] }
  if let .jump := kind then
    if !first && (← atTarget E l) then
      let gs ← applyLemma g ``Ahead.here
      for g' in gs do g'.headBetaType
      return { targets := gs }
  if depth == 0 then return { left := [g] }
  let lem := match kind with
    | .jump => ``Ahead.of_step_jump
    | .call => ``Ahead.of_step_call
    | .ret => ``Ahead.of_step_ret
  let bdefs ← (← blockDefs (ty.consumeMData.getArg! 0) l).mapM simpArg
  let mut gs := []
  for g' in ← applyLemma g lem do
    gs := gs ++ (← runOn g' (evalTactic (← `(tactic| cfg_eval [$fdefs,*, $bdefs,*]))))
  let mut out : Leaves := {}
  for g' in gs do
    out := out ++ (← afterStep S fdefs depth g')
  return out

partial def afterStep (S : Shared) (fdefs : SimpArgs) (depth : Nat) (g : MVarId) :
    TacticM Leaves := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``Onward 5 do return { left := [g] }
  let t := ty.appArg!.consumeMData
  if t.isAppOfArity ``ite 5 then
    if (t.getArg! 4).isAppOf ``Transfer.stuck then
      match ← applyLemma g ``Onward.guard with
      | [gg, gr] =>
        let left ← closeGuards S gg
        let rest ← afterStep S fdefs depth gr
        return { rest with left := left ++ rest.left }
      | gs => return { left := gs }
    let mut out : Leaves := {}
    for g' in ← applyLemma g ``Onward.ite do
      let (_, g') ← g'.intro `hc
      if let some g'' ← branchContradicts S g' then
        out := out ++ (← afterStep S fdefs depth g'')
    return out
  if t.isAppOf ``Transfer.jump then
    let mut out : Leaves := {}
    for g' in ← applyLemma g ``Onward.jump do
      out := out ++ (← runLifted S fdefs (depth - 1) false g')
    return out

  let finish (lem₁ lem₂ : Name) : TacticM Leaves := do
    let mut out : Leaves := {}
    for g' in ← applyLemma g lem₁ do
      g'.headBetaType
      match ← observing? (applyLemma g' lem₂) with
      | some gs =>
        for g'' in gs do g''.headBetaType
        out := out ++ { targets := gs }
      | none =>
        let g'' ← if ← isDefEq (← g'.getType) (mkConst ``False) then
          g'.replaceTargetDefEq (mkConst ``False) else pure g'
        out := out ++ { left := [g''] }
    return out
  if t.isAppOf ``Transfer.call then return ← finish ``Onward.call ``CallTo.intro
  if t.isAppOf ``Transfer.returned then return ← finish ``Onward.returned ``ReturnOf.intro
  return { left := [g] }

end

def runLiftedGoal (S : Shared) (g : MVarId) : TacticM Leaves := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless (runGoal? ty).isSome do return { left := [g] }
  let fdefs ← (← constDefs (ty.consumeMData.getArg! 0)).mapM simpArg
  runLifted S fdefs runDepth true g

end Tactic

open Tactic

syntax (name := refineArith) "refine_arith" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| refine_arith $[[$ls,*]]?) => do
    let S ← Shared.new (ls.map (·.getElems) |>.getD #[])
    let g ← getMainGoal
    unless ← g.withContext (closeArith S g) do throwError "refine_arith: failed"
    replaceMainGoal []

elab "store_disch" : tactic => do
  let S ← Shared.new #[]
  let g ← getMainGoal
  let some p ← g.withContext do dischargeProp S (← g.getType)
    | throwError "store_disch: failed"
  g.assign p
  replaceMainGoal []

syntax "refine_norm" " [" Lean.Parser.Tactic.simpLemma,* "]" (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| refine_norm [$ls,*] $[at $h]?) => withMainContext do
    let S ← Shared.new ls.getElems
    let h? ← h.mapM fun h => return (← getLocalDeclFromUserName h.getId).fvarId
    replaceMainGoal (← normGoal S (← getMainGoal) h?).toList

elab "refine_intro" : tactic => do
  let rs := regVars "a"
  let (cI, pI, memI, hframeI, hatomsI, largsI) := (mkIdent `c, mkIdent `p, mkIdent `mem,
    mkIdent `hframe, mkIdent `hatoms, mkIdent `largs)
  evalTactic (← `(tactic| (
    unfold Layout.BlockSimulation
    intro $cI:ident arguments store l h)))

  withMainContext do
    let ty ← whnfD (← inferType (← getLocalDeclFromUserName `c).toExpr)
    if ty.isAppOfArity ``Prod 2 && isActivation ty then
      evalTactic (← `(tactic| obtain ⟨$(mkIdent `fr):ident, $cI:ident⟩ := $cI:ident))
  evalTactic (← `(tactic| (
    obtain ⟨hlabel, hp, $hframeI:ident⟩ := h
    dsimp only at hlabel hp
    obtain ⟨$pI:ident, hargs, hstore, $hatomsI:ident⟩ := hp
    rw [hargs, hstore]
    clear hargs hstore arguments store
    obtain ⟨llabel, $largsI:ident, $memI:ident⟩ := l
    dsimp only at hlabel $hatomsI:ident $hframeI:ident
    simp only [refine_layout] at hlabel
    subst hlabel
    revert $hatomsI:ident
    refine args_cases (fun $[$rs]* => ?_) $largsI:ident
    clear $largsI:ident
    intro $hatomsI:ident)))
  splitValue `p
  withMainContext do
    evalTactic (← `(tactic| simp only [refine_layout] at $hatomsI:ident $hframeI:ident))
  withMainContext do
    let some hd := (← getLCtx).findFromUserName? `hatoms | return
    let names ← introAtoms hd.fvarId "atom"
    substRegs "a" names
    withMainContext (registerNames .rewrite names)

syntax "refine_uir" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| refine_uir [$ls,*]) => withMainContext do
    let ty := (← instantiateMVars (← getMainTarget)).consumeMData
    let some (L, _, _) := layoutParts? ty | throwError "refine_uir: not a `Layout.MatchedBy` goal"
    let udefs ← (← constDefs (← layoutDialect L)).mapM simpArg
    let set ← simpArg ``reduceGetElemSet
    let huI := mkIdent `hu
    evalTactic (← `(tactic| (
      simp only [refine_layout]
      cfg_eval [$udefs,*, $set, $ls,*]
      try simp only [$set])))
    setGoals (← (← getGoals).mapM fun g => readVectors g)
    evalTactic (← `(tactic| (
      repeat' (refine Layout.matches_ite (fun $huI:ident => ?_) (fun $huI:ident => ?_))
      all_goals try simp only [Dialect.ofPure, $udefs,*, refine_norm, ite_eq_right_iff,
        ite_eq_left_iff, BitVec.reduceEq, imp_false, Classical.not_not, $ls,*] at $huI:ident
      all_goals first
        | exact Layout.matches_stuck
        | simp only [Layout.matches_jump, Layout.matches_call, Layout.matches_returned])))

syntax "refine_lifted" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| refine_lifted [$ls,*]) => withMainContext do
    let g ← getMainGoal
    unless (runGoal? (← instantiateMVars (← g.getType))).isSome do
      throwError "refine_lifted: not a run goal{indentExpr (← g.getType)}"
    let leaves ← runLiftedGoal (← Shared.new ls.getElems) g
    replaceMainGoal (leaves.targets ++ leaves.left)

syntax "refine_close" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| refine_close [$ls,*]) => withMainContext do
    let some left ← closeTarget? (← Shared.new ls.getElems) (← getMainGoal)
      | throwError "refine_close: not a target goal{indentExpr (← getMainTarget)}"
    replaceMainGoal left

syntax "x86_refine" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| x86_refine $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    evalTactic (← `(tactic| refine_intro))
    evalTactic (← `(tactic| refine_uir [$ls,*]))
    let S ← Shared.new ls
    let mut left := []
    for g in ← getGoals do
      let leaves ← runLiftedGoal S g
      for t in leaves.targets do
        left := left ++ ((← closeTarget? S t).getD [t])
      left := left ++ leaves.left
    setGoals left

end ChaCha20Poly1305.Proofs.Refine
