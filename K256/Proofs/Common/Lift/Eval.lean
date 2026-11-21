import K256.Proofs.Common.Lift.Lockstep
import K256.Proofs.Common.Core.TheoremWithHoles
import K256.Proofs.Common.Lift.Lemma.Eval
import K256.Proofs.Common.CFG.Eval
import X86Proofs.Instructions.Jmp.Generated.R.Triple
import X86Proofs.Instructions.Jmp.Generated.M.Triple
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

section Ops

variable {code : CodeMap} {p : BitVec 64} {mem : Ram}

@[cfg_eval] theorem Op.eval_const (v : Value) (args : Values Value 0) :
    Op.eval code (.const v) args mem = some (v, mem) := rfl

@[cfg_eval] theorem Op.eval_pure {n : Nat} (f : Vector Value n → Value) (args : Values Value n) :
    Op.eval code (.pure f) args mem = some (f args, mem) := rfl

@[cfg_eval] theorem Op.eval_out (e : RamState → Effect) (reads : List Reg) (o : EffectPart)
    (args : Values Value reads.length) :
    Op.eval code (.out p e reads o) args mem =
      some (o.value (e (Op.state p reads args mem)) (Op.state p reads args mem), mem) := rfl

@[cfg_eval] theorem Op.eval_expect (v : Value) (args : Values Value 1) :
    Op.eval code (.expect v) args mem = if args[0] = v then some (⟨1, 0⟩, mem) else none := rfl

@[cfg_eval] theorem Op.eval_cut (args : Values Value 0) : Op.eval code (.cut p) args mem = none :=
  rfl

open Classical in

@[cfg_eval low] theorem Op.eval_exec (pre : RamState → Prop) (e : RamState → Effect) (reads : List Reg)
    (args : Values Value reads.length) :
    Op.eval code (.exec p pre e reads) args mem =
      if Guard code pre e (Op.state p reads args mem) mem then
        some (⟨1, 0⟩, (applyWrites (Op.state p reads args mem)
          (e (Op.state p reads args mem)).writes).external)
      else none := rfl

variable {e : RamState → Effect} {R : List Reg} {args : Values Value R.length}

theorem Op.eval_exec_rip (hmem : ∀ t, ∀ c ∈ (e t).components, c.isMem = false) :
    Op.eval code (.exec p (fun s => s.RIP = p) e R) args mem = some (⟨1, 0⟩, mem) := by
  simp only [Op.eval_exec, guard_rip (Op.state_RIP R args) (hmem _), ↓reduceIte,
    applyWrites_external_of_noMem _ fun w hw =>
      hmem _ _ (Effect.mem_components.mpr (.inl ⟨w, hw, rfl⟩)), Op.state_external]

theorem Op.eval_exec_load {addr : RamState → BitVec 64} {len : Nat}
    (hmem : ∀ t, ∀ c ∈ (e t).components, c.isMem = false) :
    Op.eval code (.exec p (LoadPre p addr len) e R) args mem =
      if LoadOk mem (addr (Op.state p R args mem)) len then some (⟨1, 0⟩, mem) else none := by
  rw [Op.eval_exec, applyWrites_external_of_noMem _ fun w hw =>
      hmem _ _ (Effect.mem_components.mpr (.inl ⟨w, hw, rfl⟩)), Op.state_external]
  rw [propext (guard_load_iff (Op.state_RIP R args) (Op.state_external R args) (hmem _))]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem Op.eval_exec_store {codeLen len : Nat} {addr : RamState → BitVec 64}
    (hmem : ∀ t, (e t).components.filter Component.isMem = [.mem (addr t) len]) :
    Op.eval code (.exec p (StorePre p codeLen addr len) e R) args mem =
      if StoreOk code mem (addr (Op.state p R args mem)) len p codeLen then
        some (⟨1, 0⟩, (applyWrites (Op.state p R args mem) (e (Op.state p R args mem)).writes).external)
      else none := by
  rw [Op.eval_exec, propext (guard_store_iff (Op.state_RIP R args) (Op.state_external R args)
    (hmem _))]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem Op.eval_exec_push {len : Nat} {rip v : RamState → BitVec 64} :
    Op.eval code (.exec p (PushPre p len) (pushEffect rip v) R) args mem =
      if StoreOk code mem (pushAddr (Op.state p R args mem)) 8 p len then
        some (⟨1, 0⟩, memStore mem (pushAddr (Op.state p R args mem)) (v (Op.state p R args mem)))
      else none := by
  rw [Op.eval_exec_store fun t => by simp only [pushEffect_components]; rfl,
    applyWrites_pushEffect_external, Op.state_external]

theorem Op.eval_exec_call {len : Nat} {target v : RamState → BitVec 64} :
    Op.eval code (.exec p (CallPre p len target) (pushEffect target v) R) args mem =
      if StoreOk code mem (pushAddr (Op.state p R args mem)) 8 p len ∧
          (target (Op.state p R args mem)).toNat < 2^32 then
        some (⟨1, 0⟩, memStore mem (pushAddr (Op.state p R args mem)) (v (Op.state p R args mem)))
      else none := by
  rw [Op.eval_exec, propext ((guard_and (pre := PushPre p len)
      (q := fun s => (target s).toNat < 2^32)).trans (and_congr_left' (guard_store_iff
        (Op.state_RIP R args) (Op.state_external R args)
        (by simp only [pushEffect_components]; rfl)))),
    applyWrites_pushEffect_external, Op.state_external]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem Op.eval_exec_callMem {am : AddrMode} :
    Op.eval code (.exec p (CallMemPre p am)
        (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am))) R) args mem =
      if (StoreOk code mem (pushAddr (Op.state p R args mem)) 8 p (callMemLen am) ∧
            (callMemPtr p am (Op.state p R args mem)).toNat < 2^32) ∧
          LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 (callMemLen am))) 8 then
        some (⟨1, 0⟩, memStore mem (pushAddr (Op.state p R args mem))
          (p + BitVec.ofNat 64 (callMemLen am)))
      else none := by
  rw [Op.eval_exec, propext ((guard_and (pre := CallPre p (callMemLen am) (callMemPtr p am))
      (q := fun s => MemReadable s (am.addr s (p + BitVec.ofNat 64 (callMemLen am))) 8)).trans
      (and_congr ((guard_and (pre := PushPre p (callMemLen am))
        (q := fun s => (callMemPtr p am s).toNat < 2^32)).trans (and_congr_left' (guard_store_iff
          (Op.state_RIP R args) (Op.state_external R args)
          (by simp only [pushEffect_components]; rfl))))
        (loadOk_iff (Op.state_external R args)))),
    applyWrites_pushEffect_external, Op.state_external]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem Op.eval_exec_jmpMem {len : Nat} {am : AddrMode} :
    Op.eval code (.exec p (JmpMemPre p len am) (jmpM64Effect p len am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 len)) 8 ∧
          (memLoad mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 len)) 64).toNat <
            2^32 then
        some (⟨1, 0⟩, mem)
      else none := by
  have hmem : ∀ t, ∀ c ∈ (jmpM64Effect p len am t).components, c.isMem = false := by
    simp [Component.isMem]
  rw [Op.eval_exec, applyWrites_external_of_noMem _ fun w hw =>
      hmem _ _ (Effect.mem_components.mpr (.inl ⟨w, hw, rfl⟩)), Op.state_external,
    propext ((guard_and (pre := LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8)
      (q := fun s => (jmpM64Effect p len am s).rip.toNat < 2^32)).trans
      (and_congr (guard_load_iff (Op.state_RIP R args) (Op.state_external R args) (hmem _))
        Iff.rfl))]
  simp only [jmpM64Effect, Operand.read_mem_external, Op.state_external]

@[cfg_eval ↓] theorem Op.eval_exec_goesTo {pre : RamState → Prop} {t : BitVec 64} :
    Op.eval code (.exec p (GoesTo pre e t) e R) args mem =
      if (e (Op.state p R args mem)).rip = t then Op.eval code (.exec p pre e R) args mem
      else none := by
  by_cases h : (e (Op.state p R args mem)).rip = t
  · have hg : Guard code (GoesTo pre e t) e (Op.state p R args mem) mem ↔
        Guard code pre e (Op.state p R args mem) mem :=
      ⟨fun ⟨⟨hp, _⟩, ha, hw⟩ => ⟨hp, ha, hw⟩, fun ⟨hp, ha, hw⟩ => ⟨⟨hp, h⟩, ha, hw⟩⟩
    simp only [h, ↓reduceIte, Op.eval_exec]
    by_cases hp : Guard code pre e (Op.state p R args mem) mem
    · simp only [hp, hg.mpr hp, ↓reduceIte]
    · simp only [hp, mt hg.mp hp, ↓reduceIte]
  · have hg : ¬ Guard code (GoesTo pre e t) e (Op.state p R args mem) mem := fun hg => h hg.1.2
    simp only [h, ↓reduceIte, Op.eval_exec, hg]

theorem Op.eval_exec_ret (hmem : ∀ t, ∀ c ∈ (e t).components, c.isMem = false) :
    Op.eval code (.exec p (RetPre p) e R) args mem =
      if LoadOk mem (stackPtr (Op.state p R args mem)) 8 ∧
          (memLoad mem (stackPtr (Op.state p R args mem)) 64).toNat < 2^32 then
        some (⟨1, 0⟩, mem)
      else none := by
  rw [Op.eval_exec, applyWrites_external_of_noMem _ fun w hw =>
      hmem _ _ (Effect.mem_components.mpr (.inl ⟨w, hw, rfl⟩)), Op.state_external]
  rw [propext (guard_ret_iff (Op.state_RIP R args) (Op.state_external R args) (hmem _))]
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

end Ops

@[cfg_eval] theorem dialect_truth (code : CodeMap) (v : Value) : (dialect code).truth v = v.truth :=
  rfl

@[cfg_eval] theorem dialect_accepts (code : CodeMap) (guard tag : Value) :
    (dialect code).accepts guard tag = decide (guard = tag) := rfl

attribute [cfg_eval ↓] dialect_eval
attribute [cfg_eval] cutBlock
namespace Eval

open Lean Meta

partial def readsList? (e : Expr) : MetaM (Option (Array Expr)) := do
  if let some rs := CFG.Eval.listElements? e then return some rs
  let isFlag (r : Expr) : Bool := r.isAppOfArity ``Reg.flag 1
  let operands (R F : Expr) : MetaM (Option (Array Expr)) := do
    let some rs ← readsList? R | return none
    let some fs := CFG.Eval.listElements? F | return none
    return some (rs.filter (!isFlag ·) ++ fs.map (mkApp (mkConst ``Reg.flag) ·))
  match_expr e with
  | Reg.operands R F => operands R F
  | EffectPart.reads o R F =>
    let some rs ← readsList? R | return none
    let some ops ← operands R F | return none
    if o.isAppOfArity ``EffectPart.flag 1 && rs.any isFlag then
      return some (ops.push (mkApp (mkConst ``Reg.flag) o.appArg!))
    if o.isAppOfArity ``EffectPart.flag 1 || o.isAppOfArity ``EffectPart.reg 1 ||
        o.isAppOf ``EffectPart.target then
      return some ops
    return none
  | _ => return none

def regMapArgs? (e : Expr) : MetaM (Option Expr) := do
  let_expr RegMap.args ρ n inst ← e | return none
  let some pairs := CFG.Eval.listElements? ρ | return none
  let mut map : Std.HashMap Nat Nat := {}
  for pr in pairs do
    let_expr Prod.mk _ _ i j := pr | return none
    let some i ← (evalNat i).run | return none
    let some j ← (evalNat j).run | return none
    unless map.contains i do map := map.insert i j
  let fin := mkApp (mkConst ``Fin) n
  let elems := (List.range Reg.count).toArray.map fun i =>
    mkApp3 (mkConst ``Fin.ofNat) n inst (mkNatLit (map.getD i i))
  return some (← CFG.Eval.mkVectorLiteral fin (mkNatLit Reg.count) elems)

end Eval

open Lean Meta in

dsimproc [cfg_eval] reduceOpState (Op.state _ _ _ _) := fun e => do
  let_expr Op.state p reads _ args mem ← e | return .continue
  let some rs ← Eval.readsList? reads | return .continue
  let some vs ← CFG.Eval.vectorElements? args | return .continue
  let reg := mkConst ``Reg
  let value := mkConst ``Value
  let entries ← mkListLit (mkApp2 (mkConst ``Prod [0, 0]) reg value)
    ((rs.zip vs).toList.map fun (r, v) => mkApp4 (mkConst ``Prod.mk [0, 0]) reg value r v)
  return .done (mkApp3 (mkConst ``stateOf) p entries mem)

open Lean Meta in

dsimproc [cfg_eval] reduceRegMapArgs (RegMap.args _ _) := fun e => do
  let some e' ← Eval.regMapArgs? e | return .continue
  return .done e'

attribute [cfg_eval] RegMap.args_entryMap
attribute [cfg_eval] read_stateOf_cons Reg.read_write_gpr Reg.read_write_flag Reg.read_write_df Value.get_mk_setWidth Reg.gpr.injEq Reg.flag.injEq stateOf_external stateOf_RIP Value.truth_ofBool BitVec.setWidth_eq BitVec.setWidth_setWidth_of_le eq_self_iff_true Option.getD_some Option.getD_none
attribute [cfg_eval] condOp condFlags flagsOf StatusFlags.set StatusFlags.get List.zip_cons_cons List.zip_nil_left List.zip_nil_right List.foldr_cons List.foldr_nil
attribute [cfg_eval ↓] condHolds_0 condHolds_1 condHolds_2 condHolds_3 condHolds_4 condHolds_5 condHolds_6 condHolds_7 condHolds_8 condHolds_9 condHolds_10 condHolds_11 condHolds_12 condHolds_13 condHolds_14 condHolds_15
attribute [cfg_eval] addr_base_none addr_base_d8 addr_base_d32 addr_sib_none addr_sib_d8 addr_sib_d32 addr_index_none addr_index_d8 addr_index_d32 addr_rip addr_abs_none addr_abs_some AddrMode.tail_length_base AddrMode.tail_length_sib AddrMode.tail_length_rip AddrMode.tail_length_abs Disp.bytes_length_none Disp.bytes_length_d8 Disp.bytes_length_d32 BitVec.shiftLeft_zero
attribute [cfg_eval] Nat.reduceAdd Nat.reduceSub Nat.reduceMul BitVec.reduceOfNat BitVec.reduceAdd BitVec.reduceSub BitVec.reduceMul BitVec.reduceNeg BitVec.reduceAnd BitVec.reduceOr BitVec.reduceXOr BitVec.reduceNot BitVec.reduceHShiftLeft BitVec.reduceHShiftRight BitVec.reduceSShiftRight BitVec.reduceRotateLeft BitVec.reduceRotateRight BitVec.reduceToNat add_zero_lit zero_add_lit sub_zero_lit xor_self_lit sub_self_lit and_true ite_ite_none
open Lean Meta Simp in

simproc [cfg_eval] reduceLtPow ((_ : Nat) < _ ^ _) := fun e => do
  let_expr LT.lt _ _ a b ← e | return .continue
  let_expr HPow.hPow _ _ _ _ base k ← b | return .continue
  let some n ← Nat.fromExpr? a | return .continue
  let some x ← Nat.fromExpr? base | return .continue
  let some k ← Nat.fromExpr? k | return .continue
  if n < x ^ k then
    return .done { expr := mkConst ``True, proof? := some (← mkEqTrue (← mkDecideProof e)) }
  return .done { expr := mkConst ``False, proof? := some (← mkEqFalse (← mkDecideProof (mkNot e))) }

open Lean Meta Simp in

simproc [cfg_eval] reduceEqAnd ((_ : BitVec 64) = _ ∧ _) := fun e => do
  let_expr And l q ← e | return .continue
  let_expr Eq ty a t ← l | return .continue
  if (← getBitVecValue? t).isNone then return .continue
  let body ← kabstract q a
  unless body.hasLooseBVars do return .continue
  let pf := mkApp4 (mkConst ``and_eq_subst [← getLevel ty]) ty a t (mkLambda `x .default ty body)
  return .visit { expr := mkAnd l (body.instantiate1 t), proof? := pf }

namespace Eval

open Lean Meta

def isNegative (w c : Nat) : Bool := w == 64 && c ≥ 2 ^ 64 - 2 ^ 31

def negated? (c : Expr) : MetaM (Option (Expr × Expr)) := do
  let some ⟨w, v⟩ ← getBitVecValue? c | return none
  unless isNegative w v.toNat do return none
  let ty := mkApp (mkConst ``BitVec) (mkNatLit w)
  let c' ← mkNumeral ty (2 ^ w - v.toNat)
  return some (c', mkApp2 (mkConst ``Eq.refl [1]) ty c)

def offset? (e : Expr) (add : Bool) : MetaM (Option Simp.Result) := do
  let some ⟨w, b⟩ ← getBitVecValue? e.appArg! | return none
  let inner := e.appFn!.appArg!
  let some (x, a, inAdd) := (match_expr inner with
    | HAdd.hAdd _ _ _ _ x a => some (x, a, true)
    | HSub.hSub _ _ _ _ x a => some (x, a, false)
    | _ => none) | return none
  let some ⟨w', a'⟩ ← getBitVecValue? a | return none
  if w' != w || (← getBitVecValue? x).isSome then return none
  let signed (v : Nat) (pos : Bool) : Int := if pos then v else -(v : Int)
  let sum := signed a'.toNat inAdd + signed b.toNat add
  let ty := mkApp (mkConst ``BitVec) (mkNatLit w)
  let cl ← mkNumeral ty (sum % 2 ^ w).toNat
  let lemma := match inAdd, add with
    | true, true => ``add_add_lit | false, true => ``sub_add_lit
    | true, false => ``add_sub_lit | false, false => ``sub_sub_lit
  let h := mkApp2 (mkConst ``Eq.refl [1]) ty cl
  let pf := mkAppN (mkConst lemma) #[mkNatLit w, x, inner.appArg!, e.appArg!, cl, h]
  if sum % 2 ^ w == 0 then
    let zero := mkApp2 (mkConst ``BitVec.add_zero) (mkNatLit w) x
    return some { expr := x, proof? := ← mkEqTrans pf zero }
  if sum < 0 then
    let cl' ← mkNumeral ty ((-sum) % 2 ^ w).toNat
    let neg := mkApp5 (mkConst ``add_eq_sub_of_neg_eq) (mkNatLit w) x cl cl' h
    return some { expr := ← mkAppM ``HSub.hSub #[x, cl'], proof? := ← mkEqTrans pf neg }
  return some { expr := ← mkAppM ``HAdd.hAdd #[x, cl], proof? := pf }

end Eval

open Lean Meta Simp in

simproc [cfg_eval] reduceAddOffset ((_ : BitVec _) + _) := fun e => do
  let_expr HAdd.hAdd _ _ _ _ _ _ ← e | return .continue
  let some r ← Eval.offset? e true | return .continue
  return .visit r

open Lean Meta Simp in

simproc [cfg_eval] reduceSubOffset ((_ : BitVec _) - _) := fun e => do
  let_expr HSub.hSub _ _ _ _ _ _ ← e | return .continue
  let some r ← Eval.offset? e false | return .continue
  return .visit r

open Lean Meta Simp in

simproc [cfg_eval] reduceAddNeg ((_ : BitVec _) + _) := fun e => do
  let_expr HAdd.hAdd _ _ _ _ x c ← e | return .continue
  if (← getBitVecValue? x).isSome then return .continue
  let some (c', h) ← Eval.negated? c | return .continue
  let w := (← inferType x).appArg!
  return .visit { expr := ← mkAppM ``HSub.hSub #[x, c'],
                  proof? := mkApp5 (mkConst ``add_eq_sub_of_neg_eq) w x c c' h }

open Lean Meta Simp in

simproc [cfg_eval] reduceSubNeg ((_ : BitVec _) - _) := fun e => do
  let_expr HSub.hSub _ _ _ _ x c ← e | return .continue
  if (← getBitVecValue? x).isSome then return .continue
  let some (c', h) ← Eval.negated? c | return .continue
  let w := (← inferType x).appArg!
  return .visit { expr := ← mkAppM ``HAdd.hAdd #[x, c'],
                  proof? := mkApp5 (mkConst ``sub_eq_add_of_neg_eq) w x c c' h }

syntax "lift_value" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| lift_value $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      simp only [EffectPart.value, writtenValue, Reg.ofWrite?, List.findSome?_cons,
        List.findSome?_nil, Option.getD_some, Option.getD_none, Effect.flag, StatusFlagsOutcome.get,
        StatusFlagsOutcome.ofStatusFlags, StatusFlags.get, Operand.read_reg_get,
        Operand.read_df_get, Operand.read_mxcsr_get, stackPtr_get, pushAddr, stackTop,
        ofRFLAGS_eq_regs, Operand.read_mem_external, Reg.gpr.injEq, ↓reduceIte,
        BitVec.setWidth_eq, applyWrites_mem_external, Op.state_external, $ls,*]
      rfl))

macro "lift_no_mem" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  intro t
  simp [$ls,*, Component.isMem]))

end K256.Proofs.Lift
