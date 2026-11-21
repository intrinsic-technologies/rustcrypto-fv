import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination.State

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.LinearCombination
open K256.Proofs.Sec1.Affine.Uncompressed

theorem adcLow (c : Bool) (a b : BitVec 64) :
    (adcSpec c a b).1 = a + b + BitVec.ofNat 64 c.toNat := rfl

theorem cmpZero (a : BitVec 64) : (cmpSpec a 0).ZF = decide (a = 0) := by
  simp [cmpSpec, subSpec, beq_zero_eq_decide]

open Lean Meta Elab Tactic in
elab "linear_post " "[" hs:ident,* "]" " model " "[" ds:ident,* "]" : tactic => do
  let ls ← hs.getElems.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  let context ← mkSimpContext (← `(tactic| simp -failIfUnchanged only [↓arithmeticRead, cfg_eval,
    rightProductSign, negateOperand, selectMagnitude, BitVec.add_zero, $ls,*])) (eraseLocal := false)
  let shared ← K256.Proofs.Refine.Tactic.Shared.new #[]
  let some keys ← Simp.getSimprocDeclKeys? ``K256.Proofs.Refine.Tactic.memLoadKeys
    | throwError "missing memory load simproc"
  let procs := ({} : Simp.Simprocs).addCore keys ``K256.Proofs.Refine.Tactic.memLoadKeys
    true (.inl (K256.Proofs.Refine.Tactic.forwardLoad shared))
  let mut remain := []
  for g in ← getGoals do
    let (r, _) ← g.withContext (simpGoal g context.ctx (context.simprocs.push procs)
      (discharge? := some (K256.Proofs.Refine.Tactic.discharger shared)))
    if let some (_, next) := r then remain := remain ++ [next]
  setGoals remain
  let defs ← ds.getElems.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  evalTactic (← `(tactic| all_goals first | with_reducible rfl | lifted_word_eq [$ds,*] |
    (simp -failIfUnchanged only [$defs,*, mulResult_fst, add_zero_lit, BitVec.add_zero, BitVec.zero_add, adcLow, addSpec_low, cmpZero, BitVec.zero_sub, low_byte, byte_extend, widen_low,
      setWidth_mergeGPR8, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq, BitVec.reduceSetWidth,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)] <;> rfl) | rfl))


abbrev Cut (n : Nat) := Registers → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    Inputs → Values Value n → Ram → Prop

def Segment {k k' : Nat} (block : Block Op Label signature Reg.count k)
    (tail : Block Op Label signature Reg.count k') (before : Cut k) (after : Cut k') : Prop :=
  ∀ {a : Registers} {sp dst ret left right : BitVec 64} {p : Inputs} {b : Values Value k}
    {m original : Ram} {x y : Int},
    CalleeFrame a original sp dst ret 112 41 →
    SignedSource original sp dst left 112 41 x → SignedSource original sp dst right 112 41 y →
    RamWriteFrame original m [⟨(sp - 112).toNat, 112⟩, ⟨dst.toNat, 41⟩] →
    before a sp dst ret left right p b m →
    ∃ c n, block.eval (dialect Extracted.programImage) b m =
      tail.eval (dialect Extracted.programImage) c n ∧
      RamWriteFrame original n [⟨(sp - 112).toNat, 112⟩, ⟨dst.toNat, 41⟩] ∧
      after a sp dst ret left right p c n

open Lean Meta Elab Tactic in
elab "linear_segment " "model " "[" ds:ident,* "]" : tactic => withMainContext do
  let state := mkIdent `state
  evalTactic (← `(tactic| intro a sp dst ret left right p b m original x y fr lsrc rsrc frame $state))
  evalTactic (← `(tactic| obtain ⟨_, _, _, _, depth, _, retSlot, _, low, stack, dest, apart⟩ := fr))
  evalTactic (← `(tactic| obtain ⟨leftRead, la, ld, _⟩ := lsrc))
  evalTactic (← `(tactic| obtain ⟨rightRead, ra, rd, _⟩ := rsrc))
  evalTactic (← `(tactic| have splow := retSlot.low))
  evalTactic (← `(tactic| have dstlow := dest.readable.low))
  evalTactic (← `(tactic| have leftlow := leftRead.low))
  evalTactic (← `(tactic| have rightlow := rightRead.low))
  let mut hs : Array Ident := #[]
  let unpack (h : Ident) : TacticM (Array Ident) := withMainContext do
    let decl ← getLocalDeclFromUserName h.getId
    let ty ← instantiateMVars decl.type
    let fields := getStructureFields (← getEnv) ty.getAppFn.constName!
    let args := fields.map fun f => mkIdent f
    evalTactic (← `(tactic| obtain ⟨$args,*⟩ := $h))
    return args
  for field in ← unpack state do
    if field.getId == `toControls || field.getId == `toSaved then
      hs := hs ++ (← unpack field)
    else hs := hs.push field
  let ls ← hs.mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:ident)
  evalTactic (← `(tactic| refine ⟨?_, ?_, ?ev, ?frameOut, ?post⟩))
  evalTactic (← `(tactic| case ev =>
    arithmetic_prefix [BitVec.add_zero, $ls,*]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1084e0)
    try refine Eq.trans (ite_eq_left (And.intro (by slot_guard using code_l1084e0)
      (by refine_norm [$ls,*, low]))) ?_
    rfl))
  evalTactic (← `(tactic| case frameOut => slot_state region))
  evalTactic (← `(tactic| case post =>
    constructor
    all_goals first | apply Controls.mk | apply Saved.mk | skip
    linear_post [$hs,*] model [$ds,*]))

end K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
