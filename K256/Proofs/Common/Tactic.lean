import K256.Proofs.Common.SignatureRun
import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Generate.LIR.Generated.Values
import K256.Proofs.Sec1.Affine.Uncompressed.ArithmeticExec.Segment
import K256.Proofs.Sec1.SqrtLaterProducts.Certificate

namespace K256.Proofs.Common.Tactic

open Lean Meta Elab.Tactic
open X86.Machine X86.UserProcess X86Proofs CFG Lift Refine

elab "slot_state" " region" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let shared ← Refine.Tactic.Shared.new #[]
  let proof ← if ty.isAppOfArity ``RamWriteFrame 3 then
      Refine.Tactic.frameProof? shared (ty.getArg! 0) (ty.getArg! 1) (ty.getArg! 2)
    else Refine.Tactic.regionAtom? shared ty
  let some p := proof | throwError "could not derive the requested memory region"
  g.assign p
  replaceMainGoal []

private theorem storeOkInBlock {code : CodeMap} {m : Ram} {a pc base : BitVec 64}
    {size len : Nat} {bytes : List UInt8} (w : Writable code m a size)
    (incl : ∀ x ∈ codeRange base bytes, x ∈ code)
    (within : (pc - base).toNat + len ≤ bytes.length) : StoreOk code m a size pc len := by
  have h := ParseSignature.storeOk_of_codeRange w incl within
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq, show base + (pc - base) = pc by bv_omega] at h

elab "slot_guard" " using " blockCode:term : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``LoadOk 3 then
    let some p ← Refine.Tactic.loadProof? (← Refine.Tactic.Shared.new #[])
        (ty.getArg! 0) (ty.getArg! 1) (ty.getArg! 2)
      | throwError "could not derive the load from a readable region"
    g.assign p
    replaceMainGoal []
  else
    evalTactic (← `(tactic| refine storeOkInBlock (by slot_state region)
      (by first | with_reducible exact $blockCode | exact fun x hx => fnCode_subset_programImage x ($blockCode x hx))
      (by decide +kernel)))

elab "lifted_inputs " h:ident : tactic => withMainContext do
  let _ ← Refine.Tactic.introAtoms (← getFVarId h) "input"

elab "segment_words " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let shared ← Refine.Tactic.Shared.new ls.getElems
  let some keys ← Simp.getSimprocDeclKeys? ``Refine.Tactic.memLoadKeys
    | throwError "missing load simplifier"
  let procs := ({} : Simp.Simprocs).addCore keys ``Refine.Tactic.memLoadKeys true
    (.inl (Refine.Tactic.forwardLoad shared))
  let (goal, _) ← simpTarget (← getMainGoal) shared.norm (shared.normProcs.push procs)
  replaceMainGoal goal.toList

elab "generate_block " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some run := target.find? (·.isAppOfArity ``Program.runBlock 9)
    | throwError "expected a generator runBlock"
  let defs ← Refine.Tactic.blockDefs (mkConst ``Generate.LIR.lifted) run.appArg!
  let lemmas := (← defs.mapM Refine.Tactic.simpArg) ++ ls.getElems
  evalTactic (← `(tactic| cfg_eval [$lemmas,*]))

syntax "arithmetic_segment" " using " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| arithmetic_segment using $incl:term [$ls,*]) =>
    `(tactic| (
      generate_block [$ls,*]
      segment_words [$ls,*]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | slot_guard using $incl | assumption)
      try rfl))

syntax "certify_product" " reads " "[" ident,* "]" " model " "[" ident,* "]" : tactic

macro_rules
  | `(tactic| certify_product reads [$hs,*] model [$defs,*]) =>
    `(tactic| (lifted_word_reads [$hs,*]; all_goals lifted_word_eq [$defs,*]))

end K256.Proofs.Common.Tactic
