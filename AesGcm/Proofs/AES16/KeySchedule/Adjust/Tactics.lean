import AesGcm.Proofs.AES16.KeySchedule.Adjust.Bitwise
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Lean Meta Elab Tactic
open X86 X86.Machine X86Proofs X86Proofs.Refine

elab "adjust_words_context " h:ident " at " selected:num : tactic => withMainContext do
  let source ← getFVarId h
  let ty ← whnf (← source.getType)
  let .forallE _ domain _ _ := ty | throwError "expected round-indexed words"
  let some count ← (Lean.Meta.evalNat domain.appArg!).run
    | throwError "expected fixed round count"
  let mut goal ← getMainGoal
  let mut names := #[]
  for r in [selected.getNat:selected.getNat + 1] do
    let hr ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit r, mkNatLit count])
    let round := mkApp3 (mkConst ``Fin.mk) (mkNatLit count) (mkNatLit r) hr
    for p in [:8] do
      let hp ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit p, mkNatLit 8])
      let plane := mkApp3 (mkConst ``Fin.mk) (mkNatLit 8) (mkNatLit p) hp
      let proof := mkApp2 (mkFVar source) round plane
      let name := Name.mkSimple s!"adjustWord{r}_{p}"
      let (_, next) ← goal.note name proof
      goal := next
      names := names.push name
  setGoals [goal]
  for name in names do
    let id := mkIdent name
    evalTactic (← `(tactic| simp (config := { bitVecOfNat := false }) only
      [Fin.val_mk, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at $id:ident))
  for name in names do
    withMainContext do
      let d ← getLocalDeclFromUserName name
      let ty ← instantiateMVars d.type
      let lhs := ty.getArg! 1
      let fa ← Refine.Tactic.addrOf (lhs.getArg! 3)
      let lit := Syntax.mkNumLit (toString fa.val)
      let offset ← Term.elabTerm (← `(($lit : BitVec 64))) none
      let address ← mkAppM ``HAdd.hAdd #[fa.base, offset]
      let left := mkAppN lhs.getAppFn (lhs.getAppArgs.set! 3 address)
      let goal ← getMainGoal
      replaceMainGoal [← goal.replaceLocalDeclDefEq d.fvarId (← mkEq left (ty.getArg! 2))]
  withMainContext do Refine.Tactic.registerNames .rewrite names

syntax "adjust_finish_all" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

elab_rules : tactic
  | `(tactic| adjust_finish_all [$ls,*]) => withMainContext do
    let mut names : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := ls.getElems
    for d in ← getLCtx do
      if d.userName.toString.startsWith "adjustWord" then
        let id := mkIdent d.userName
        names := names.push (← `(Lean.Parser.Tactic.simpLemma| $id:ident))
    evalTactic (← `(tactic| runtime_finish_all [$names,*]))
    evalTactic (← `(tactic| all_goals try simp only [$names,*]))

set_option hygiene false in
macro "adjust_schedule_proof " callee:ident " at " round:num : tactic => do
  let calleeSimp ← `(Lean.Parser.Tactic.simpLemma| $callee:ident)
  `(tactic| (
    runtime_context [hsp]
    simp (config := { zeta := false }) only [$calleeSimp]
    extract_lets
    adjust_words_context hwords at $round
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
    repeat' apply And.intro
    adjust_finish_all [hsp, adjust_add_self, adjust_deltaSwap_machine,
      adjustDelta32_1320, adjustDelta32_2310, adjustDelta32_3030, adjustDelta32_5050,
      adjustKey, adjustRows, Machine.KeySchedule.roundPhase, Standards.NIST.AES.Variant.Nr,
      Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
      Nat.reduceEqDiff, ↓reduceIte, Fixslice16.subBytesNots,
      AES16.shiftRows1, AES16.shiftRowsWord1, AES16.shiftRows2, AES16.shiftRowsWord2,
      AES16.shiftRows3, AES16.shiftRowsWord3, true_or, false_or, or_true, or_false]
    all_goals rfl
  ))

end AesGcm.Proofs.Machine.AES16.KeySchedule
