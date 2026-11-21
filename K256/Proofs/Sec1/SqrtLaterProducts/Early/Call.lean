import K256.Proofs.Sec1.SqrtLaterProducts.Final.Call

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open K256.Proofs.Sec1.LIR (lifted)

def squareEntry (args : Values Value Reg.count) (mem : Ram) (sp : Word)
    (resume : LIR.Label) (ret : Word) (dstReg : Fin Reg.count) (offsets : List Word)
    (post : Values Value Reg.count → Ram → Prop)
    (next : lifted.Location) (frame : lifted.StackFrame) : Prop :=
  ∃ (regs : Values Value Reg.count) (scratch : Ram),
    next = ⟨.l1145f0, regs, memStore scratch (sp - 8) ret⟩ ∧
    frame = Wrapper.callFrame resume ret ∧
    regs[4] = ⟨64, sp - 8⟩ ∧ regs[6] = ⟨64, sp⟩ ∧ regs[7] = ⟨64, sp + 40⟩ ∧
    regs[dstReg] = ⟨64, sp + 40⟩ ∧ regs[14] = ⟨64, sp⟩ ∧
    (∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → regs[i] = args[i]) ∧
    (∀ i : Fin Reg.count, i.val ∈ Activation.entryNumbers → regs[i].width = 64) ∧
    Final.ScratchWrites mem scratch sp offsets ∧ post regs next.store

macro "early_registers" : tactic => `(tactic|
  (first
   | (intro ⟨i, hi⟩ h
      simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl)
   | (intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> subst i <;> rfl)))

open Lean Meta Elab.Tactic

elab "early_saved_word" : tactic => withMainContext do
  let shared ← Refine.Tactic.Shared.new #[]
  let regions ← Refine.Tactic.regions
  let env := {shared, inputs := #[], bases := regions.map (·.addr.base) : Sqrt.WordReads.Env}
  let some g ← Refine.Tactic.simpShallow shared.words (← getMainGoal) | replaceMainGoal []; return
  let some (_, lhs, rhs) := (← g.getType).eq? | throwError "expected a word equality"
  let project (x : Expr) : MetaM Simp.Result := do
    let y ← Sqrt.WordReads.exposeLimb x
    if y.expr.isAppOfArity ``memLoad 5 then y.mkEqTrans (← Sqrt.WordReads.read env y.expr) else pure y
  let l ← project lhs
  let r ← project rhs
  unless ← isDefEq l.expr r.expr do throwError "different saved words"
  g.assign (← mkEqTrans (← l.getProof) (← mkEqSymm (← r.getProof)))
  replaceMainGoal []

end K256.Proofs.Sec1.SqrtLaterProducts.Early
