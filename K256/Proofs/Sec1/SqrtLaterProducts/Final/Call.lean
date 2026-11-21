import K256.Proofs.Sec1.Sqrt.WordReads
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Field.Multiply.Words
import K256.Proofs.Sec1.Wrapper.Entry

namespace K256.Proofs.Sec1.SqrtLaterProducts.Final

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field

def ScratchWrites (mem scratch : Ram) (sp : Word) (offsets : List Word) : Prop :=
  ∀ regions : List MemoryRegion, (∀ off ∈ offsets, InRegions regions (sp + off) 8) →
    RamWriteFrame mem scratch regions

structure CallRegs (args regs : Values Value Reg.count) (sp : Word) : Prop where
  rsp : regs[4] = ⟨64, sp - 8⟩
  rdi : regs[7] = ⟨64, sp + 40⟩
  rsi : regs[6] = ⟨64, sp⟩
  rbx : regs[3] = ⟨64, sp + 40⟩
  r14 : regs[14] = ⟨64, sp⟩
  control : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → regs[i] = args[i]
  widths : ∀ i : Fin Reg.count, i.val ∈ Activation.entryNumbers → regs[i].width = 64

def CallsSquare (args : Values Value Reg.count) (mem : Ram) (sp : Word) (ret : LIR.Label)
    (addr : Word) (offsets : List Word) (post : LIR.lifted.Location → Prop)
    (next : LIR.lifted.Location) (frame : LIR.lifted.StackFrame) : Prop :=
  ∃ (regs : Values Value Reg.count) (scratch : Ram),
    next = ⟨.l1145f0, regs, memStore scratch (sp - 8) addr⟩ ∧
    frame = Wrapper.callFrame ret addr ∧ CallRegs args regs sp ∧
    ScratchWrites mem scratch sp offsets ∧ post next

theorem callTo_of_onward {code : CodeMap} {P : LIR.lifted.Location → LIR.lifted.StackFrame → Prop}
    {l : LIR.lifted.Location}
    (h : Onward LIR.lifted code (fun _ => False) (CallTo (lifted := LIR.lifted) P) (LIR.lifted.program.runBlock (dialect code) l)) :
    CallTo (lifted := LIR.lifted) P (LIR.lifted.program.runBlock (dialect code) l) := by
  generalize he : LIR.lifted.program.runBlock (dialect code) l = t at h ⊢
  cases t with
  | jump l => exact h.choose_spec.2.elim
  | call | returned | stuck => exact h

open Lean Meta Elab.Tactic

elab "final_product_block" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.consumeMData
  unless ty.isAppOfArity ``CallTo 3 do throwError "expected CallTo, got {ty.getAppFn}"
  let run := ty.appArg!.consumeMData
  unless run.isAppOf ``Program.runBlock do throwError "expected runBlock, got {run.getAppFn}"
  let lift := mkConst ``LIR.lifted
  let ds ← (← Refine.Tactic.constDefs lift).mapM Refine.Tactic.simpArg
  let bs ← (← Refine.Tactic.blockDefs lift run.appArg!).mapM Refine.Tactic.simpArg
  let shared ← Refine.Tactic.Shared.new #[]
  let cs ← Refine.Tactic.applyLemma g ``callTo_of_onward
  let mut goals := []
  for c in cs do
    for k in ← Refine.Tactic.runOn c (evalTactic (← `(tactic| cfg_eval [$ds,*, $bs,*]))) do
      let leaves ← Refine.Tactic.afterStep shared ds 1 k
      goals := goals ++ leaves.targets ++ leaves.left
  replaceMainGoal goals

macro "final_product_registers" : tactic => `(tactic|
  (constructor
   · rfl
   · rfl
   · rfl
   · rfl
   · rfl
   · intro ⟨i, hi⟩ h
     simp only [List.mem_cons, List.not_mem_nil, or_false] at h
     rcases h with h | h | h | h <;> subst i <;> rfl
   · intro ⟨i, hi⟩ h
     simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
     rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl))

theorem inRegions_atZero {regions : List MemoryRegion} {sp : Word}
    (h : InRegions regions (sp + (0 : Word)) 8) : InRegions regions sp 8 :=
  (congrArg (fun a => InRegions regions a 8) (BitVec.add_zero sp)) ▸ h

macro "final_product_frame" : tactic => `(tactic|
  (intro regions inside
   repeat' first
     | exact RamWriteFrame.refl _ _
     | refine RamWriteFrame.memStore ?_ _ ?hinside
       case hinside =>
         first
         | exact inside _ (by decide)
         | exact inRegions_atZero (inside 0 (by decide))))

end K256.Proofs.Sec1.SqrtLaterProducts.Final
