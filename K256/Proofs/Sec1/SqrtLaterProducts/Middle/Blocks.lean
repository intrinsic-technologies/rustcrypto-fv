import K256.Proofs.Sec1.Sqrt.WordReads
import K256.Proofs.Sec1.Wrapper.Entry
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Field.Multiply.Words

namespace K256.Proofs.Sec1.SqrtLaterProducts.Middle

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open K256.Proofs.Sec1.LIR (lifted)
open Lean Meta Elab.Tactic

private theorem transfer_guard {g : Prop} [Decidable g]
    {t u : Transfer Value Ram LIR.Label signature Reg.count}
    (valid : g) (next : t = u) : (if g then t else .stuck) = u := by
  rw [ite_eq_left valid, next]

local elab "middle_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let some (_, run, _) := (← instantiateMVars (← goal.getType)).eq?
    | throwError "expected the lifted block transfer equation"
  let defs ← (← Refine.Tactic.blockDefs (mkConst ``lifted) run.appArg!).mapM Refine.Tactic.simpArg
  evalTactic (← `(tactic| cfg_eval [$defs,*]))
  let shared ← Refine.Tactic.Shared.new #[]
  let mut goal ← getMainGoal
  while (← goal.withContext do
      pure (((← instantiateMVars (← goal.getType)).eq?).any fun (_, lhs, _) =>
        lhs.isAppOfArity ``ite 5)) do
    let [guard, next] ← Refine.Tactic.applyLemma goal ``transfer_guard
      | throwError "expected a guarded transfer"
    let pending ← Refine.Tactic.closeGuards shared guard
    unless pending.isEmpty do throwError "could not discharge the product memory guards"
    goal := next
  replaceMainGoal [goal]
  evalTactic (← `(tactic| rfl))

local elab "middle_frame" : tactic => withMainContext do
  let g ← getMainGoal
  let left ← Refine.Tactic.closeFrame (← Refine.Tactic.Shared.new #[]) g
  replaceMainGoal left

def PreservesWords (before after : Ram) (sp : Word) (offsets : List Word) : Prop :=
  ∀ off ∈ offsets, memLoad after (sp + off) 64 = memLoad before (sp + off) 64

structure ProductRegisters (before after : Values Value Reg.count) : Prop where
  control : ∀ r : Fin Reg.count, r.val ∈ [22, 39, 50, 51] → after[r] = before[r]
  widths : ∀ r : Fin Reg.count, r.val ∈ Activation.entryNumbers → after[r].width = 64

local macro "product_registers" : tactic => `(tactic|
  (constructor
   · intro ⟨i, hi⟩ h
     simp only [List.mem_cons, List.not_mem_nil, or_false] at h
     rcases h with h | h | h | h <;> subst i <;> rfl
   · intro ⟨i, hi⟩ h
     simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
     rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> first | rfl | assumption))

local macro "product_word" : tactic => `(tactic| (refine_norm [] <;> rfl))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem stageSix {code : CodeMap} {args : Values Value Reg.count}
    {mem : Ram} {sp : Word}
    (hsp : args[4].get 64 = sp)
    (hs : Writable code mem (sp - 8) 440)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2^32)
    (hcode : sp.toNat + 432 ≤ 0x117297 ∨ 0x1176f2 + 8 ≤ sp.toNat) :
    ∃ (regs : Values Value Reg.count) (store : Ram),
      LIR.program.runBlock (dialect code) ⟨.l117297, args, mem⟩ =
        .call ⟨.l1145f0, regs, store⟩ (Wrapper.callFrame .l1176f2 0x1176f2) ∧
      regs[4] = ⟨64, sp - 8⟩ ∧
      regs[3].get 64 = sp + 40 ∧ regs[14].get 64 = sp ∧
      regs[7] = ⟨64, sp + 40⟩ ∧ regs[6] = ⟨64, sp⟩ ∧
      memLoad store (sp - 8) 64 = 0x1176f2 ∧
      RamWriteFrame mem store [⟨(sp - 8).toNat, 392⟩] ∧
      ProductRegisters args regs ∧
      memLoad store (sp + 136) 64 = memLoad store sp 64 ∧
      regs[13] = ⟨64, memLoad store (sp + 8) 64⟩ ∧
      regs[5] = ⟨64, memLoad store (sp + 16) 64⟩ ∧
      regs[15] = ⟨64, memLoad store (sp + 24) 64⟩ ∧
      regs[12] = ⟨64, memLoad store (sp + 32) 64⟩ ∧
      PreservesWords mem store sp [352, 328, 304, 336, 320, 240, 288, 312, 256, 248, 160, 176,
        208, 168, 144] := by
  have haddr : (sp - (8 : BitVec 64)).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (by change 8 ≤ sp.toNat; exact hbase)
  lifted_registers [hsp]
  subst sp
  refine ⟨?_, ?_, ?step, ?post⟩
  case step => middle_step
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · product_word
    · middle_frame
    · product_registers
    · product_word
    · apply congrArg (Value.mk 64)
      product_word
    · apply congrArg (Value.mk 64)
      product_word
    · apply congrArg (Value.mk 64)
      product_word
    · apply congrArg (Value.mk 64)
      product_word
    · intro off h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> product_word

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem stageSeven {code : CodeMap} {args : Values Value Reg.count}
    {mem : Ram} {sp : Word}
    (hsp : args[4].get 64 = sp) (hspWidth : args[4].width = 64)
    (hs : Writable code mem sp 432) (hlow : sp.toNat + 432 ≤ 2^32)
    (hcode : sp.toNat + 432 ≤ 0x117bde ∨ 0x118040 ≤ sp.toNat) :
    ∃ (regs : Values Value Reg.count) (store : Ram),
      LIR.program.runBlock (dialect code) ⟨.l117bde, args, mem⟩ =
        .jump ⟨.l118040, regs, store⟩ ∧ regs[4] = args[4] ∧
      regs[3] = ⟨64, 44⟩ ∧ regs[15].get 64 = sp ∧
      regs[14].get 64 = sp + 40 ∧
      RamWriteFrame mem store [⟨sp.toNat, 384⟩] ∧
      ProductRegisters args regs ∧
      memLoad store (sp + 120) 64 = memLoad store sp 64 ∧
      memLoad store (sp + 96) 64 = memLoad store (sp + 8) 64 ∧
      memLoad store (sp + 128) 64 = memLoad store (sp + 16) 64 ∧
      memLoad store (sp + 80) 64 = memLoad store (sp + 24) 64 ∧
      memLoad store (sp + 88) 64 = memLoad store (sp + 32) 64 ∧
      memLoad store (sp + 104) 64 = args[15].get 64 ∧
      memLoad store (sp + 112) 64 = args[12].get 64 ∧
      memLoad store (sp + 192) 64 = args[13].get 64 ∧
      memLoad store (sp + 264) 64 = args[5].get 64 ∧
      regs[5] = ⟨64, memLoad store sp 64⟩ ∧
      regs[12] = ⟨64, memLoad store (sp + 24) 64⟩ ∧
      PreservesWords mem store sp [352, 328, 304, 336, 320, 240, 288, 312, 256, 248, 160, 176,
        208, 168, 144, 136] := by
  lifted_registers [hsp]
  subst sp
  refine ⟨?_, ?_, ?step, ?post⟩
  case step => middle_step
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · middle_frame
    · product_registers
    · product_word
    · product_word
    · product_word
    · product_word
    · product_word
    · product_word
    · product_word
    · product_word
    · product_word
    · apply congrArg (Value.mk 64)
      product_word
    · apply congrArg (Value.mk 64)
      product_word
    · intro off h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> product_word

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem stageEight {code : CodeMap} {args : Values Value Reg.count}
    {mem : Ram} {sp : Word}
    (hsp : args[4].get 64 = sp) (hspWidth : args[4].width = 64)
    (hs : Writable code mem sp 432) (hlow : sp.toNat + 432 ≤ 2^32)
    (hcode : sp.toNat + 432 ≤ 0x118081 ∨ 0x1184d0 ≤ sp.toNat) :
    ∃ (regs : Values Value Reg.count) (store : Ram),
      LIR.program.runBlock (dialect code) ⟨.l118081, args, mem⟩ =
        .jump ⟨.l1184d0, regs, store⟩ ∧ regs[4] = args[4] ∧
      regs[15] = ⟨64, 88⟩ ∧ regs[14].get 64 = sp ∧
      regs[3].get 64 = sp + 40 ∧
      RamWriteFrame mem store [⟨sp.toNat, 384⟩] ∧
      ProductRegisters args regs ∧
      memLoad store (sp + 152) 64 = memLoad store sp 64 ∧
      memLoad store (sp + 184) 64 = memLoad store (sp + 8) 64 ∧
      memLoad store (sp + 200) 64 = memLoad store (sp + 24) 64 ∧
      memLoad store (sp + 232) 64 = memLoad store (sp + 32) 64 ∧
      regs[13] = ⟨64, memLoad store (sp + 8) 64⟩ ∧
      regs[5] = ⟨64, memLoad store (sp + 16) 64⟩ ∧
      regs[12] = ⟨64, memLoad store (sp + 24) 64⟩ ∧
      PreservesWords mem store sp [352, 328, 304, 336, 320, 240, 288, 312, 256, 248, 160, 176,
        208, 168, 144, 136, 192, 264, 104, 112, 120, 96, 128, 80,
        88] := by
  lifted_registers [hsp]
  subst sp
  refine ⟨?_, ?_, ?step, ?post⟩
  case step => middle_step
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · middle_frame
    · product_registers
    · product_word
    · product_word
    · product_word
    · product_word
    · apply congrArg (Value.mk 64)
      product_word
    · apply congrArg (Value.mk 64)
      product_word
    · apply congrArg (Value.mk 64)
      product_word
    · intro off h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> product_word

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem stageNine {code : CodeMap} {args : Values Value Reg.count}
    {mem : Ram} {sp : Word}
    (hsp : args[4].get 64 = sp) (hspWidth : args[4].width = 64)
    (hs : Writable code mem sp 432) (hlow : sp.toNat + 432 ≤ 2^32)
    (hcode : sp.toNat + 432 ≤ 0x118511 ∨ 0x118950 ≤ sp.toNat) :
    ∃ (regs : Values Value Reg.count) (store : Ram),
      LIR.program.runBlock (dialect code) ⟨.l118511, args, mem⟩ =
        .jump ⟨.l118950, regs, store⟩ ∧ regs[4] = args[4] ∧
      regs[15] = ⟨64, 44⟩ ∧ regs[14].get 64 = sp ∧
      regs[3].get 64 = sp + 40 ∧
      RamWriteFrame mem store [⟨sp.toNat, 384⟩] ∧
      ProductRegisters args regs ∧
      PreservesWords mem store sp [352, 328, 304, 336, 320, 240, 288, 312, 256, 248, 160, 176,
        208, 168, 144, 136, 192, 264, 104, 112, 120, 96, 128, 80,
        88] := by
  lifted_registers [hsp]
  subst sp
  refine ⟨?_, ?_, ?step, ?post⟩
  case step => middle_step
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · middle_frame
    · product_registers
    · intro off h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> product_word

end K256.Proofs.Sec1.SqrtLaterProducts.Middle
