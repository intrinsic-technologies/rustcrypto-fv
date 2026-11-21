import Sha2.Proofs.Wrapper.Finish.Pop
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Finish

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

structure Result [bindings : Bindings] (initial before final : RamState) (v : Variant := .sha256) : Prop where
  execution : ∃ fuel, UniqueExecution initial fuel final
  machine : SupportedMachine bindings final
  frame : MemoryWriteFrame initial final
    #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes]
  memory : final.external = before.external
  calleeSaved : CalleeSavedRegistersUnchanged initial final
  directionFlag : DirectionFlagUnset final

 theorem run [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (input : Preserved initial s v) (rip : s.RIP = (v.pc v.epilogueOffset)) :
    ∃ final, Result initial s final v := by
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (add_r64_imm32_effect_step (v.pc v.epilogueOffset) 0x48 0xc4 296
      (by constructor <;> decide +kernel) (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)).advances
      (supportedMachine_readyToStep input.machine)
      (programText_slice (programLoaded_codeIn input.loaded) (v.textOffset + v.epilogueOffset)
        [0x48, 0x81, 0xc4, 0x28, 1, 0, 0] (by cases v <;> decide) (by cases v <;> decide +kernel)) rip
      (boundary_ne_program (validCall_returnBoundary ctx.machine ctx.call).2.2
        (by
          cases v with
          | sha224 => exact inProgram_of_textOffset 0x63a (by decide)
          | sha256 => exact inProgram_of_textOffset 0x2246 (by decide)))
  change (addR64Imm32Effect (v.pc v.epilogueOffset) 4 296 s).Holds s a at effectA
  have stateA := input.toState.of_agrees ctx runA readyA effectA.agrees
    (by simp [WritesWithin, Component.Covers]) (by simp [Component.Covers])
  have rspA : stackPtr a = stackPtr initial - 48 := by
    have hw : stackPtr a = stackPtr s + 296 := effectA.writes
    rw [hw, input.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  obtain ⟨s1, state1, effect1⟩ := pop_saved ctx stateA
    (v.textOffset + (v.epilogueOffset + 7)) 48 3 (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide +kernel)
    (by cases v <;> decide) (by cases v <;> exact effectA.rip) rspA
  change (popR64Effect (v.pc (v.epilogueOffset + 7)) 1 3 a).Holds a s1 at effect1
  have rsp1 : stackPtr s1 = stackPtr initial - 40 := by
    have hw : stackPtr s1 = stackPtr a + 8 := effect1.writes.2
    rw [hw, rspA]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value1 : s1.regValue .rbx = initial.regValue .rbx := by
    have hw : s1.regValue .rbx = memLoad a.external (stackPtr a) 64 := effect1.writes.1
    rw [rspA] at hw
    exact hw.trans (stateA.saved.words (.rbx, 48) (by simp))
  obtain ⟨s2, state2, effect2⟩ := pop_saved ctx state1
    (v.textOffset + (v.epilogueOffset + 8)) 40 12 (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide +kernel)
    (by cases v <;> decide) (by cases v <;> exact effect1.rip) rsp1
  change (popR64Effect (v.pc (v.epilogueOffset + 8)) 2 12 s1).Holds s1 s2 at effect2
  have rsp2 : stackPtr s2 = stackPtr initial - 32 := by
    have hw : stackPtr s2 = stackPtr s1 + 8 := effect2.writes.2
    rw [hw, rsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value2 : s2.regValue .r12 = initial.regValue .r12 := by
    have hw : s2.regValue .r12 = memLoad s1.external (stackPtr s1) 64 := effect2.writes.1
    rw [rsp1] at hw
    exact hw.trans (state1.saved.words (.r12, 40) (by simp))
  obtain ⟨s3, state3, effect3⟩ := pop_saved ctx state2
    (v.textOffset + (v.epilogueOffset + 10)) 32 13 (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide +kernel)
    (by cases v <;> decide) (by cases v <;> exact effect2.rip) rsp2
  change (popR64Effect (v.pc (v.epilogueOffset + 10)) 2 13 s2).Holds s2 s3 at effect3
  have rsp3 : stackPtr s3 = stackPtr initial - 24 := by
    have hw : stackPtr s3 = stackPtr s2 + 8 := effect3.writes.2
    rw [hw, rsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value3 : s3.regValue .r13 = initial.regValue .r13 := by
    have hw : s3.regValue .r13 = memLoad s2.external (stackPtr s2) 64 := effect3.writes.1
    rw [rsp2] at hw
    exact hw.trans (state2.saved.words (.r13, 32) (by simp))
  obtain ⟨s4, state4, effect4⟩ := pop_saved ctx state3
    (v.textOffset + (v.epilogueOffset + 12)) 24 14 (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide +kernel)
    (by cases v <;> decide) (by cases v <;> exact effect3.rip) rsp3
  change (popR64Effect (v.pc (v.epilogueOffset + 12)) 2 14 s3).Holds s3 s4 at effect4
  have rsp4 : stackPtr s4 = stackPtr initial - 16 := by
    have hw : stackPtr s4 = stackPtr s3 + 8 := effect4.writes.2
    rw [hw, rsp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value4 : s4.regValue .r14 = initial.regValue .r14 := by
    have hw : s4.regValue .r14 = memLoad s3.external (stackPtr s3) 64 := effect4.writes.1
    rw [rsp3] at hw
    exact hw.trans (state3.saved.words (.r14, 24) (by simp))
  obtain ⟨s5, state5, effect5⟩ := pop_saved ctx state4
    (v.textOffset + (v.epilogueOffset + 14)) 16 15 (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide +kernel)
    (by cases v <;> decide) (by cases v <;> exact effect4.rip) rsp4
  change (popR64Effect (v.pc (v.epilogueOffset + 14)) 2 15 s4).Holds s4 s5 at effect5
  have rsp5 : stackPtr s5 = stackPtr initial - 8 := by
    have hw : stackPtr s5 = stackPtr s4 + 8 := effect5.writes.2
    rw [hw, rsp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  have value5 : s5.regValue .r15 = initial.regValue .r15 := by
    have hw : s5.regValue .r15 = memLoad s4.external (stackPtr s4) 64 := effect5.writes.1
    rw [rsp4] at hw
    exact hw.trans (state4.saved.words (.r15, 16) (by simp))
  obtain ⟨s6, state6, effect6⟩ := pop_saved ctx state5
    (v.textOffset + (v.epilogueOffset + 16)) 8 5 (by cases v <;> decide) (by cases v <;> decide) (by cases v <;> decide +kernel)
    (by cases v <;> decide) (by cases v <;> exact effect5.rip) rsp5
  change (popR64Effect (v.pc (v.epilogueOffset + 16)) 1 5 s5).Holds s5 s6 at effect6
  have rsp6 : stackPtr s6 = stackPtr initial := by
    have hw : stackPtr s6 = stackPtr s5 + 8 := effect6.writes.2
    rw [hw, rsp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_zero]
  have value6 : s6.regValue .rbp = initial.regValue .rbp := by
    have hw : s6.regValue .rbp = memLoad s5.external (stackPtr s5) 64 := effect6.writes.1
    rw [rsp5] at hw
    exact hw.trans (state5.saved.words (.rbp, 8) (by simp))
  have readable : MemReadable s6 (stackPtr s6) 8 := by
    rw [rsp6]
    simpa only [BitVec.sub_zero] using
      stack_readable ctx state6 (offset := 0) (len := 8) (by cases v <;> decide) (by cases v <;> decide)
  have top : stackTop s6 = (returnBoundary initial).rip := by
    change memLoad s6.external (stackPtr s6) 64 = _
    rw [rsp6]
    exact state6.saved.returnAddress
  obtain ⟨final, step, ready, effect⟩ := ret_effect_step (v.pc (v.epilogueOffset + 17)) s6
    (supportedMachine_readyToStep state6.machine)
    (programText_slice (programLoaded_codeIn state6.loaded) (v.textOffset + (v.epilogueOffset + 17)) [0xc3]
      (by cases v <;> decide) (by cases v <;> decide +kernel))
    ⟨⟨(by cases v <;> exact effect6.rip), readable⟩, top ▸ (validCall_returnBoundary ctx.machine ctx.call).2.1⟩
  have ret : X86Proofs.Returns (returnBoundary initial) 1 s6 final :=
    X86Proofs.Returns.of_step step (effect.rip.trans top) (by
      change stackPtr final = stackPtr initial + 8
      have hw : stackPtr final = stackPtr s6 + 8 := effect.writes
      rw [hw, rsp6])
  have finalFrame : AgreesExcept [.reg 4, .rip] s6 final := effect.agrees
  have calleeSaved : CalleeSavedRegistersUnchanged initial final := by
    intro register member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp), effect5.agrees.read (by simp), effect4.agrees.read (by simp), effect3.agrees.read (by simp), effect2.agrees.read (by simp)]
      exact value1
    · change (Operand.reg 5 : Operand 64).read final = _
      rw [finalFrame.read (by simp)]
      exact value6
    · change (Operand.reg 12 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp), effect5.agrees.read (by simp), effect4.agrees.read (by simp), effect3.agrees.read (by simp)]
      exact value2
    · change (Operand.reg 13 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp), effect5.agrees.read (by simp), effect4.agrees.read (by simp)]
      exact value3
    · change (Operand.reg 14 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp), effect5.agrees.read (by simp)]
      exact value4
    · change (Operand.reg 15 : Operand 64).read final = _
      rw [finalFrame.read (by simp), effect6.agrees.read (by simp)]
      exact value5
  obtain ⟨fuel, execution⟩ := state6.execution
  have unique := (execution.returns ret).unique_of_boundary
    (validCall_returnBoundary ctx.machine ctx.call).1
  refine ⟨final, unique, supportedMachine_of_ready_agrees state6.machine ready finalFrame,
    ?_, ?_, calleeSaved, finalFrame.directionFlagClear (by simp) state6.directionFlag⟩
  · intro address outside
    rw [finalFrame.external (by simp [Component.Covers])]
    exact state6.frame address outside
  · rw [finalFrame.external (by simp [Component.Covers]),
      effect6.agrees.external (by simp [Component.Covers]),
      effect5.agrees.external (by simp [Component.Covers]),
      effect4.agrees.external (by simp [Component.Covers]),
      effect3.agrees.external (by simp [Component.Covers]),
      effect2.agrees.external (by simp [Component.Covers]),
      effect1.agrees.external (by simp [Component.Covers]),
      effectA.agrees.external (by simp [Component.Covers])]

end Sha2.Proofs.Wrapper.Finish
