import P256.Proofs.Sec1.Decompress.State
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import P256.Proofs.Projective.Add.Frame.Restore

set_option autoImplicit false


namespace P256.Proofs.Sec1.Decompress


open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open P256.Proofs.Projective.Add (restore_registers restoreComponents)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def epilogueComponents : List Component := .flags :: restoreComponents

theorem epilogue_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592)
    (state : FrameState s t 80 2592 408) (rip : t.RIP = 0x1100bc) :
    ∃ u, Advances boundary 8 t u ∧ ReadyToStep u ∧
      AgreesExcept epilogueComponents t u ∧
      u.RIP = (returnBoundary s).rip ∧ stackPtr u = (returnBoundary s).rsp ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue r = s.regValue r) := by
  obtain ⟨v, step, ready, effect⟩ :=
    (add_r64_imm32_effect_step 0x1100bc 0x48 0xc4 360
      (by constructor <;> decide) (by decide) (by decide)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x100bc
        [0x48, 0x81, 0xc4, 0x68, 0x01, 0, 0] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x100c3 (by decide)))
  change (addR64Imm32Effect 0x1100bc 4 360 t).Holds t v at effect
  have memory : v.external = t.external := effect.agrees.external (by simp [Component.Covers])
  have restore : FrameState s v 80 2592 48 := by
    refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees,
      supportedMachine_of_ready_agrees state.machine ready effect.agrees, ?_,
      effect.agrees.directionFlagClear (by component_not_mem) state.directionFlag,
      fun a ha => effect.agrees.grow a (state.allocated a ha), ?_, ?_, ?_, ?_,
      (effect.agrees.mxcsr (by component_not_mem)).trans state.mxcsr,
      (effect.agrees.fcw (by component_not_mem)).trans state.fp87⟩
    · intro a b hb
      rw [memory]
      exact state.loaded a b hb
    · intro a ha
      rw [memory]
      exact state.frame a ha
    · have hw : stackPtr v = stackPtr t + 360 := effect.writes
      rw [hw, state.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    · intro item hi
      rw [memory]
      exact state.saved item hi
    · change memLoad v.external (stackPtr s) 64 = _
      rw [memory]
      exact state.returnAddress
  obtain ⟨u, run, ready', frame, rip', rsp', regs⟩ :=
    restore_registers pre (by decide) restore (codeOffset := 0x100c3)
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩ effect.rip
  refine ⟨u, step.trans run, ready', ?_, rip', rsp', regs⟩
  apply (effect.agrees.trans frame).mono
  simp [epilogueComponents, restoreComponents]

theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592)
    (state : FrameState s t 80 2592 408) (rip : t.RIP = 0x1100bc)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 80 2592 ∧ u.external = t.external := by
  obtain ⟨u, run, ready, frame, rip', rsp', regs⟩ := epilogue_correct pre state rip
  have memory : u.external = t.external :=
    frame.external (by simp [epilogueComponents, restoreComponents, Component.Covers])
  refine ⟨u, ⟨?_, rip', rsp',
    bindingsSupported_of_ready_agrees state.bindingsSupported ready frame,
    supportedMachine_of_ready_agrees state.machine ready frame,
    regs, frame.directionFlagClear (by component_not_mem) state.directionFlag,
    (frame.mxcsr (by component_not_mem)).trans state.mxcsr,
    (frame.fcw (by component_not_mem)).trans state.fp87,
    ?_, ?_, fun a ha => frame.grow a (state.allocated a ha)⟩, memory⟩
  · obtain ⟨fuel, execution⟩ := execution
    exact ⟨fuel + 8, execution.trans run⟩
  · intro a ha
    rw [memory]
    exact state.frame a ha
  · intro a b hb
    rw [memory]
    exact state.loaded a b hb

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592)
    (state : Frame s t) (rip : t.RIP = 0x1100b9)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 80 2592 ∧ u.external = t.external := by
  obtain ⟨v, run, ready, effect⟩ :=
    (mov_r64_r64_effect_step 0x1100b9 0x48 0xd8 (by simp [RexWPrefix]) rfl).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x100b9
        [0x48, 0x89, 0xd8] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x100bc (by decide)))
  change (movR64R64Effect 0x1100b9 0 3 t).Holds t v at effect
  have frame := state.after_registers ready effect.agrees (by simp [Component.Covers]) (by simp)
  obtain ⟨u, result, memory⟩ := epilogue pre frame effect.rip (by
    obtain ⟨fuel, before⟩ := execution
    exact ⟨fuel + 1, before.trans run⟩)
  exact ⟨u, result, memory.trans (effect.agrees.external (by simp [Component.Covers]))⟩

end P256.Proofs.Sec1.Decompress
