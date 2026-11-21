import P256.Proofs.Verifying.Core.Reduce.Interface
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import P256.Proofs.Projective.Add.Frame.Restore

set_option autoImplicit false


namespace P256.Proofs.Verifying.Core.Reduce


open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open P256.Proofs.Projective.Add (restore_registers restoreComponents)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def epilogueComponents : List Component := .flags :: restoreComponents

theorem epilogue_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104)
    (state : ScalarFrame.FrameState s t 32 104 88) (rip : t.RIP = 0x113248) :
    ∃ u, Advances boundary 8 t u ∧ ReadyToStep u ∧
      AgreesExcept epilogueComponents t u ∧
      u.RIP = (returnBoundary s).rip ∧ stackPtr u = (returnBoundary s).rsp ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue r = s.regValue r) := by
  obtain ⟨v, step, ready, effect⟩ :=
    (add_r64_imm8_effect_step 0x113248 0x48 0xc4 40
      (by simp [RexWPrefix]) (by decide) (by decide)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x13248
        [0x48, 0x83, 0xc4, 0x28] (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1324c (by decide)))
  change (addR64Imm8Effect 0x113248 4 40 t).Holds t v at effect
  have memory : v.external = t.external := effect.agrees.external (by simp [Component.Covers])
  have restore : ScalarFrame.FrameState s v 32 104 48 := by
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
    · have hw : stackPtr v = stackPtr t + 40 := effect.writes
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
    restore_registers pre (by decide) restore (codeOffset := 0x1324c)
      ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩ effect.rip
  refine ⟨u, step.trans run, ready', ?_, rip', rsp', regs⟩
  apply (effect.agrees.trans frame).mono
  simp [epilogueComponents, restoreComponents]

theorem epilogue [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x113120 32 32 104)
    (state : ScalarFrame.FrameState s t 32 104 88) (rip : t.RIP = 0x113248)
    (execution : ∃ fuel, Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 32 104 ∧ u.external = t.external := by
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

end P256.Proofs.Verifying.Core.Reduce
