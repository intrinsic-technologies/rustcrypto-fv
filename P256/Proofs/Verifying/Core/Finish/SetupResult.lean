import P256.Proofs.Verifying.Core.Finish.Setup
import P256.Proofs.Verifying.Core.Finish.Memory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem copy_setup_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10d570 72 24 9992)
    (state : FrameState s t 24 9992 1176) (rip : t.RIP = 0x10df8c) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 24 9992 1176 ∧
      (copySetupEffect t).Holds t u := by
  obtain ⟨fuel,u,run,ready,_,effect⟩ := copy_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xdf8c copySetupBytes
      (by decide) (by decide +kernel)) rip
  refine ⟨fuel,u,run,state.after_registers ready effect.agrees ?_ ?_,effect⟩
  · simp [copySetupEffect,Effect.components,Component.Covers]
  · simp [copySetupEffect,Effect.components]

theorem constant_setup_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10d570 72 24 9992)
    (state : FrameState s t 24 9992 1176) (rip : t.RIP = 0x10dfa2) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 24 9992 1176 ∧
      (constantSetupEffect t).Holds t u := by
  have cp : ConstantSetupPre t := ⟨rip, local_byte_writable pre state (by decide),
    fun off len hb => stack_code (frameOffset := 1176) pre state (by decide) (by decide) hb⟩
  obtain ⟨fuel,u,run,ready,_,effect⟩ := constant_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xdfa2 constantSetupBytes
      (by decide) (by decide +kernel)) cp
  refine ⟨fuel,u,run,state.after_effect (frameOffset := 1176) pre (by decide) ready effect.agrees ?_ ?_,effect⟩
  · intro c hc a ha
    simp only [constantSetupEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl|rfl|rfl|rfl|rfl)|rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s 9992, by simp, local_work pre state (by decide) ha⟩
  · simp [constantSetupEffect,Effect.components]

end P256.Proofs.Verifying.Core.Finish
