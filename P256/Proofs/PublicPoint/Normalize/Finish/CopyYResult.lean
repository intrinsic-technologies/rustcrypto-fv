import P256.Proofs.PublicPoint.Normalize.Finish.CopyY
import P256.Proofs.PublicPoint.Normalize.Finish.Memory

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem copy_y_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944) (rip : t.RIP = 0x10ea45) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 3352 1944 ∧
      (copyYEffect t).Holds t u := by
  have cp : CopyYPre t := by
    refine ⟨rip, ?_, ?_, local_byte_writable pre state (by decide), ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact stack_readable (frameOffset := 1944) pre state (by decide) (by decide)
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact local_writable pre state (by decide) (by decide)
    · intro i hi off len hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact stack_code (frameOffset := 1944) pre state (by decide) (by decide) hb
    · intro off len hb
      exact stack_code (frameOffset := 1944) pre state (by decide) (by decide) hb
  obtain ⟨fuel, u, run, ready, _, effect⟩ := copy_y_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xea45 copyYBytes
      (by decide) (by decide +kernel)) cp
  refine ⟨fuel, u, run, state.after_effect (frameOffset := 1944) pre (by decide) ready effect.agrees ?_ ?_, effect⟩
  · intro c hc a ha
    simp only [copyYEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl|rfl|rfl|rfl|rfl|rfl|rfl)|rfl
    all_goals try exact ha.elim
    all_goals exact ⟨workRegion s 3352, by simp, local_work pre state (by decide) ha⟩
  · simp [copyYEffect, Effect.components]

end P256.Proofs.PublicPoint.Normalize.Finish
