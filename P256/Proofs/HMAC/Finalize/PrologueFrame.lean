import P256.Proofs.HMAC.Finalize.Prologue
import P256.Proofs.HMAC.Finalize.FrameSupport
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem prologue_frame [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre s boundary 0x100f10 168 672) :
    ∃ t, Advances boundary 7 s t ∧ ScalarFrame.FrameState s t 0 672 328 ∧
      t.RIP = 0x100f21 ∧ AgreesExcept (Program.saveFrame s ++ [.flags]) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ := prologue pre
  have ag : AgreesExcept (Program.saveFrame s ++ [.flags]) s t := agrees.mono (by
    intro c hc
    simp only [saveComponents, pushSequenceFrame, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
      (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)
    all_goals simp [Program.saveFrame])
  refine ⟨t, run, ScalarFrame.prologue_frame (stackPre pre) (by decide) ready loaded rsp ?_ ag,
    rip, ag⟩
  exact memory

end P256.Proofs.HMAC.Finalize
