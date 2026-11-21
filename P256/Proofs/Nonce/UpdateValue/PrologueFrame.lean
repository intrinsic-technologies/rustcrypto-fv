import P256.Proofs.Nonce.UpdateValue.Prologue
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem prologue_frame [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre s boundary state) :
    ∃ t, Advances boundary 7 s t ∧ ScalarFrame.FrameState s t 64 1168 488 ∧
      t.RIP = 0x10a911 ∧ AgreesExcept (Program.saveFrame s ++ [.flags]) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ := prologue pre
  have ag : AgreesExcept (Program.saveFrame s ++ [.flags]) s t := agrees.mono (by
    intro c hc
    simp only [saveComponents, pushSequenceFrame, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
      (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)
    all_goals simp [Program.saveFrame])
  refine ⟨t, run, ScalarFrame.prologue_frame pre.callee (by decide) ready loaded rsp ?_ ag,
    rip, ag⟩
  exact memory

end P256.Proofs.Nonce.UpdateValue
