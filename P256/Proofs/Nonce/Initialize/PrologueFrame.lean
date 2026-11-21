import P256.Proofs.Nonce.Initialize.Prologue
import P256.Proofs.Program.ScalarFrame.Prologue

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem prologue_frame [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre s boundary orderAddress) :
    ∃ t, Advances boundary 7 s t ∧ ScalarFrame.FrameState s t 72 2144 280 ∧
      t.RIP = 0x1077a1 ∧ AgreesExcept (Program.saveFrame s ++ [.flags]) s t := by
  obtain ⟨t, run, ready, loaded, rip, rsp, memory, agrees⟩ := prologue pre
  have ag : AgreesExcept (Program.saveFrame s ++ [.flags]) s t := agrees.mono (by
    intro c hc
    simp only [saveComponents, pushSequenceFrame, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl) |
      (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)
    all_goals simp [Program.saveFrame])
  refine ⟨t, run, ScalarFrame.prologue_frame pre.toCalleePre (by decide) ready loaded rsp ?_ ag,
    rip, ag⟩
  exact memory

end P256.Proofs.Nonce.Initialize
