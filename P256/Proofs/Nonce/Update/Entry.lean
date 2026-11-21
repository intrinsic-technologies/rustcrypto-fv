import P256.Proofs.Nonce.Update.PrologueFrame
import P256.Proofs.Nonce.Update.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem entry [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre s boundary 0x109f30 1856 state) :
    ∃ t, Advances boundary 7 s t ∧ Saved s t state := by
  obtain ⟨t, run, frame, rip, agrees⟩ := prologue_frame pre
  refine ⟨t, run, frame, rip, agrees.read (n := 64) (r := 7) (by simp [saveFrame]),
    agrees.read (n := 64) (r := 6) (by simp [saveFrame]),
    agrees.read (n := 64) (r := 2) (by simp [saveFrame]), ?_⟩
  apply pre.stateBytes.of_frame pre.stateBounded
    (ScalarFrame.save_frame pre.callee (by decide) agrees (by simp [Component.Covers]))
  intro region member
  have h : region = Stack.region s 1856 := by simpa using member
  subst region
  exact pre.separation

end P256.Proofs.Nonce.Update
