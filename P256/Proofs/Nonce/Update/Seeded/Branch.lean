import P256.Proofs.Nonce.Update.Seeded.State
import P256.Proofs.Nonce.Update.Branch

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem enter [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} {secret reduced : ByteArray}
    (pre : UpdateSeededPre initial boundary state secret reduced)
    (zero : RoundZeroDone initial s state (.seeded secret reduced)) :
    ∃ t, Advances boundary 2 s t ∧
      Entered initial t (updateRound 0 (secret ++ reduced) state) := by
  obtain ⟨t, run, frame, rip, agrees⟩ := branch_after_zero pre.toDrbgCalleePre zero
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨t, run, frame, ?_, zero.drbg.copy (by intros; rw [memory]), ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pre.inputCount] using rip
  · exact (agrees.read (n := 64) (r := 3) (by simp)).trans zero.drbgPointer
  · rw [memory]; exact zero.savedPointer
  · rw [memory]; exact zero.savedValue
  · exact (agrees.read (n := 64) (r := 5) (by simp)).trans zero.descriptors
  · rw [memory]; exact zero.savedEnd

end P256.Proofs.Nonce.Update.Seeded
