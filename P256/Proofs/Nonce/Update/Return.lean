import P256.Proofs.Nonce.Update.Return.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state result : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (finished : Finished initial s result)
    (execution : ∃ fuel, Advances boundary fuel initial s) :
    ∃ t, DrbgCalleeResult initial t boundary 1856 result := by
  obtain ⟨t, result, memory⟩ := Return.epilogue pre finished.toFrameState execution finished.rip
  exact ⟨t, result, by simpa only [DrbgAt, memory] using finished.drbg⟩

end P256.Proofs.Nonce.Update
