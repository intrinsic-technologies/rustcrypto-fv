import P256.Proofs.Nonce.Update.Correctness
import P256.Proofs.Nonce.Update.Prepare
import P256.Proofs.Nonce.Update.Absorb
import P256.Proofs.Nonce.Update.Zero
import P256.Proofs.Nonce.Update.Seeded

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {state : State} {input : UpdateInput} (pre : UpdatePre s boundary state input) :
    ∃ t, DrbgCalleeResult s t boundary 1856 (updateState input.nonempty input.seed state) := by
  exact update_correct_of_stages prepare absorb zero seeded pre

end P256.Proofs.Nonce.Update
