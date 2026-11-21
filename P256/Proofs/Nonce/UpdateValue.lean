import P256.Proofs.Nonce.UpdateValue.Entry
import P256.Proofs.Nonce.UpdateValue.Prepare
import P256.Proofs.Nonce.UpdateValue.Absorb
import P256.Proofs.Nonce.UpdateValue.Finish

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre s boundary state) :
    ∃ t, DrbgCalleeResult s t boundary 1168 (updateValue state) := by
  obtain ⟨t, entryRun, saved⟩ := entry pre
  obtain ⟨prepareFuel, u, prepareRun, prepared⟩ := prepare pre saved
  obtain ⟨absorbFuel, v, absorbRun, absorbed⟩ := absorb pre prepared
  exact finish pre ⟨7 + prepareFuel + absorbFuel, (entryRun.trans prepareRun).trans absorbRun⟩ absorbed

end P256.Proofs.Nonce.UpdateValue
