import P256.Proofs.Nonce.UpdateValue.Finish.Arguments
import P256.Proofs.Nonce.UpdateValue.Finish.Return
import P256.Proofs.Nonce.UpdateValue.Finish.Store
import P256.Proofs.Nonce.UpdateValue.Return
import P256.Proofs.HMAC.Finalize

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : UpdateValuePre initial boundary state)
    (execution : ∃ fuel, Advances boundary fuel initial s)
    (absorbed : Absorbed initial s state) :
    ∃ t, DrbgCalleeResult initial t boundary 1168 (updateValue state) := by
  obtain ⟨setupFuel, ready, setupRun, readyState⟩ := Finish.arguments pre absorbed
  obtain ⟨called, callRun, callState⟩ := Finish.call pre readyState
  obtain ⟨finalized, result⟩ := HMAC.hmac_finalize_correct callState.pre
  have finalizedState := Finish.finalized pre callState result
  obtain ⟨storeFuel, stored, storeRun, frame, rip, drbg⟩ := Finish.store pre finalizedState
  obtain ⟨initialFuel, initialRun⟩ := execution
  obtain ⟨hashFuel, hashRun⟩ := result.execution
  obtain ⟨t, returned, memory⟩ := Return.epilogue pre frame rip
    ⟨initialFuel + setupFuel + 1 + hashFuel + storeFuel,
      (((initialRun.trans setupRun).trans callRun).trans hashRun).trans storeRun⟩
  exact ⟨t, returned, by simpa only [DrbgAt, memory] using drbg⟩

end P256.Proofs.Nonce.UpdateValue
