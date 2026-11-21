import P256.Proofs.Signing.Core.Initialize.Encode
import P256.Proofs.Signing.Core.Initialize.ArgumentState
import P256.Proofs.Signing.Core.Initialize.Enter
import P256.Proofs.Signing.Core.Initialize.CallPre
import P256.Proofs.Signing.Core.Initialize.Inputs
import P256.Proofs.Signing.Core.Initialize.Result
import P256.Proofs.Signing.Core.Initialize.Finish
import P256.Proofs.Nonce.Initialize

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct : InitializeContract := by
  intro bindings s boundary secret digest pre input
  obtain ⟨encodeFuel, encoded, encodeRun, encoding, encodedRip⟩ := encode_secret pre input.scalar
  obtain ⟨setupFuel, prepared, setupRun, preparedRip, preparation⟩ := arguments_entry pre encoding encodedRip
  obtain ⟨entry, enterRun, entered⟩ := enter pre preparation preparedRip
  obtain ⟨returned, result, generator⟩ := Nonce.initialize_correct (nonce_pre pre preparation entered)
    (nonce_key preparation entered) (nonce_digest pre preparation entered input.digest)
  obtain ⟨calleeFuel, calleeRun⟩ := result.execution
  obtain ⟨initialized, returnRun, initialization, initializedRip⟩ :=
    nonce_result pre preparation entered result generator
  obtain ⟨finishFuel, final, finishRun, loop, finalRip⟩ := finish pre initialization initializedRip
  exact ⟨encodeFuel+setupFuel+3+calleeFuel+1+finishFuel, final,
    ((((encodeRun.trans setupRun).trans enterRun).trans calleeRun).trans returnRun).trans finishRun,
    loop, finalRip⟩

end P256.Proofs.Signing.Core.Initialize
