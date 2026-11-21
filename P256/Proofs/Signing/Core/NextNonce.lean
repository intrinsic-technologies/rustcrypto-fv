import P256.Proofs.Signing.Core.NextNonce.Setup
import P256.Proofs.Signing.Core.NextNonce.Return
import P256.Proofs.Nonce.Fill

set_option autoImplicit false

namespace P256.Proofs.Signing.Core

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Machine

theorem nextNonce_correct : NextNonceContract := by
  constructor
  · intro _ s t boundary state final nonce pre input rip search
    obtain ⟨prepared, setupRun, stage, preparedRip, count, source, destination⟩ := NextNonce.setup pre input rip
    obtain ⟨called, callRun, effect, cp⟩ := NextNonce.call pre stage preparedRip count source destination
    obtain ⟨u, result⟩ := Nonce.Fill.fill_correct cp search
    obtain ⟨fuel, run⟩ := result.execution
    exact ⟨7 + 1 + fuel, u, by omega, (setupRun.trans callRun).trans run,
      result.rip.trans (callEffect_stack effect).1,
      NextNonce.fill_candidate pre stage source destination effect result search.valid.1 search.valid.2⟩
  · intro _ s t boundary state pre input rip noValid
    obtain ⟨prepared, setupRun, stage, preparedRip, count, source, destination⟩ := NextNonce.setup pre input rip
    obtain ⟨called, callRun, effect, cp⟩ := NextNonce.call pre stage preparedRip count source destination
    exact diverges_of_advances (setupRun.trans callRun) (Nonce.Fill.fill_diverges cp noValid)

end P256.Proofs.Signing.Core
