import P256.Proofs.Signing.Core.Loop
import P256.Proofs.Signing.Mathematics

set_option autoImplicit false

namespace P256.Proofs.Signing

open P256.Proofs.Common.Machine

theorem core_correct_of_contracts (initializeCorrect : Core.InitializeContract)
    (nextNonce : Core.NextNonceContract) (iteration : Core.IterationContract) : CoreContract := by
  intro bindings s boundary secret digest pre input
  obtain ⟨fuel, t, run, loop, rip⟩ := initializeCorrect pre input
  constructor
  · intro attempts signature signed
    have success : Search.signingAttempts secret digest attempts
        (Core.initialState secret digest) = some signature := by
      simpa only [rfc6979Within_empty, Search.signingAttempts, Core.initialState,
        P256.Spec.Ecdsa.order] using signed
    exact Core.loop_correct nextNonce iteration pre input loop rip ⟨fuel, run⟩ success
  · intro exhausted
    have noSuccess : ∀ attempts, Search.signingAttempts secret digest attempts
        (Core.initialState secret digest) = none := by
      intro attempts
      simpa only [rfc6979Within_empty, Search.signingAttempts, Core.initialState,
        P256.Spec.Ecdsa.order] using exhausted attempts
    exact diverges_of_advances run
      (Core.loop_diverges nextNonce iteration pre input loop rip ⟨fuel, run⟩ noSuccess)

end P256.Proofs.Signing
