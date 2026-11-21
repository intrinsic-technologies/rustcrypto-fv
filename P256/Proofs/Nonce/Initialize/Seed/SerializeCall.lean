import P256.Proofs.Nonce.Initialize.Seed.SerializeCall.Result
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem serialize_digest [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {value : Nat}
    (pre : Nonce.InitializePre initial boundary orderAddress)
    (reduced : Reduce.Selected initial s boundary value) :
    ∃ t, Serialized initial t boundary orderAddress value := by
  obtain ⟨a, state⟩ := serialization_setup pre reduced
  obtain ⟨entry, frame, cp, integer, effect⟩ := serialization_call pre state
  obtain ⟨t, result⟩ := Conversions.Int2Octets.correct cp integer
  exact ⟨t, serialization_result pre state frame effect result⟩

end P256.Proofs.Nonce.Initialize.Seed
