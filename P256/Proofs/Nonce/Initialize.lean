import P256.Proofs.Nonce.Initialize.Reduce
import P256.Proofs.Nonce.Initialize.Seed.SerializeCall
import P256.Proofs.Nonce.Initialize.Seed.Call
import P256.Proofs.Nonce.Initialize.Seed.Mathematics
import P256.Proofs.Nonce.Initialize.Finish
import P256.Proofs.Nonce.Update

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem initialize_correct [Bindings]
    {initial : RamState} {boundary : ReturnBoundary} {orderAddress : BitVec 64}
    {secret : Nat} {digest : ByteArray}
    (pre : InitializePre initial boundary orderAddress)
    (key : (registerRegion initial .rsi 32).HasBytes initial.external
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret))
    (hash : (registerRegion initial .rcx 32).HasBytes initial.external digest) :
    ∃ t, CalleeResult initial t boundary 72 2144 ∧
      GeneratorAt t (initial.regValue .rdi) orderAddress
        (Standards.RFC.DeterministicSigning.Nonce.initialState
          Operations.hash 64 32 Operations.domain.n secret digest) := by
  obtain ⟨s, reduced⟩ := Initialize.reduce_correct pre hash
  obtain ⟨t, serialized⟩ := Initialize.Seed.serialize_digest pre reduced
  obtain ⟨u, prepared⟩ := Initialize.Seed.prepare_update pre serialized
  obtain ⟨entry, run, ready, effect, cp⟩ := Initialize.Seed.update_call pre prepared key
  obtain ⟨v, result⟩ := Update.correct (input := .seeded
    (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret)
    (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n
      (Arith.uint digest % Operations.domain.n))) cp
  have seeded := Initialize.Seed.update_result pre prepared run ready effect result
  rw [Initialize.Seed.initialState_eq_reduced secret (by have size : digest.size = 32 := hash.1; omega)]
  exact Initialize.finish pre seeded.stage seeded.rip seeded.order seeded.output seeded.drbg

end P256.Proofs.Nonce
