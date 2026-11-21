import P256.Proofs.Nonce.Mathematics
import P256.Spec.Arith

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec

theorem initialState_eq_reduced (secret : Nat) {digest : ByteArray} (size : digest.size ≤ 32) :
    Standards.RFC.DeterministicSigning.Nonce.initialState Operations.hash 64 32 Operations.domain.n secret digest =
      updateState true
        (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret ++
          Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n (Arith.uint digest % Operations.domain.n))
        ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩ := by
  rw [initialState_eq_updateState]
  simp only [Standards.RFC.DeterministicSigning.Nonce.bitsToOctets, bitsToInt_eq_octetsToNat size,
    Arith.uint, Arith.decodeBigEndian]

end P256.Proofs.Nonce.Initialize.Seed
