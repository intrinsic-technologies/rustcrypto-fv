import P256.Proofs.Nonce.Model

set_option autoImplicit false

namespace P256.Proofs.Nonce

theorem initialState_eq_updateState (secret : Nat) (digest : ByteArray) :
    Standards.RFC.DeterministicSigning.Nonce.initialState P256.Spec.Operations.hash 64 32 P256.Spec.Operations.domain.n secret digest =
      updateState true
        (Standards.RFC.DeterministicSigning.Nonce.intToOctets P256.Spec.Operations.domain.n secret ++
          Standards.RFC.DeterministicSigning.Nonce.bitsToOctets P256.Spec.Operations.domain.n digest)
        ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩ := by
  rfl

theorem orderBits_eq :
    Standards.RFC.DeterministicSigning.Nonce.orderBits P256.Spec.Operations.domain.n = 256 := by
  decide +kernel

theorem bitsToInt_eq_octetsToNat {input : ByteArray} (h : input.size ≤ 32) :
    Standards.RFC.DeterministicSigning.Nonce.bitsToInt P256.Spec.Operations.domain.n input =
      Standards.SECG.ECC.Encoding.octetsToNat input := by
  simp [Standards.RFC.DeterministicSigning.Nonce.bitsToInt,
    Standards.SECG.ECC.Encoding.octetsToNat, orderBits_eq,
    Nat.sub_eq_zero_of_le (show 8 * input.size ≤ 256 by omega)]

theorem intToOctets_eq (value : Nat) :
    Standards.RFC.DeterministicSigning.Nonce.intToOctets P256.Spec.Operations.domain.n value =
      Standards.SECG.ECC.Encoding.natToOctets 32 value := by
  simp only [Standards.RFC.DeterministicSigning.Nonce.intToOctets, orderBits_eq,
    Standards.SECG.ECC.Encoding.natToOctets]

end P256.Proofs.Nonce
