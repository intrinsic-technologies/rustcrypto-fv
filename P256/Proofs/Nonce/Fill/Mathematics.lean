import P256.Proofs.Nonce.Mathematics
import P256.Proofs.Signing.Search
import P256.Proofs.SecretKeyFromBytes.Encoding

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill

open P256.Spec

theorem nextCandidate_eq (state : State) :
    Signing.Search.nextCandidate state =
      (Standards.SECG.ECC.Encoding.octetsToNat (updateValue state).value, updateValue state) := by
  have candidate : Signing.Search.nextCandidate state =
      (Standards.RFC.DeterministicSigning.Nonce.bitsToInt Operations.domain.n
        (updateValue state).value, updateValue state) := by
    simp only [Signing.Search.nextCandidate, Standards.RFC.DeterministicSigning.Nonce.candidate,
      orderBits_eq]
    simp [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, updateValue]
  rw [candidate, bitsToInt_eq_octetsToNat]
  exact Nat.le_of_eq (HMAC.hmac_size state.key state.value)

theorem nextCandidate_octets (state : State) :
    Standards.SECG.ECC.Encoding.natToOctets 32 (Signing.Search.nextCandidate state).1 =
      (updateValue state).value := by
  simp only [nextCandidate_eq]
  have result := SecretKeyFromBytes.Encoding.natToOctets_octetsToNat (updateValue state).value
  have size : (updateValue state).value.size = 32 := HMAC.hmac_size state.key state.value
  rw [size] at result
  exact result

theorem nextState_eq (state : State) :
    Signing.Search.nextState state = updateState false ByteArray.empty (updateValue state) := by
  simp only [Signing.Search.nextState, nextCandidate_eq, updateState, Bool.false_eq_true,
    ↓reduceIte, updateRound, ByteArray.append_empty, updateValue,
    Standards.RFC.DeterministicSigning.Nonce.reject]

end P256.Proofs.Nonce.Fill
