import K256.Proofs.Signing.SearchBound

namespace K256.Proofs.Signing.Drbg

open Standards.RFC Standards.RFC.DeterministicSigning Standards.NIST.SHA2
  Standards.SECG.DomainParameters Standards.SECG.ECC

def updateValue (state : Nonce.State) : Nonce.State :=
  ⟨state.key, HMAC.hmac SHA256.hashBytes 64 state.key state.value⟩

def updateRound (tag : UInt8) (seed : ByteArray) (state : Nonce.State) : Nonce.State :=
  let key := HMAC.hmac SHA256.hashBytes 64 state.key (state.value ++ ⟨#[tag]⟩ ++ seed)
  updateValue ⟨key, state.value⟩

theorem orderBits_eq : Nonce.orderBits Secp256k1.domain.n = 256 := by decide +kernel

theorem bitsToInt_eq_octetsToNat {bytes : ByteArray} (short : bytes.size ≤ 32) :
    Nonce.bitsToInt Secp256k1.domain.n bytes = Encoding.octetsToNat bytes := by
  simp [Nonce.bitsToInt, Encoding.octetsToNat, orderBits_eq,
    Nat.sub_eq_zero_of_le (show 8 * bytes.size ≤ 256 by omega)]

theorem intToOctets_eq (d : Nat) :
    Nonce.intToOctets Secp256k1.domain.n d = Encoding.natToOctets 32 d := by
  simp only [Nonce.intToOctets, orderBits_eq, Encoding.natToOctets]

theorem initialState_eq (d : Nat) (digest : ByteArray) (len : digest.size = 32) :
    let seed := Encoding.natToOctets 32 d ++
      Encoding.natToOctets 32 (Encoding.octetsToNat digest % Secp256k1.domain.n)
    Nonce.initialState SHA256.hashBytes 64 32 Secp256k1.domain.n d digest =
      updateRound 1 seed (updateRound 0 seed ⟨⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 1⟩⟩) := by
  simp only [Nonce.initialState, Nonce.bitsToOctets, bitsToInt_eq_octetsToNat (Nat.le_of_eq len),
    intToOctets_eq, updateRound, updateValue]

theorem candidate_eq (state : Nonce.State) :
    candidate state = (Encoding.octetsToNat (updateValue state).value, updateValue state) := by
  have step : candidate state =
      (Nonce.bitsToInt Secp256k1.domain.n (updateValue state).value, updateValue state) := by
    simp only [candidate, Nonce.candidate, orderBits_eq]
    simp [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, updateValue]
  rw [step, bitsToInt_eq_octetsToNat]
  exact Nat.le_of_eq (show (updateValue state).value.size = 32 from Vector.size_toArray _)

theorem retry_eq (state : Nonce.State) :
    retry state = updateRound 0 ByteArray.empty (updateValue state) := by
  simp only [retry, candidate_eq, updateRound, updateValue, ByteArray.append_empty, Nonce.reject]

end K256.Proofs.Signing.Drbg
