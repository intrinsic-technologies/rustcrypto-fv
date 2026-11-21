import P256.Spec.Ecdsa

set_option autoImplicit false

namespace P256.Proofs.Signing

open Standards.RFC.DeterministicSigning
open P256.Spec

theorem additionalData_initialState_empty (hash : ByteArray → ByteArray)
    (blockBytes digestBytes order secret : Nat) (digest : ByteArray) :
    AdditionalData.initialState hash blockBytes digestBytes order secret digest .empty =
      Nonce.initialState hash blockBytes digestBytes order secret digest := by
  simp only [AdditionalData.initialState, ByteArray.append_empty]
  rfl

theorem rfc6979Within_empty (attempts secret : Nat) (digest : ByteArray) :
    Ecdsa.rfc6979Within attempts secret digest .empty =
      Standards.RFC.DeterministicSigning.Signing.signingAttempts
        Operations.hash Operations.hashBlockBytes Operations.hashDigestBytes Ecdsa.order
        (fun nonce => Ecdsa.signWithNonce secret nonce digest) attempts
        (Nonce.initialState Operations.hash Operations.hashBlockBytes Operations.hashDigestBytes
          Ecdsa.order secret digest) := by
  simp only [Ecdsa.rfc6979Within, AdditionalData.signWithin, additionalData_initialState_empty]

theorem signingAttempts_add {Signature : Type} (hash : ByteArray → ByteArray)
    (blockBytes digestBytes order : Nat) (sign : Nat → Option Signature)
    {attempts : Nat} {state : Nonce.State} {signature : Signature}
    (found : Standards.RFC.DeterministicSigning.Signing.signingAttempts
      hash blockBytes digestBytes order sign attempts state = some signature) (extra : Nat) :
    Standards.RFC.DeterministicSigning.Signing.signingAttempts
      hash blockBytes digestBytes order sign (attempts + extra) state = some signature := by
  induction attempts generalizing state with
  | zero => simp [Standards.RFC.DeterministicSigning.Signing.signingAttempts] at found
  | succ attempts ih =>
    rw [Nat.succ_add, Standards.RFC.DeterministicSigning.Signing.signingAttempts]
    rw [Standards.RFC.DeterministicSigning.Signing.signingAttempts] at found
    generalize hc : Nonce.candidate hash blockBytes digestBytes order state = candidate at found ⊢
    rcases candidate with ⟨nonce, next⟩
    dsimp only at found ⊢
    cases hs : (if (decide (0 < nonce) && decide (nonce < order)) = true
        then sign nonce else none) with
    | none =>
      simp only [hs] at found ⊢
      exact ih found
    | some result => simpa only [hs] using found

theorem signingAttempts_unique {Signature : Type} (hash : ByteArray → ByteArray)
    (blockBytes digestBytes order : Nat) (sign : Nat → Option Signature)
    {first second : Nat} {state : Nonce.State} {a b : Signature}
    (ha : Standards.RFC.DeterministicSigning.Signing.signingAttempts
      hash blockBytes digestBytes order sign first state = some a)
    (hb : Standards.RFC.DeterministicSigning.Signing.signingAttempts
      hash blockBytes digestBytes order sign second state = some b) : a = b := by
  have left := signingAttempts_add hash blockBytes digestBytes order sign ha second
  have right := signingAttempts_add hash blockBytes digestBytes order sign hb first
  rw [Nat.add_comm second first] at right
  exact Option.some.inj (left.symm.trans right)

theorem rfc6979Within_unique {first second secret : Nat} {digest extra : ByteArray}
    {a b : Nat × Nat} (ha : Ecdsa.rfc6979Within first secret digest extra = some a)
    (hb : Ecdsa.rfc6979Within second secret digest extra = some b) : a = b :=
  signingAttempts_unique _ _ _ _ _ ha hb

theorem signMessageWithin_ne_some_none (attempts : Nat) (inputs : Array ByteArray) :
    Ecdsa.signMessageWithin attempts inputs ≠ some none := by
  unfold Ecdsa.signMessageWithin Ecdsa.signedWithin
  cases Ecdsa.rfc6979Within attempts (Ecdsa.secretValue (Arith.argument inputs 0))
    (Operations.hash (Arith.argument inputs 1)) ByteArray.empty <;> simp

theorem signMessageWithin_unique {first second : Nat} {inputs : Array ByteArray}
    {a b : ByteArray} (ha : Ecdsa.signMessageWithin first inputs = some (some a))
    (hb : Ecdsa.signMessageWithin second inputs = some (some b)) : a = b := by
  unfold Ecdsa.signMessageWithin Ecdsa.signedWithin at ha hb
  cases hfirst : Ecdsa.rfc6979Within first (Ecdsa.secretValue (Arith.argument inputs 0))
    (Operations.hash (Arith.argument inputs 1)) ByteArray.empty with
  | none => simp [hfirst] at ha
  | some x =>
    cases hsecond : Ecdsa.rfc6979Within second (Ecdsa.secretValue (Arith.argument inputs 0))
      (Operations.hash (Arith.argument inputs 1)) ByteArray.empty with
    | none => simp [hsecond] at hb
    | some y =>
      have he := rfc6979Within_unique hfirst hsecond
      subst y
      simp only [hfirst, Option.map_some, Option.some.injEq] at ha
      simp only [hsecond, Option.map_some, Option.some.injEq] at hb
      exact ha.symm.trans hb

theorem exists_signature_of_not_neverSigns {inputs : Array ByteArray}
    (terminates : ¬ Ecdsa.NeverSigns inputs) :
    ∃ attempts bytes, Ecdsa.signMessageWithin attempts inputs = some (some bytes) := by
  classical
  have existsAttempt : ∃ attempts, Ecdsa.signMessageWithin attempts inputs ≠ none := by
    apply Classical.byContradiction
    intro absent
    exact terminates (fun attempts => Classical.byContradiction
      (fun found => absent ⟨attempts, found⟩))
  obtain ⟨attempts, found⟩ := existsAttempt
  cases hresult : Ecdsa.signMessageWithin attempts inputs with
  | none => exact False.elim (found hresult)
  | some result =>
    cases result with
    | none => exact False.elim (signMessageWithin_ne_some_none attempts inputs hresult)
    | some bytes => exact ⟨attempts, bytes, hresult⟩

theorem signMessage_eq_of_found {inputs : Array ByteArray} {attempts : Nat} {bytes : ByteArray}
    (found : Ecdsa.signMessageWithin attempts inputs = some (some bytes)) :
    Ecdsa.signMessage inputs = bytes := by
  classical
  have existsResult : ∃ n b, Ecdsa.signMessageWithin n inputs = some (some b) :=
    ⟨attempts, bytes, found⟩
  rw [Ecdsa.signMessage, dite_eq_left existsResult]
  exact signMessageWithin_unique (Classical.choose_spec (Classical.choose_spec existsResult)) found

theorem signMessage_found {inputs : Array ByteArray} (terminates : ¬ Ecdsa.NeverSigns inputs) :
    ∃ attempts, Ecdsa.signMessageWithin attempts inputs = some (some (Ecdsa.signMessage inputs)) := by
  obtain ⟨attempts, bytes, found⟩ := exists_signature_of_not_neverSigns terminates
  exact ⟨attempts, (signMessage_eq_of_found found).symm ▸ found⟩

end P256.Proofs.Signing
