import P256.Spec.Ecdsa

set_option autoImplicit false

namespace P256.Proofs.Signing.Search

open P256.Spec Standards.RFC.DeterministicSigning

abbrev State := Nonce.State

def nextCandidate (state : State) : Nat × State :=
  Nonce.candidate Operations.hash 64 32 Operations.domain.n state

def nextState (state : State) : State :=
  Nonce.reject Operations.hash 64 (nextCandidate state).2

def ValidNonce (nonce : Nat) : Prop :=
  0 < nonce ∧ nonce < Operations.domain.n

inductive FirstValid : State → Nat → State → Prop where
  | accept (state : State) (valid : ValidNonce (nextCandidate state).1) :
      FirstValid state (nextCandidate state).1 (nextState state)
  | reject (state : State) {nonce : Nat} {final : State}
      (invalid : ¬ ValidNonce (nextCandidate state).1)
      (rest : FirstValid (nextState state) nonce final) : FirstValid state nonce final

def signingAttempts (secret : Nat) (digest : ByteArray) (attempts : Nat) (state : State) :
    Option (Nat × Nat) :=
  Standards.RFC.DeterministicSigning.Signing.signingAttempts Operations.hash 64 32
    Operations.domain.n (fun nonce => Ecdsa.signWithNonce secret nonce digest) attempts state

theorem FirstValid.valid {state final : State} {nonce : Nat}
    (found : FirstValid state nonce final) : ValidNonce nonce := by
  induction found with
  | accept _ valid => exact valid
  | reject _ _ _ ih => exact ih

theorem signWithNonce_eq_none_of_invalid (secret : Nat) (digest : ByteArray) {nonce : Nat}
    (invalid : ¬ ValidNonce nonce) : Ecdsa.signWithNonce secret nonce digest = none := by
  have either : nonce = 0 ∨ Operations.domain.n ≤ nonce := by
    unfold ValidNonce at invalid
    omega
  rcases either with zero | large
  · simp only [Ecdsa.signWithNonce, Standards.SECG.ECC.ECDSA.signWithNonce, zero,
      beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte]
  · simp only [Ecdsa.signWithNonce, Standards.SECG.ECC.ECDSA.signWithNonce, large,
      decide_true, Bool.or_true, ↓reduceIte]

theorem signingAttempts_step {Signature : Type} (hash : ByteArray → ByteArray)
    (blockBytes digestBytes order attempts : Nat) (state : State)
    (sign : Nat → Option Signature)
    (invalid : ∀ nonce, ¬ (0 < nonce ∧ nonce < order) → sign nonce = none) :
    Standards.RFC.DeterministicSigning.Signing.signingAttempts hash blockBytes digestBytes
      order sign (attempts + 1) state =
      match sign (Nonce.candidate hash blockBytes digestBytes order state).1 with
      | some signature => some signature
      | none => Standards.RFC.DeterministicSigning.Signing.signingAttempts hash blockBytes
          digestBytes order sign attempts
          (Nonce.reject hash blockBytes (Nonce.candidate hash blockBytes digestBytes order state).2) := by
  rw [Standards.RFC.DeterministicSigning.Signing.signingAttempts]
  generalize Nonce.candidate hash blockBytes digestBytes order state = candidate
  rcases candidate with ⟨nonce, next⟩
  dsimp only
  by_cases valid : 0 < nonce ∧ nonce < order
  · simp only [Bool.and_eq_true, decide_eq_true_eq, valid, and_self, ↓reduceIte]
    cases sign nonce <;> rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq, valid, ↓reduceIte, invalid nonce valid]

theorem signingAttempts_succ (secret : Nat) (digest : ByteArray) (attempts : Nat)
    (state : State) :
    P256.Proofs.Signing.Search.signingAttempts secret digest (attempts + 1) state =
      match Ecdsa.signWithNonce secret (nextCandidate state).1 digest with
      | some signature => some signature
      | none => P256.Proofs.Signing.Search.signingAttempts secret digest attempts (nextState state) := by
  have step := signingAttempts_step Operations.hash 64 32 Operations.domain.n attempts state
    (fun nonce => Ecdsa.signWithNonce secret nonce digest)
    (fun nonce invalid => signWithNonce_eq_none_of_invalid secret digest invalid)
  cases result : Ecdsa.signWithNonce secret (nextCandidate state).1 digest
  all_goals
    simp only [nextCandidate] at result
    simpa only [signingAttempts, nextState, nextCandidate, result] using step

theorem signingAttempts_invalid (secret : Nat) (digest : ByteArray) (attempts : Nat)
    {state : State} (invalid : ¬ ValidNonce (nextCandidate state).1) :
    P256.Proofs.Signing.Search.signingAttempts secret digest (attempts + 1) state =
      P256.Proofs.Signing.Search.signingAttempts secret digest attempts (nextState state) := by
  rw [signingAttempts_succ, signWithNonce_eq_none_of_invalid secret digest invalid]

theorem FirstValid.signingAttempts {state final : State} {nonce : Nat}
    (found : FirstValid state nonce final) (secret : Nat) (digest : ByteArray) :
    ∃ skipped, ∀ attempts,
      P256.Proofs.Signing.Search.signingAttempts secret digest (skipped + attempts + 1) state =
        match Ecdsa.signWithNonce secret nonce digest with
        | some signature => some signature
        | none => P256.Proofs.Signing.Search.signingAttempts secret digest attempts final := by
  induction found with
  | accept state valid =>
      refine ⟨0, fun attempts => ?_⟩
      simp only [Nat.zero_add]
      exact signingAttempts_succ secret digest attempts state
  | reject state invalid rest ih =>
      obtain ⟨skipped, ih⟩ := ih
      refine ⟨skipped + 1, fun attempts => ?_⟩
      rw [signingAttempts_invalid secret digest _ invalid]
      simpa only [Nat.add_assoc, Nat.add_comm 1 attempts] using ih attempts

theorem FirstValid.signingAttempts_none {state final : State} {nonce secret : Nat}
    {digest : ByteArray} (found : FirstValid state nonce final)
    (noSuccess : ∀ attempts, P256.Proofs.Signing.Search.signingAttempts secret digest attempts state = none) :
    Ecdsa.signWithNonce secret nonce digest = none ∧
      ∀ attempts, P256.Proofs.Signing.Search.signingAttempts secret digest attempts final = none := by
  obtain ⟨skipped, run⟩ := found.signingAttempts secret digest
  have head := noSuccess (skipped + 0 + 1)
  rw [run 0] at head
  cases result : Ecdsa.signWithNonce secret nonce digest with
  | some signature => simp [result] at head
  | none =>
      refine ⟨rfl, fun attempts => ?_⟩
      have tail := noSuccess (skipped + attempts + 1)
      simpa only [run attempts, result] using tail

theorem exists_firstValid_of_signingAttempts {secret attempts : Nat}
    {digest : ByteArray} {signature : Nat × Nat} {state : State}
    (success : P256.Proofs.Signing.Search.signingAttempts secret digest attempts state = some signature) :
    ∃ nonce final, FirstValid state nonce final ∧
      (Ecdsa.signWithNonce secret nonce digest = some signature ∨
        (Ecdsa.signWithNonce secret nonce digest = none ∧
          ∃ remaining < attempts,
            P256.Proofs.Signing.Search.signingAttempts secret digest remaining final = some signature)) := by
  induction attempts generalizing state with
  | zero => simp [signingAttempts,
      Standards.RFC.DeterministicSigning.Signing.signingAttempts] at success
  | succ attempts ih =>
      by_cases valid : ValidNonce (nextCandidate state).1
      · refine ⟨(nextCandidate state).1, nextState state, .accept state valid, ?_⟩
        rw [signingAttempts_succ] at success
        cases result : Ecdsa.signWithNonce secret (nextCandidate state).1 digest with
        | none =>
            exact .inr ⟨rfl, attempts, Nat.lt_succ_self _, by simpa only [result] using success⟩
        | some output =>
            have eq : output = signature := by simpa only [result, Option.some.injEq] using success
            exact .inl (congrArg some eq)
      · rw [signingAttempts_invalid secret digest attempts valid] at success
        obtain ⟨nonce, final, found, result⟩ := ih success
        refine ⟨nonce, final, .reject state valid found, ?_⟩
        rcases result with success | ⟨failure, remaining, lt, success⟩
        · exact .inl success
        · exact .inr ⟨failure, remaining, Nat.lt_trans lt (Nat.lt_succ_self _), success⟩

end P256.Proofs.Signing.Search
