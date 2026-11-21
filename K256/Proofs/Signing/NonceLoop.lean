import K256.Proofs.Common.Divergence
import K256.Proofs.Signing.SearchBound

namespace K256.Proofs.Signing

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift Standards.RFC.DeterministicSigning
  Standards.SECG.DomainParameters Standards.SECG.ECC Standards.NIST.SHA2

abbrev signCandidate (d : Nat) (message : ByteArray) (nonce : Nat) :=
  ECDSA.signWithNonce Secp256k1.domain d nonce (SHA256.hashBytes message)

abbrev initialNonceState (d : Nat) (message : ByteArray) :=
  Nonce.initialState SHA256.hashBytes 64 32 Secp256k1.domain.n d (SHA256.hashBytes message)

structure NonceLoop (P : Lifted) (sign : Nat → Option (Nat × Nat))
    (post : Nat × Nat → Output Value Ram Reg.count → Prop)
    (atCandidate : Nonce.State → P.State → Prop) : Prop where
  accepted : ∀ {state x pair}, atCandidate state x → attemptResult sign state = some pair →
    ∃ out, P.program.Exec (dialect Extracted.programImage) x out ∧ post pair out
  rejected : ∀ {state x}, atCandidate state x → attemptResult sign state = none →
    ∃ mid next, (P.program.sem (dialect Extracted.programImage)).Reaches x mid ∧
      P.address x.location.label ≠ P.address mid.location.label ∧
      (P.program.sem (dialect Extracted.programImage)).Reaches mid next ∧
      atCandidate (retry state) next

theorem NonceLoop.terminates {P sign post atCandidate} (loop : NonceLoop P sign post atCandidate)
    {count state x pair} (atHead : atCandidate state x)
    (found : attempts sign count state = some pair) :
    ∃ out, P.program.Exec (dialect Extracted.programImage) x out ∧ post pair out := by
  induction count generalizing state x with
  | zero => cases found
  | succ count ih =>
    rw [attempts_succ] at found
    cases result : attemptResult sign state with
    | some value =>
      have eq : value = pair := Option.some.inj (by simpa only [result, Option.orElse_some] using found)
      exact loop.accepted atHead (eq ▸ result)
    | none =>
      obtain ⟨mid, next, front, _, back, again⟩ := loop.rejected atHead result
      obtain ⟨out, run, done_⟩ := ih again (by simpa only [result, Option.orElse_none] using found)
      exact ⟨out, Program.Exec.of_sem ((front.trans back).exec run.sem), done_⟩

theorem NonceLoop.neverReturns [bindings : Bindings] {P sign post atCandidate}
    (loop : NonceLoop P sign post atCandidate)
    {initial : RamState} {routine : Routine} {inputs : List ByteArray} {args : List Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall routine initial inputs args)
    {entry : P.Label} (address : P.address entry = routine.entryAddress)
    (blocks : ∀ l, LiftedBlock Extracted.programImage P l)
    {start : P.State} {seed : Nonce.State}
    (front : (P.program.sem (dialect Extracted.programImage)).Reaches
      ⟨P.locationOf entry initial, []⟩ start)
    (atHead : atCandidate seed start)
    (absent : ∀ count, attempts sign count seed = none) : NeverReturns initial := by
  apply Common.neverReturns_of_lifted_progress
    (I := fun x => ∃ state, atCandidate state x ∧ ∀ count, attempts sign count state = none)
    hBindings hMachine hCall address blocks front ⟨seed, atHead, absent⟩
  rintro x ⟨state, atHead, exhausted⟩
  have failed : attemptResult sign state = none := by
    have first := exhausted 1
    rw [attempts_succ sign 0] at first
    cases h : attemptResult sign state with
    | none => rfl
    | some value => simp [h] at first
  obtain ⟨mid, next, pre, moved, back, again⟩ := loop.rejected atHead failed
  refine ⟨mid, next, pre, moved, back, retry state, again, fun n => ?_⟩
  simpa only [attempts_succ sign n, failed, Option.orElse_none] using exhausted (n+1)

end K256.Proofs.Signing
