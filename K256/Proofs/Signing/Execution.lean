import K256.Proofs.Signing.NonceLoop

namespace K256.Proofs.Signing

open K256.Spec K256.Spec.Program Prelude X86 Standards.SECG.ECC Standards.SECG.DomainParameters

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open Standards.RFC.DeterministicSigning

def ReturnedSignature [bindings : Machine.Bindings] (initial : Machine.RamState)
    (bytes : ByteArray) : Prop :=
  ∃ (fuel : Nat) (final : Machine.RamState),
    UniqueExecution initial fuel final ∧
    SupportedIntegerMachineState bindings.processor final ∧
    MachineRamUnitStrideDecodable bindings final ∧
    CalleeSavedRegistersUnchanged initial final ∧
    DirectionFlagUnset final ∧
    MemoryWriteFrame initial final
      #v[outputRegion signingKeyTrySign initial,
        Stack.region initial signingKeyTrySign.minStackBytes] ∧
    readOutput signingKeyTrySign initial final = .ok bytes

def signatureOutput (initial : RamState) (rs : Nat × Nat) (out : Output Value Ram Reg.count) : Prop :=
  Common.Returned initial #v[outputRegion signingKeyTrySign initial,
    Stack.region initial signingKeyTrySign.minStackBytes] out ∧
  (outputRegion signingKeyTrySign initial).HasBytes out.store (Ecdsa.normalizeS rs.1 rs.2)

theorem execution_of_nonceLoop [bindings : Machine.Bindings] {initial : Machine.RamState}
    {secret message : ByteArray} {d : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyTrySign initial [secret, message])
    {P : Lifted} {entry : P.Label} {head : P.State} {inv : Nonce.State → P.State → Prop}
    (address : P.address entry = signingKeyTrySign.entryAddress)
    (blocks : ∀ l, LiftedBlock Extracted.programImage P l)
    (live : ∀ r ∈ [0,3,4,5,12,13,14,15,22], Live P.retLive r)
    (prefixRun : (P.program.sem (dialect Extracted.programImage)).Reaches
      ⟨P.locationOf entry initial, []⟩ head)
    (start : inv (initialNonceState d message) head)
    (loop : NonceLoop P (signCandidate d message) (signatureOutput initial) inv) :
    (∀ attempts r s, Ecdsa.signatureWithin d message attempts = some (r, s) →
      ReturnedSignature initial (Ecdsa.normalizeS r s)) ∧
    ((∀ attempts, Ecdsa.signatureWithin d message attempts = none) → NeverReturns initial) := by
  constructor
  · intro n r s found
    obtain ⟨out, run, ret, bytes⟩ := loop.terminates start found
    exact Common.output_of_lifted_execution hBindings hMachine hCall address blocks live
      (Program.Exec.of_sem (prefixRun.exec run.sem)) ret bytes
  · exact fun absent => loop.neverReturns hBindings hMachine hCall address blocks prefixRun start absent

end K256.Proofs.Signing
