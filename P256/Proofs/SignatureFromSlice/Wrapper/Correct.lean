import P256.Proofs.SignatureFromSlice.Wrapper.Entry.Call
import P256.Proofs.SignatureFromSlice.Wrapper.Accepted
import P256.Proofs.SignatureFromSlice.Wrapper.Reject

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Wrapper

theorem signature_from_slice_of_decoder [bindings : Bindings]
    (decoder : ∀ {s : RamState} {boundary : ReturnBoundary} {input : ByteArray},
      CalleePre s boundary 0x109ac0 input.size 72 560 →
      s.regValue .rdx = BitVec.ofNat 64 input.size →
      (registerRegion s .rsi input.size).HasBytes s.external input →
      ∃ t, CalleeResult s t boundary 72 560 ∧
        SignatureFromDer.Fixed.ResultAt t (s.regValue .rdi) input)
    {initial : RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signatureFromSlice initial [bytes]) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      match Ecdsa.signatureFromSlice #[bytes] with
      | some result =>
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion signatureFromSlice initial [bytes], allocatorStateRegion,
            randomSourceRegion, callStack signatureFromSlice initial] ∧
        readOutput signatureFromSlice initial final = .ok result
      | none =>
        FailureStatus final invalidSignatureBytesStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion, randomSourceRegion, callStack signatureFromSlice initial] := by
  obtain ⟨slices, call⟩ := hCall
  obtain ⟨s, entry⟩ := decoder_entry_correct hBindings hMachine call
  obtain ⟨t, returned, decoded⟩ := decoder entry.pre entry.length entry.inputBytes
  cases model : Ecdsa.signatureFromSlice #[bytes] with
  | none =>
    simpa only [model] using
      reject_from_decoder hBindings hMachine call entry returned decoded model
  | some result =>
    simpa only [model] using
      accept_from_decoder hBindings hMachine call entry returned decoded model

end P256.Proofs.SignatureFromSlice
