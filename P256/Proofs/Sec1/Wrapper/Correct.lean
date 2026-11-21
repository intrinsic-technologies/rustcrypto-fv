import P256.Proofs.Sec1.Wrapper.Call
import P256.Proofs.Sec1.Wrapper.Reject
import P256.Proofs.Sec1.Wrapper.Success
import P256.Proofs.Sec1.Model

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct_of_decoder [bindings : Bindings]
    (decoder : ∀ (s : RamState) (boundary : ReturnBoundary) (bytes : ByteArray),
      DecodePre s boundary bytes → ∃ t, CalleeResult s t boundary 80 3680 ∧
        PublicKeyResultAt t (s.regValue .rdi) (Points.decodePublicKey bytes))
    {initial : RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall publicKeyFromSec1Bytes initial [bytes]) :
    ∃ (fuel : Nat) (final : RamState), UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      match Keys.publicKeyFromSec1 #[bytes] with
      | some result => SuccessfulStatus final ∧
        MemoryWriteFrame initial final
          #v[outputRegion publicKeyFromSec1Bytes initial [bytes], allocatorStateRegion,
            randomSourceRegion, callStack publicKeyFromSec1Bytes initial] ∧
        readOutput publicKeyFromSec1Bytes initial final = .ok result
      | none => FailureStatus final invalidPublicKeyStatus ∧
        MemoryWriteFrame initial final
          #v[allocatorStateRegion, randomSourceRegion, callStack publicKeyFromSec1Bytes initial] := by
  obtain ⟨slices, valid⟩ := hCall
  obtain ⟨s, entry⟩ := decoder_entry_correct hBindings hMachine valid
  obtain ⟨t, result, decoded⟩ := decoder s (returnBoundary initial) bytes
    ⟨entry.pre, entry.inputBytes, entry.length⟩
  cases model : Points.decodePublicKey bytes with
  | none =>
    rw [model] at decoded
    obtain ⟨fuel, final, unique, machine, supported, saved, direction, status, frame⟩ :=
      reject_from_decoder hBindings hMachine valid entry result decoded
    refine ⟨fuel, final, unique, machine, supported, saved, direction, ?_⟩
    simpa only [publicKeyFromSec1_eq, model, Option.map_none] using And.intro status frame
  | some point =>
    obtain ⟨x, y, rfl⟩ := decodePublicKey_some_affine model
    rw [model] at decoded
    obtain ⟨fuel, final, unique, machine, supported, saved, direction, status, frame, output⟩ :=
      success_from_decoder hBindings hMachine valid model entry result decoded
    have encoding : Points.encode (.affine x y) = Keys.uncompressed (.affine x y) := rfl
    rw [encoding] at output
    refine ⟨fuel, final, unique, machine, supported, saved, direction, ?_⟩
    simpa only [publicKeyFromSec1_eq, model, Option.map_some] using
      And.intro status (And.intro frame output)

end P256.Proofs.Sec1.Wrapper
