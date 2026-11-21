import Hkdf.Proofs.Standard.Initialization
import Hkdf.Proofs.Standard.Update.Correctness
import Hkdf.Proofs.Standard.Finalize
import Hkdf.Proofs.Standard.Finalize.Result
import Hkdf.Proofs.Standard.Finalize.Suffix.WithState
import Hkdf.Proofs.Standard.Extract.Return
import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Common.CallFrame

namespace Hkdf.Statements

open Hkdf.Spec Hkdf.Spec.Program Prelude X86

theorem hkdf_sha256_extract_writes_prk_of_salt_and_ikm
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {salt : Option ByteArray} {ikm : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidExtractCall hkdfSha256Extract initial salt ikm) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion initial hkdfSha256Extract,
          Stack.region initial hkdfSha256Extract.minStackBytes] ∧
      readOutput (outputRegion initial hkdfSha256Extract) final.external =
        .ok (RFC5869.extract .sha256 salt (concatenation ikm)) := by
  let ctx : Hkdf.Proofs.Standard.Context initial salt ikm := ⟨hBindings, hMachine, hCall⟩
  obtain ⟨_, s, _, readyS, initialized⟩ :=
    Hkdf.Proofs.Standard.Initialization.initialize_correct ctx
  obtain ⟨_, u, _, _, completed⟩ :=
    Hkdf.Proofs.Standard.Update.from_initialized ctx readyS initialized
  obtain ⟨a, stateA, pre, hmac, rspA, _, outputA, boundaryA, pointerA, size⟩ :=
    Hkdf.Proofs.Standard.Finalize.prepare ctx completed
  obtain ⟨b, result, bytes, _⟩ :=
    Hkdf.Proofs.Standard.Finalize.Suffix.finalize_correct_with_state pre hmac size
  have ready := Hkdf.Proofs.Standard.Finalize.digest_ready_of_callee ctx stateA result
    rspA outputA boundaryA pointerA bytes
  obtain ⟨n, final, returned, machine, environment, saved, direction, _, _, frame, output⟩ :=
    Hkdf.Proofs.Standard.Extract.finish ctx ready.toState ready.rip ready.rsp
      ready.outputPointer ready.bytes
  obtain ⟨m, prefixRun⟩ := ready.execution
  have completedRun := prefixRun.returns returned
  have initialReady := Hkdf.Proofs.Common.Machine.entryReady bindings ctx.environment
    ctx.machine ctx.call.programLoaded
  have boundary := (Hkdf.Proofs.Common.Machine.returnBoundary_valid initialReady.ready
    ctx.call.stack ctx.call.returnAddress).1
  obtain ⟨fuel, unique⟩ := X86Proofs.Returns.unique_of_boundary boundary completedRun
  have prefixFrame : MemoryWriteFrame initial b
      #v[outputRegion initial hkdfSha256Extract,
        Stack.region initial hkdfSha256Extract.minStackBytes] := by
    apply Hkdf.Proofs.Common.CallFrame.frame_mono ready.frame
    intro region member a contains
    have same : region = Stack.region initial hkdfSha256Extract.minStackBytes := by
      simpa using member
    subst region
    exact ⟨_, by simp, contains⟩
  refine ⟨fuel, final, unique, machine, environment, saved, direction,
    X86Proofs.memoryWriteFrame_trans prefixFrame frame, ?_⟩
  exact output

end Hkdf.Statements
