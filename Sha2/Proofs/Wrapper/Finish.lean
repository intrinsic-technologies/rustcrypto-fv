import Sha2.Proofs.Wrapper.Hash.Finalize
import Sha2.Proofs.Wrapper.Hash.Serialize
import Sha2.Proofs.Wrapper.Finish.Epilogue
import Sha2.Proofs.Wrapper.Output

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper

open Sha2.Spec Sha2.Spec.Program Standards.NIST Prelude X86 X86.Machine

 theorem finish [bindings : Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input}
    (ctx : Context initial inputs v) (buffered : Buffered initial s (message inputs) v)
    (rip : s.RIP = v.pc 0x1bb) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion v.routine initial, Stack.region initial v.routine.minStackBytes] ∧
      readOutput v.routine initial final =
        .ok (v.digest (message inputs)) := by
  obtain ⟨compressed, compressedState⟩ := Hash.finalize ctx buffered rip
  obtain ⟨serialized, serializedState, serializedRip, output⟩ := Hash.serialize ctx compressedState
  obtain ⟨final, result⟩ := Finish.run ctx serializedState serializedRip
  obtain ⟨fuel, unique⟩ := result.execution
  refine ⟨fuel, final, unique, result.machine.supported, result.machine.to_environment ctx.stride,
    result.calleeSaved, result.directionFlag, result.frame, ?_⟩
  apply readOutput_variant
  rw [result.memory]
  exact output

end Sha2.Proofs.Wrapper
