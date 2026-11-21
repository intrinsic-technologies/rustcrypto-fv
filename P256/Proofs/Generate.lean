import P256.Proofs.Generate.Sampler.Correct
import P256.Proofs.Generate.Wrapper.Correct

set_option autoImplicit false

namespace P256.Proofs.Generate

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

theorem generate_correct [bindings : Bindings] {initial : RamState} {randomBytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyGenerateFromRng initial [randomBytes]) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyGenerateFromRng initial [randomBytes],allocatorStateRegion,
          randomSourceRegion,callStack signingKeyGenerateFromRng initial] ∧
      readOutput signingKeyGenerateFromRng initial final =
        .ok (Spec.Generate.generatedSigningKey #[randomBytes]) :=
  Wrapper.generate_correct_of_sampler (Sampler.sampler_correct bindings) hBindings hMachine hCall

end P256.Proofs.Generate
