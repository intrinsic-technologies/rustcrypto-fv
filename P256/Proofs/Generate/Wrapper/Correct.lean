import P256.Proofs.Generate.Wrapper.Tail.Compute
import P256.Proofs.Generate.Wrapper.Tail.Ready
import P256.Proofs.Generate.Wrapper.Tail.Copy
import P256.Proofs.Generate.Wrapper.Finish.Correct

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem generate_correct_of_sampler [bindings : Bindings] {initial : RamState}
    {randomBytes : ByteArray} (sampler : Sampler.Contract bindings)
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
        .ok (Spec.Generate.generatedSigningKey #[randomBytes]) := by
  obtain ⟨slices,call⟩ := hCall
  obtain ⟨d,trace⟩ := (Generate.arguments_iff randomBytes).mp call.argumentsValid
  have draw := draw_some_iff_trace.mpr trace
  have outside := outer_boundary call hMachine hBindings
  obtain ⟨a,sa,ipa,scalarA,pointA⟩ := compute sampler hBindings hMachine call draw
  obtain ⟨b,sb,ipb,dst,src,cnt,len,mem⟩ := copy_ready call draw sa outside ipa pointA
  obtain ⟨c,sc,ipc,length,pointC,scalarC⟩ := copy_point call draw sb outside ipb src dst cnt len
    (by rwa [mem]) (by rwa [mem])
  exact Finish.finish hBindings hMachine call draw sc ipc length
    (generated_payload draw scalarC pointC)

end P256.Proofs.Generate.Wrapper
