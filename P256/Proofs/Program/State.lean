import P256.Spec.Program
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86Proofs

theorem supportedMachine_of_ready_agrees [bindings : Bindings]
    {initial final : RamState} {components : List Component}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hReady : ReadyToStep final) (hAgrees : AgreesExcept components initial final) :
    SupportedIntegerMachineState bindings.processor final :=
  ⟨hReady.cpu, SupportedSSE.of_agreesExcept hAgrees hMachine.sse, hReady.memory, hReady.ready⟩

theorem bindingsSupported_of_ready_agrees [bindings : Bindings]
    {initial final : RamState} {components : List Component}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hReady : ReadyToStep final) (hAgrees : AgreesExcept components initial final) :
    MachineRamUnitStrideDecodable bindings final :=
  ⟨hReady.smrr, hReady.memoryType, hBindings.stringStride,
    hBindings.leadingZeroCount.imp (fun _ =>
      reportsCPUFeature_of_sameControls (SameControls.of_fixedPart hAgrees.rest))⟩

end P256.Proofs.Program
