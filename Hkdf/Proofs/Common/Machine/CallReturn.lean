import Hkdf.Proofs.Program
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Sse

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Machine

open Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86Proofs

theorem supportedMachine_of_ready_agrees [bindings : Machine.Bindings]
    {initial final : Machine.RamState} {components : List Component}
    (hMachine : SupportedMachine bindings initial) (hReady : ReadyToStep final)
    (hAgrees : AgreesExcept components initial final) :
    SupportedMachine bindings final := by
  have hControls := SameControls.of_fixedPart hAgrees.rest
  exact ⟨⟨hReady.cpu, SupportedSSE.of_agreesExcept hAgrees hMachine.supported.sse,
      hReady.memory, hReady.ready⟩,
    hReady.smrr, hReady.memoryType,
    by
      obtain ⟨enabled, report⟩ := hMachine.leadingZeroCount
      exact ⟨enabled, reportsCPUFeature_of_sameControls hControls report⟩⟩

theorem preservesABI_of_agrees {initial final : Machine.RamState}
    {components : List Component} (hAgrees : AgreesExcept components initial final)
    (hDirection : Prelude.RFLAGS.DirectionFlagClear initial.RFLAGS)
    (hRegisters : ∀ register ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      final.regValue register = initial.regValue register)
    (hdf : .df ∉ components) (hmxcsr : .mxcsr ∉ components) (hfcw : .fcw ∉ components) :
    PreservesABI initial final :=
  ⟨hRegisters, hAgrees.directionFlagClear hdf hDirection,
    hAgrees.mxcsr hmxcsr, hAgrees.fcw hfcw⟩

end Hkdf.Proofs.Common.Machine
