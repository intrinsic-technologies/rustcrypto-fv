import Hkdf.Spec.Program

set_option autoImplicit false

namespace Hkdf.Proofs.Program

open Prelude X86 X86.Machine

structure SupportedMachine (bindings : Bindings) (s : RamState) : Prop where
  supported : SupportedIntegerMachineState bindings.processor s
  smrr : SMRRUnblocked bindings s
  writeBack : WriteBackMemoryType bindings s 0
  leadingZeroCount : LeadingZeroCountReported bindings s

theorem SupportedMachine.of_root (bindings : Bindings) (s : RamState)
    (machine : SupportedIntegerMachineState bindings.processor s)
    (environment : MachineRamUnitStrideDecodable bindings s) : SupportedMachine bindings s :=
  ⟨machine, environment.smrr, environment.memoryType, environment.leadingZeroCount⟩

theorem SupportedMachine.to_environment {bindings : Bindings} {s : RamState}
    (machine : SupportedMachine bindings s) (stride : UnitStringStride bindings) :
    MachineRamUnitStrideDecodable bindings s :=
  ⟨machine.smrr, machine.writeBack, stride, machine.leadingZeroCount⟩

def InPageTables (address : BitVec 64) : Prop :=
  Hkdf.Spec.Program.pageTables.Contains address.toNat

def PreservesABI (initial final : RamState) : Prop :=
  Hkdf.Spec.Program.CalleeSavedRegistersUnchanged initial final ∧
  RFLAGS.DirectionFlagClear final.RFLAGS ∧
  final.MXCSR = initial.MXCSR ∧
  final.FP87_Control = initial.FP87_Control

end Hkdf.Proofs.Program
