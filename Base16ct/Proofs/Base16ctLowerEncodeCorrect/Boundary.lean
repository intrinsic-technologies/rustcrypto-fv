import Base16ct.Spec.Program
import Base16ct.Proofs.Copied.Md5.Proofs.Machine
import X86Proofs.Program.ReadWrite.Bytes

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86Proofs

theorem lowerEncode_returnBoundary [bindings : Machine.Bindings]
    {initial : Machine.RamState} {input : List UInt8} {outputCapacity : Nat}
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidCall base16ctLowerEncode initial input.toByteArray outputCapacity (2 * input.length) (2 * input.length ≤ outputCapacity)) :
    nearReturn64Boundary initial = .ok (returnBoundary initial) := by
  have hReady : ReadyToStep initial :=
    ReadyToStep.of_supported hMachine hBindings.smrr hBindings.memoryType
      (DecoderFeatures.of_supported hMachine hBindings.leadingZeroCount)
  exact nearReturn64Boundary_eq initial hReady.dataReady hMachine.integer.ss
    (Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable hCall.stack)

theorem lowerEncode_returnBoundary_bounds
    {initial : Machine.RamState} {input : List UInt8} {outputCapacity : Nat}
    (hCall : ValidCall base16ctLowerEncode initial input.toByteArray outputCapacity (2 * input.length) (2 * input.length ≤ outputCapacity)) :
    (returnBoundary initial).rip.toNat < userAddressLimit ∧
      ¬ InProgram (returnBoundary initial).rip := by
  obtain ⟨address, hWord, hLow, hOutside⟩ := hCall.returnAddress
  have hReadable := Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable hCall.stack
  have hBytes := Bytes.of_memLoad (n := 64) hReadable.mem
  have hLoad : Machine.loadBytes initial.external (stackPtr initial) 8 = .ok address := by
    simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show initial.regValue .rsp = stackPtr initial from rfl] using hWord.2
  have hEq : (returnBoundary initial).rip = address :=
    Except.ok.inj (hBytes.loadBytes64.symm.trans hLoad)
  rw [hEq]
  exact ⟨hLow, hOutside⟩

end Base16ct.Proofs.LowerEncode
