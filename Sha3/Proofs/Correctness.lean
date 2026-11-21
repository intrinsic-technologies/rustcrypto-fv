import Sha3.Proofs.Wrapper.Execution

namespace Sha3.Statements

open Sha3.Spec Sha3.Spec.Program Standards.NIST Prelude X86 X86Proofs Sha3.Proofs

theorem sha3_224_digest_slices_writes_sha3_224_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha3_224_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha3_224_digest_slices initial,
          Stack.region initial sha3_224_digest_slices.minStackBytes] ∧
      readOutput sha3_224_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_224 (SHA3.bytesToBits (message inputs)))) := by
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution .sha224 .plain (split := 0) hMachine hBindings hCall
  have hBoundary := Wrapper.validInvocation_returnBoundary
    (v := .sha224) (mode := .plain) (split := 0)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hCall
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  exact hResult.output.trans
    (congrArg Except.ok (Absorption.digestLanes_sha3_224 (message inputs)))

theorem sha3_256_digest_slices_writes_sha3_256_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha3_256_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha3_256_digest_slices initial,
          Stack.region initial sha3_256_digest_slices.minStackBytes] ∧
      readOutput sha3_256_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_256 (SHA3.bytesToBits (message inputs)))) := by
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution .sha256 .plain (split := 0) hMachine hBindings hCall
  have hBoundary := Wrapper.validInvocation_returnBoundary
    (v := .sha256) (mode := .plain) (split := 0)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hCall
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  exact hResult.output.trans
    (congrArg Except.ok (Absorption.digestLanes_sha3_256 (message inputs)))

theorem sha3_384_digest_slices_writes_sha3_384_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha3_384_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha3_384_digest_slices initial,
          Stack.region initial sha3_384_digest_slices.minStackBytes] ∧
      readOutput sha3_384_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_384 (SHA3.bytesToBits (message inputs)))) := by
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution .sha384 .plain (split := 0) hMachine hBindings hCall
  have hBoundary := Wrapper.validInvocation_returnBoundary
    (v := .sha384) (mode := .plain) (split := 0)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hCall
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  exact hResult.output.trans
    (congrArg Except.ok (Absorption.digestLanes_sha3_384 (message inputs)))

theorem sha3_512_digest_slices_writes_sha3_512_of_message
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall sha3_512_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion sha3_512_digest_slices initial,
          Stack.region initial sha3_512_digest_slices.minStackBytes] ∧
      readOutput sha3_512_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_512 (SHA3.bytesToBits (message inputs)))) := by
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution .sha512 .plain (split := 0) hMachine hBindings hCall
  have hBoundary := Wrapper.validInvocation_returnBoundary
    (v := .sha512) (mode := .plain) (split := 0)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hCall
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  exact hResult.output.trans
    (congrArg Except.ok (Absorption.digestLanes_sha3_512 (message inputs)))

end Sha3.Statements
