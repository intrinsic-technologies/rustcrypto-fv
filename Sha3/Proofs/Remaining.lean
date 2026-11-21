import Sha3.Proofs.Wrapper.Execution

namespace Sha3.Statements

open Sha3.Spec Sha3.Spec.Program Standards.NIST Prelude X86 X86Proofs Sha3.Proofs

theorem sha3_224_digest_writes_sha3_224_of_data[bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall sha3_224_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion sha3_224_digest initial,
          Stack.region initial sha3_224_digest.minStackBytes] ∧
      readDigestOutput sha3_224_digest initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_224 (SHA3.bytesToBits data))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha224 .digest initial #[⟨initial.regValue .rdi, data⟩] 0 false false :=
    ⟨data, rfl, hCall⟩
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha224 .digest false false
      (inputs := #[⟨initial.regValue .rdi, data⟩]) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := false) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  have hm : message (#[⟨initial.regValue .rdi, data⟩] : Array Input) = data := by
    simp [message]
  have he := hResult.output.trans (congrArg Except.ok (Absorption.digestLanes_sha3_224
    (message #[⟨initial.regValue .rdi, data⟩])))
  change readDigestOutput sha3_224_digest initial final = _ at he
  rw [hm] at he
  exact he

theorem sha3_256_digest_writes_sha3_256_of_data[bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall sha3_256_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion sha3_256_digest initial,
          Stack.region initial sha3_256_digest.minStackBytes] ∧
      readDigestOutput sha3_256_digest initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_256 (SHA3.bytesToBits data))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha256 .digest initial #[⟨initial.regValue .rdi, data⟩] 0 false false :=
    ⟨data, rfl, hCall⟩
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha256 .digest false false
      (inputs := #[⟨initial.regValue .rdi, data⟩]) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := false) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  have hm : message (#[⟨initial.regValue .rdi, data⟩] : Array Input) = data := by
    simp [message]
  have he := hResult.output.trans (congrArg Except.ok (Absorption.digestLanes_sha3_256
    (message #[⟨initial.regValue .rdi, data⟩])))
  change readDigestOutput sha3_256_digest initial final = _ at he
  rw [hm] at he
  exact he

theorem sha3_384_digest_writes_sha3_384_of_data[bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall sha3_384_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion sha3_384_digest initial,
          Stack.region initial sha3_384_digest.minStackBytes] ∧
      readDigestOutput sha3_384_digest initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_384 (SHA3.bytesToBits data))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha384 .digest initial #[⟨initial.regValue .rdi, data⟩] 0 false false :=
    ⟨data, rfl, hCall⟩
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha384 .digest false false
      (inputs := #[⟨initial.regValue .rdi, data⟩]) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := false) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  have hm : message (#[⟨initial.regValue .rdi, data⟩] : Array Input) = data := by
    simp [message]
  have he := hResult.output.trans (congrArg Except.ok (Absorption.digestLanes_sha3_384
    (message #[⟨initial.regValue .rdi, data⟩])))
  change readDigestOutput sha3_384_digest initial final = _ at he
  rw [hm] at he
  exact he

theorem sha3_512_digest_writes_sha3_512_of_data[bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall sha3_512_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion sha3_512_digest initial,
          Stack.region initial sha3_512_digest.minStackBytes] ∧
      readDigestOutput sha3_512_digest initial final =
        .ok (SHA3.Digest.ofBits (SHA3.SHA3_512 (SHA3.bytesToBits data))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha512 .digest initial #[⟨initial.regValue .rdi, data⟩] 0 false false :=
    ⟨data, rfl, hCall⟩
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha512 .digest false false
      (inputs := #[⟨initial.regValue .rdi, data⟩]) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := false) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  have hm : message (#[⟨initial.regValue .rdi, data⟩] : Array Input) = data := by
    simp [message]
  have he := hResult.output.trans (congrArg Except.ok (Absorption.digestLanes_sha3_512
    (message #[⟨initial.regValue .rdi, data⟩])))
  change readDigestOutput sha3_512_digest initial final = _ at he
  rw [hm] at he
  exact he

theorem keccak224_digest_writes_keccak224_of_data[bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall keccak224_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion keccak224_digest initial,
          Stack.region initial keccak224_digest.minStackBytes] ∧
      readDigestOutput keccak224_digest initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak224 (SHA3.bytesToBits data))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha224 .digest initial #[⟨initial.regValue .rdi, data⟩] 0 true false :=
    ⟨data, rfl, hCall⟩
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha224 .digest true false
      (inputs := #[⟨initial.regValue .rdi, data⟩]) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := true) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  have hm : message (#[⟨initial.regValue .rdi, data⟩] : Array Input) = data := by
    simp [message]
  have he := hResult.output.trans (congrArg Except.ok (Absorption.digestLanes_keccak224
    (message #[⟨initial.regValue .rdi, data⟩])))
  change readDigestOutput keccak224_digest initial final = _ at he
  rw [hm] at he
  exact he

theorem keccak224_digest_slices_writes_keccak224_of_message[bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall keccak224_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion keccak224_digest_slices initial,
          Stack.region initial keccak224_digest_slices.minStackBytes] ∧
      readOutput keccak224_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak224 (SHA3.bytesToBits (message inputs)))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha224 .plain initial inputs 0 true false :=
    hCall
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha224 .plain true false
      (inputs := inputs) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := true) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  exact hResult.output.trans
    (congrArg Except.ok (Absorption.digestLanes_keccak224 (message inputs)))

theorem keccak256_digest_writes_keccak256_of_data[bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall keccak256_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion keccak256_digest initial,
          Stack.region initial keccak256_digest.minStackBytes] ∧
      readDigestOutput keccak256_digest initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak256 (SHA3.bytesToBits data))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha256 .digest initial #[⟨initial.regValue .rdi, data⟩] 0 true false :=
    ⟨data, rfl, hCall⟩
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha256 .digest true false
      (inputs := #[⟨initial.regValue .rdi, data⟩]) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := true) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  have hm : message (#[⟨initial.regValue .rdi, data⟩] : Array Input) = data := by
    simp [message]
  have he := hResult.output.trans (congrArg Except.ok (Absorption.digestLanes_keccak256
    (message #[⟨initial.regValue .rdi, data⟩])))
  change readDigestOutput keccak256_digest initial final = _ at he
  rw [hm] at he
  exact he

theorem keccak256_digest_slices_writes_keccak256_of_message[bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall keccak256_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion keccak256_digest_slices initial,
          Stack.region initial keccak256_digest_slices.minStackBytes] ∧
      readOutput keccak256_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak256 (SHA3.bytesToBits (message inputs)))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha256 .plain initial inputs 0 true false :=
    hCall
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha256 .plain true false
      (inputs := inputs) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := true) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  exact hResult.output.trans
    (congrArg Except.ok (Absorption.digestLanes_keccak256 (message inputs)))

theorem keccak384_digest_writes_keccak384_of_data[bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall keccak384_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion keccak384_digest initial,
          Stack.region initial keccak384_digest.minStackBytes] ∧
      readDigestOutput keccak384_digest initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak384 (SHA3.bytesToBits data))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha384 .digest initial #[⟨initial.regValue .rdi, data⟩] 0 true false :=
    ⟨data, rfl, hCall⟩
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha384 .digest true false
      (inputs := #[⟨initial.regValue .rdi, data⟩]) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := true) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  have hm : message (#[⟨initial.regValue .rdi, data⟩] : Array Input) = data := by
    simp [message]
  have he := hResult.output.trans (congrArg Except.ok (Absorption.digestLanes_keccak384
    (message #[⟨initial.regValue .rdi, data⟩])))
  change readDigestOutput keccak384_digest initial final = _ at he
  rw [hm] at he
  exact he

theorem keccak384_digest_slices_writes_keccak384_of_message[bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall keccak384_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion keccak384_digest_slices initial,
          Stack.region initial keccak384_digest_slices.minStackBytes] ∧
      readOutput keccak384_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak384 (SHA3.bytesToBits (message inputs)))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha384 .plain initial inputs 0 true false :=
    hCall
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha384 .plain true false
      (inputs := inputs) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := true) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  exact hResult.output.trans
    (congrArg Except.ok (Absorption.digestLanes_keccak384 (message inputs)))

theorem keccak512_digest_writes_keccak512_of_data[bindings : Machine.Bindings]
    {initial : Machine.RamState} {data : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidDigestCall keccak512_digest initial data) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[digestOutputRegion keccak512_digest initial,
          Stack.region initial keccak512_digest.minStackBytes] ∧
      readDigestOutput keccak512_digest initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak512 (SHA3.bytesToBits data))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha512 .digest initial #[⟨initial.regValue .rdi, data⟩] 0 true false :=
    ⟨data, rfl, hCall⟩
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha512 .digest true false
      (inputs := #[⟨initial.regValue .rdi, data⟩]) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := true) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  have hm : message (#[⟨initial.regValue .rdi, data⟩] : Array Input) = data := by
    simp [message]
  have he := hResult.output.trans (congrArg Except.ok (Absorption.digestLanes_keccak512
    (message #[⟨initial.regValue .rdi, data⟩])))
  change readDigestOutput keccak512_digest initial final = _ at he
  rw [hm] at he
  exact he

theorem keccak512_digest_slices_writes_keccak512_of_message[bindings : Machine.Bindings]
    {initial : Machine.RamState} {inputs : Array Input}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall keccak512_digest_slices initial inputs) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion keccak512_digest_slices initial,
          Stack.region initial keccak512_digest_slices.minStackBytes] ∧
      readOutput keccak512_digest_slices initial final =
        .ok (SHA3.Digest.ofBits (Keccak.keccak512 (SHA3.bytesToBits (message inputs)))) := by
  have hInvocation :
      Wrapper.ValidInvocation bindings .sha512 .plain initial inputs 0 true false :=
    hCall
  obtain ⟨fuel, final, hReturn, hResult⟩ :=
    Wrapper.execution_with_options .sha512 .plain true false
      (inputs := inputs) (split := 0) hMachine hBindings hInvocation
  have hBoundary := Wrapper.validInvocation_returnBoundary_with_options
    (keccak := true) (fullState := false)
    (machineRamUnitStrideDecodable_readyToStep hMachine hBindings) hInvocation
  obtain ⟨least, hUnique⟩ := Returns.unique_of_boundary hBoundary hReturn
  refine ⟨least, final, hUnique,
    ⟨hResult.invariant.ready.cpu, hResult.invariant.sse,
      hResult.invariant.ready.memory, hResult.invariant.ready.ready⟩,
    machineRamUnitStrideDecodable_of_ready hBindings.stringStride hResult.invariant.ready,
    hResult.saved, hResult.invariant.direction, hResult.invariant.frame, ?_⟩
  exact hResult.output.trans
    (congrArg Except.ok (Absorption.digestLanes_keccak512 (message inputs)))

end Sha3.Statements
