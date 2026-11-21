import K256.Proofs.Common.Finish
import K256.Proofs.Common.Output
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Generate

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Common

theorem ofExecution [bindings : Bindings] {initial : RamState} {random : ByteArray}
    {program : Lifted} {entry : program.Label} {out : Output Value Ram Reg.count}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signingKeyGenerateFromRng initial [random])
    (address : program.address entry = signingKeyGenerateFromRng.entryAddress)
    (blocks : ∀ l, LiftedBlock Extracted.programImage program l)
    (live : ∀ r ∈ [0, 3, 4, 5, 12, 13, 14, 15, 22], Live program.retLive r)
    (exec : program.program.Exec (dialect Extracted.programImage)
      ⟨program.locationOf entry initial, []⟩ out)
    (returned : Returned initial #v[outputRegion signingKeyGenerateFromRng initial,
      Stack.region initial signingKeyGenerateFromRng.minStackBytes] out)
    (bytes : (outputRegion signingKeyGenerateFromRng initial).HasBytes out.store
      (Secp256k1.generatedSigningKey random)) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[outputRegion signingKeyGenerateFromRng initial,
          Stack.region initial signingKeyGenerateFromRng.minStackBytes] ∧
      readOutput signingKeyGenerateFromRng initial final =
        .ok (Secp256k1.generatedSigningKey random) := by
  have ready := entryReady bindings hBindings hMachine hCall.programLoaded
  obtain ⟨ret, slot, _, outside⟩ := hCall.returnAddress
  have hret : (returnBoundary initial).rip = ret := Refine.memLoad_returnSlot slot
  have boundary : ReturnOutside (returnBoundary initial) Extracted.programImage := by
    intro x hx
    rw [hret]
    rintro rfl
    exact outside ⟨x.2, programSections_fetchByte_of_mem hx⟩
  obtain ⟨fuel, final, run, supported, decodable, writes, saved, df, mem, _⟩ :=
    run_of_lifted_execution hBindings
      (nearReturn64Boundary_eq initial ready.ready.dataReady hMachine.integer.ss
        (stack_return_readable hCall.stackAvailable))
      (Lifted.simulation blocks boundary)
      (Rel.locationOf (P := program) (l := entry) ready (hCall.atEntryPoint.trans address.symm))
      exec returned live
  exact ⟨fuel, final, run, supported, decodable, saved, df, writes,
    readRegion_of_hasBytes (mem ▸ bytes)⟩

end K256.Proofs.Generate
