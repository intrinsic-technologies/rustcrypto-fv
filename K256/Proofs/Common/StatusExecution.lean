import K256.Proofs.Common.Finish
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Common

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift

theorem status_of_lifted_execution [bindings : Bindings] {initial : RamState}
    {routine : Routine} {inputs : List ByteArray} {args : List Nat} {accepted : Bool}
    {program : Lifted} {entry : program.Label} {out : Output Value Ram Reg.count}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall routine initial inputs args)
    (address : program.address entry = routine.entryAddress)
    (blocks : ∀ l, LiftedBlock Extracted.programImage program l)
    (live : ∀ r ∈ [0, 3, 4, 5, 12, 13, 14, 15, 22], Live program.retLive r)
    (exec : program.program.Exec (dialect Extracted.programImage)
      ⟨program.locationOf entry initial, []⟩ out)
    (returned : Returned initial #v[Stack.region initial routine.minStackBytes] out)
    (status : out.values[0] = ⟨64, if accepted then 0 else 1⟩) :
    ∃ (fuel : Nat) (final : RamState),
      UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      if accepted then
        SuccessfulStatus final ∧
        MemoryWriteFrame initial final #v[Stack.region initial routine.minStackBytes]
      else
        FailureStatus final signatureErrorStatus ∧
        MemoryWriteFrame initial final #v[Stack.region initial routine.minStackBytes] := by
  have ready := entryReady bindings hBindings hMachine hCall.programLoaded
  obtain ⟨ret, slot, _, outside⟩ := hCall.returnAddress
  have hret : (returnBoundary initial).rip = ret := Refine.memLoad_returnSlot slot
  have boundary : ReturnOutside (returnBoundary initial) Extracted.programImage := by
    intro x hx
    rw [hret]
    rintro rfl
    exact outside ⟨x.2, programSections_fetchByte_of_mem hx⟩
  obtain ⟨fuel, final, run, supported, decodable, writes, saved, df, _, eax⟩ :=
    run_of_lifted_execution hBindings
      (nearReturn64Boundary_eq initial ready.ready.dataReady hMachine.integer.ss
        (stack_return_readable hCall.stackAvailable))
      (Lifted.simulation blocks boundary)
      (Rel.locationOf (P := program) (l := entry) ready (hCall.atEntryPoint.trans address.symm))
      exec returned live
  refine ⟨fuel, final, run, supported, decodable, saved, df, ?_⟩
  cases accepted with
  | false =>
    have hv : final.regValue .rax = 1 := Value.eq_bits (eax.trans status)
    exact ⟨by simp only [FailureStatus, hv, signatureErrorStatus]; rfl, writes⟩
  | true =>
    have hv : final.regValue .rax = 0 := Value.eq_bits (eax.trans status)
    exact ⟨by simp only [SuccessfulStatus, hv]; rfl, writes⟩

end K256.Proofs.Common
