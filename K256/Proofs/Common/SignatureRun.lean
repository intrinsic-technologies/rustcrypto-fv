import K256.Proofs.SignatureSlice
import K256.Proofs.Common.Output
import K256.Proofs.Common.SignatureEncoding
import K256.Proofs.Common.Finish
import K256.Proofs.LIR
import K256.Proofs.LIR.SignatureFromSlice.Frame

namespace K256.Proofs.Common

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.LIR

theorem fnCode_subset_programImage : ∀ x ∈ fnCode, x ∈ Extracted.programImage := by
  intro x hx
  apply List.mem_flatMap.mpr
  refine ⟨textSection, by simp [Extracted.programSections, textSection], ?_⟩
  simpa only [fnCode, sections, ImageSections.toCodeMap, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] using hx

theorem signatureFramePre {initial : RamState} {bytes : ByteArray} {ret : BitVec 64}
    (hCall : ValidCall signatureFromSlice initial [bytes])
    (hret : memLoad initial.external (initial.regValue .rsp) 64 = ret)
    (hlow : ret.toNat < userAddressLimit) (hout : ¬ InProgram ret) :
    SignatureFromSlice.Pre Extracted.programImage
      (Activation.ofEntry initial signatureFromSlice.minStackBytes ret) initial := by
  let forbidden := fun a : BitVec 64 => InProgram a ∨ pageTables.Contains a.toNat
  have hs : Stack.region initial signatureFromSlice.minStackBytes ∈
      writtenRegions signatureFromSlice initial := by simp [writtenRegions, signatureFromSlice]
  have hr : rodataSection ∈ Extracted.programSections := by
    simp [Extracted.programSections, rodataSection]
  apply FrameInfo.Pre.of_sysV (forbidden := forbidden)
  · exact hCall.atEntryPoint
  · exact hCall.stackAvailable
  · decide
  · exact (hCall.separation.2 _ hs).1
  · exact fun x hx => Or.inl ⟨x.2, programSections_fetchByte_of_mem hx⟩
  · intro b hb
    have h := not_pageTableEntriesApart_frames hb
    exact Or.inr (contains_iff.mpr (by simp only [pageTables]; omega))
  · exact hret
  · exact hlow
  · rintro x hx rfl
    exact hout ⟨x.2, programSections_fetchByte_of_mem hx⟩
  · apply SignatureFromSlice.callSlots_loaded hr
    exact fun x hx => hCall.programLoaded x.1 x.2 (programSections_fetchByte_of_mem hx)
  · intro _ a h₁ h₂
    obtain ⟨b, hb⟩ := SignatureFromSlice.callSlots_span hr a h₁ h₂
    exact Or.inl ⟨b, programSections_fetchByte_of_mem hb⟩
  · exact hCall.directionFlagUnset

theorem signatureRun [bindings : Bindings] {initial : RamState} {bytes : ByteArray}
    {n : Nat} {regions : Vector MemoryRegion n} {output : Output Value Ram Reg.count}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signatureFromSlice initial [bytes])
    (hexec : lifted.program.Exec (dialect Extracted.programImage)
      ⟨lifted.locationOf .l102450 initial, []⟩ output)
    (hpost : Returned initial regions output) :
    ∃ fuel final, UniqueExecution initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      MemoryWriteFrame initial final regions ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      final.external = output.store ∧ (Reg.ofIndex 0).read final = output.values[0] := by
  have he := entryReady bindings hBindings hMachine hCall.programLoaded
  obtain ⟨ret, slot, low, outside⟩ := hCall.returnAddress
  have hp := signatureFramePre hCall (memLoad_returnSlot slot) low outside
  have hboundary : ReturnOutside (returnBoundary initial) Extracted.programImage := by
    intro x hx
    rw [hp.returnBoundary.1]
    exact hp.retOutside x hx
  apply run_of_lifted_execution hBindings
    (nearReturn64Boundary_eq initial he.ready.dataReady hMachine.integer.ss
      (stack_return_readable hCall.stackAvailable))
    (LIR.simulation hBindings.stringStride _ fnCode_subset_programImage hboundary)
    (Rel.locationOf (P := lifted) (l := .l102450) he hCall.atEntryPoint) hexec hpost
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section

open K256.Spec

variable [bindings : Bindings] {initial : RamState} {bytes : ByteArray}
  {output : Output Value Ram Reg.count}
  (hBindings : MachineRamUnitStrideDecodable bindings initial)
  (hMachine : SupportedIntegerMachineState bindings.processor initial)
  (hCall : ValidCall signatureFromSlice initial [bytes])
  (hexec : lifted.program.Exec (dialect Extracted.programImage)
    ⟨lifted.locationOf .l102450 initial, []⟩ output)

include hBindings hMachine hCall hexec

theorem signatureSliceRejected
    (hpost : Returned initial #v[Stack.region initial signatureFromSlice.minStackBytes] output)
    (hstatus : output.values[0] = ⟨64, 1⟩) (hmodel : Ecdsa.signatureScalars bytes = none) :
    SignatureSliceResult initial bytes := by
  obtain ⟨fuel, final, run, supported, decodable, frame, saved, df, _, eax⟩ :=
    signatureRun hBindings hMachine hCall hexec hpost
  refine ⟨fuel, final, run, supported, decodable, saved, df, ?_⟩
  rw [hmodel]
  have hv : final.regValue .rax = 1 := Value.eq_bits (eax.trans hstatus)
  exact ⟨by simp only [FailureStatus, hv, signatureErrorStatus]; rfl, frame⟩

theorem signatureSliceAccepted {r s : Nat}
    (hpost : Returned initial #v[outputRegion signatureFromSlice initial,
      Stack.region initial signatureFromSlice.minStackBytes] output)
    (hstatus : output.values[0] = ⟨64, 0⟩)
    (hbytes : (outputRegion signatureFromSlice initial).HasBytes output.store bytes)
    (hmodel : Ecdsa.signatureScalars bytes = some (r, s)) : SignatureSliceResult initial bytes := by
  obtain ⟨fuel, final, run, supported, decodable, frame, saved, df, mem, eax⟩ :=
    signatureRun hBindings hMachine hCall hexec hpost
  refine ⟨fuel, final, run, supported, decodable, saved, df, ?_⟩
  simp only [hmodel, signatureBytes_of_signatureScalars hmodel]
  have hv : final.regValue .rax = 0 := Value.eq_bits (eax.trans hstatus)
  exact ⟨by simp only [SuccessfulStatus, hv]; rfl, frame, readRegion_of_hasBytes (mem ▸ hbytes)⟩

end

end K256.Proofs.Common
