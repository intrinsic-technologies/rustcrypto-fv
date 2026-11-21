import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Setup
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Outcome

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect

open Base16ct.Spec.Program Prelude X86

theorem readOutput_eq_of_bytes {initial final : Machine.RamState} {output : List UInt8}
    (hbytes : ∀ j (hj : j < output.length),
      final.external[initial.regValue .rcx + BitVec.ofNat 64 j]? = some output[j]) :
    readOutput initial final output.length = .ok output.toByteArray := by
  have hr : List.range output.length = (List.finRange output.length).map Fin.val := by
    apply List.ext_getElem <;> simp
  unfold readOutput
  simp only [outputRegion, registerRegion, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  rw [hr, List.mapM_map]
  simp only [Function.comp_def, hbytes _ (Fin.isLt _)]
  have hm : (List.finRange output.length).mapM
      (fun i ↦ Except.ok output[i.val]) = (Except.ok output : Except Machine.Fault (List UInt8)) := by
    change (List.finRange output.length).mapM
      (fun i ↦ pure output[i.val]) = (pure output : Except Machine.Fault (List UInt8))
    rw [List.mapM_pure]
    congr 1
    simp [List.finRange, Function.comp_def]
  rw [hm]
  change Except.ok (⟨output.toArray⟩ : ByteArray) = Except.ok output.toByteArray
  congr 1
  exact ByteArray.ext List.data_toByteArray.symm

end Base16ct.Proofs.Base16ctMixedDecodeCorrect

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem mixedCallChanges_frame {initial final : RamState} {input : ByteArray}
    {capacity written n : Nat} {lengthWritten : Prop} {writesLength : Bool}
    {regions : Vector MemoryRegion n}
    (hCall : ValidCall base16ctMixedDecode initial input capacity (input.size / 2) lengthWritten)
    (hFit : written ≤ capacity) (hLength : writesLength = true → lengthWritten)
    (h : AgreesExcept (mixedCallChanges initial written writesLength) initial final)
    (hOutput : written ≠ 0 → outputRegion initial written ∈ regions)
    (hStack : Stack.region initial base16ctMixedDecode.minStackBytes ∈ regions)
    (hLengthRegion : writesLength = true → lengthOutputRegion initial ∈ regions) :
    MemoryWriteFrame initial final regions := by
  apply h.memoryWriteFrame
  intro c hc address hcover
  simp only [mixedCallChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨outputRegion initial written, hOutput (by omega), ?_⟩
    have hb : (outputRegion initial written).Bounded := by
      have hb : (initial.regValue .rcx).toNat + capacity < userAddressLimit :=
        hCall.outputInMemory.2.1
      change (initial.regValue .rcx).toNat + written < userAddressLimit
      omega
    simpa only [outputRegion, registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      region_offset_contains hb hi
  · obtain ⟨i, hi, rfl⟩ := hcover
    cases hb : writesLength with
    | false => simp [hb] at hi
    | true =>
      simp only [hb, ite_true] at hi
      refine ⟨lengthOutputRegion initial, hLengthRegion hb, ?_⟩
      simpa only [lengthOutputRegion, registerRegion, BitVec.ofNat_toNat,
        BitVec.setWidth_eq] using
        region_offset_contains (hCall.lengthOutputInMemoryIfLengthWritten (hLength hb)).1 hi
  · obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨Stack.region initial base16ctMixedDecode.minStackBytes, hStack, ?_⟩
    obtain ⟨hs, he⟩ := Base16ct.Proofs.Copied.Md5.Proofs.Block.stack_subrange_bounds hCall.stack
      (used := 24) (by decide +kernel)
    exact Base16ct.Proofs.Copied.Md5.Proofs.Block.contains_offset_of_subrange hCall.stack.1 hs he i (by omega)

theorem finish_call [bindings : Bindings] {initial final : RamState} {input : ByteArray}
    {capacity written fuel : Nat} {lengthWritten : Prop} {writesLength : Bool}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall base16ctMixedDecode initial input capacity (input.size / 2) lengthWritten)
    (hReturn : Returns (returnBoundary initial) fuel initial final)
    (hReady : ReadyToStep final)
    (hFrame : AgreesExcept (mixedCallChanges initial written writesLength) initial final)
    (hRbx : final.regValue .rbx = initial.regValue .rbx)
    (hRbp : final.regValue .rbp = initial.regValue .rbp)
    (hR14 : final.regValue .r14 = initial.regValue .r14) :
    ∃ least, UniqueExecution initial least final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final := by
  have hEntry := entryReady hBindings hMachine hCall.programLoaded
  obtain ⟨least, hUnique⟩ := hReturn.unique_of_boundary
    (validCall_nearReturnBoundary hCall hEntry.ready)
  refine ⟨least, hUnique,
    Base16ct.Proofs.Copied.Md5.Proofs.supportedIntegerMachineState_of_ready hReady hFrame hMachine.sse,
    Base16ct.Proofs.Copied.Md5.Proofs.machineRamUnitStrideDecodable_of_ready hReady hBindings.stringStride,
    ?_, hFrame.directionFlagClear ?_ hCall.directionFlagUnset⟩
  · intro register hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRbx
    · exact hRbp
    · exact hFrame.read (r := 12) (n := 64) (by cases writesLength <;> simp [mixedCallChanges])
    · exact hFrame.read (r := 13) (n := 64) (by cases writesLength <;> simp [mixedCallChanges])
    · exact hR14
    · exact hFrame.read (r := 15) (n := 64) (by cases writesLength <;> simp [mixedCallChanges])
  · cases writesLength <;> simp [mixedCallChanges]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
