import Md5.Proofs.Block.Subroutine


namespace Md5.Statements

open Md5.Spec Md5.Spec.Program Md5.Proofs Md5.Proofs.Block Prelude X86 X86Proofs

theorem md5_compress_writes_buffer_after_blocks
    {initial : Machine.RamState} {buffer : Standards.RFC.MD5.Buffer} {blocks : ByteArray}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Compress.ValidCall bindings initial buffer blocks) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final
        #v[Compress.outputRegion initial, Stack.region initial Compress.minStackBytes] ∧
      Compress.readOutput initial final =
        .ok (Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes blocks)).toBytes := by
  letI := bindings
  have hEntry := entryReady bindings hBindings hMachine hCall.programLoaded
  have hReadable := stack_return_readable hCall.stackAvailable
  have hBoundary := nearReturn64Boundary_eq initial hEntry.ready.dataReady
    hMachine.integer.ss hReadable
  obtain ⟨boundary, hBoundary', hLow, hOutside⟩ := hCall.returnAddress
  have hEq : boundary = returnBoundary initial := Except.ok.inj (hBoundary'.symm.trans hBoundary)
  subst boundary
  have hNot : OutsideCompression (returnBoundary initial).rip :=
    outsideCompression_of_not_inProgram hOutside
  obtain ⟨middle, hAdvance, hReady, hJump⟩ := compress_jump hEntry.ready hEntry.code
    hCall.atEntryPoint (outsideCompression_ne hNot (by decide) (by decide))
  have hCode := hJump.codeIn (jmpEffect_avoids _ _ _ _) hEntry.code
  have hGpr : middle.GPR = initial.GPR :=
    hJump.gprUnchanged (by intro r; simp [jmpEffect_components])
  have hMem : middle.external = initial.external :=
    hJump.agrees.external (by simp [jmpEffect_components, Component.Covers])
  have hReg (r : Syntax.Reg) : middle.regValue r = initial.regValue r := by
    simp only [State.regValue, hGpr]
  have hInput : Call.Compress.ValidInput middle blocks := by
    simpa only [Call.Compress.ValidInput, Compress.inputRegion, registerRegion, hReg, hMem]
      using (show Call.Compress.ValidInput initial blocks from
        ⟨hCall.inputInMemory.2.1, hCall.blockCountArgumentMatchesBlocks, hCall.inputInMemory.2.2⟩)
  have hBuffer : Call.Compress.ValidBuffer middle buffer := by
    simpa only [Call.Compress.ValidBuffer, Compress.outputRegion, registerRegion, hReg, hMem]
      using (show Call.Compress.ValidBuffer initial buffer from hCall.outputInMemory.2)
  have hStack : Stack.Valid middle Compress.minStackBytes := by
    simpa only [Stack.Valid, Stack.region, Stack.NoUnderflow, Stack.returnSlot, hReg, hMem]
      using hCall.stackAvailable
  have hSeparation : Call.Compress.MemorySeparation middle blocks := by
    simpa only [Call.Compress.MemorySeparation, Compress.inputRegion, Compress.outputRegion,
      registerRegion, Stack.region, hReg] using
      (show Call.Compress.MemorySeparation initial blocks from Call.separation_pair hCall.separation)
  have hRet : returnBoundary middle = returnBoundary initial := by
    simp only [returnBoundary, stackPtr, Operand.read, hGpr, hMem]
  obtain ⟨fuel, final, hReturns, hFinalReady, _, hAgrees, hOutput⟩ :=
    compress_subroutine hReady hCode hJump.rip hInput hBuffer hStack hSeparation
      (hRet ▸ hLow) (hRet ▸ hNot)
  have hFullAgrees : AgreesExcept (compressionComponents initial) initial final := by
    have hComponents : compressionComponents middle = compressionComponents initial := by
      simp only [compressionComponents, Stack.region, hReg]
    rw [hComponents] at hAgrees
    apply (hJump.agrees.trans hAgrees).mono
    intro c hc
    simp only [jmpEffect_components, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | hc
    · simp [compressionComponents]
    · exact hc
  rw [hRet] at hReturns
  obtain ⟨least, hUnique⟩ := (hAdvance.returns hReturns).unique_of_boundary hBoundary
  refine ⟨least, final, hUnique,
    supportedIntegerMachineState_of_ready hFinalReady hFullAgrees hMachine.sse,
    machineRamUnitStrideDecodable_of_ready hFinalReady hBindings.stringStride,
    compression_calleeSaved hFullAgrees,
    hFullAgrees.directionFlagClear (by simp [compressionComponents]) hCall.directionFlagUnset,
    compression_memoryWriteFrame hFullAgrees hCall.outputInMemory.2.1 hCall.stackAvailable.1, ?_⟩
  simpa only [Compress.readOutput, readRegion, Compress.outputRegion, registerRegion, hReg] using hOutput

end Md5.Statements
