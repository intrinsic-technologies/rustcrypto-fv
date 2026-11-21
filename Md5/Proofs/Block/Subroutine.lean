import Md5.Proofs.Block.Control
import Md5.Proofs.Block.Frame
import Md5.Proofs.Block.Empty
import Md5.Proofs.Block.Positive


namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compress_run [bindings : Bindings] (boundary : ReturnBoundary)
    {initial : RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hEntry : initial.RIP = 0x101ba0)
    (hInput : Call.Compress.ValidInput initial input)
    (hBuffer : Call.Compress.ValidBuffer initial buffer)
    (hStack : Stack.Valid initial Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation initial input)
    (hReturnLow : (returnBoundary initial).rip.toNat < userAddressLimit)
    (_hReturnOutside : OutsideCompression (returnBoundary initial).rip)
    (hBoundaryOutside : OutsideCompression boundary.rip) :
    ∃ (fuel : Nat) (final : RamState),
      (boundary = returnBoundary initial → Returns boundary fuel initial final) ∧
      (boundary.rip ≠ (returnBoundary initial).rip → Advances boundary fuel initial final) ∧
      final.RIP = (returnBoundary initial).rip ∧
      stackPtr final = (returnBoundary initial).rsp ∧
      ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      AgreesExcept (compressionComponents initial) initial final ∧
      Compress.readOutput initial final =
        .ok (Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input)).toBytes := by
  by_cases hZero : initial.regValue .rdx = 0
  · obtain ⟨final, hReturns, hAdvances, hReady', hCode', hFrame, hRip, hRsp⟩ :=
      compression_empty_run boundary hReady hCode hEntry hZero
        (stack_return_readable hStack) hReturnLow hBoundaryOutside
    refine ⟨3, final, hReturns, hAdvances, hRip, hRsp, hReady', hCode', ?_, ?_⟩
    · exact hFrame.mono (by simp [compressionComponents])
    · have hSize : input.size = 0 := by
        have hLength := hInput.2.1
        change 64 * (initial.regValue .rdx).toNat = input.size at hLength
        simpa [hZero] using hLength.symm
      have hWords : Standards.RFC.MD5.wordsOfBytes input = #[] := by
        apply Array.eq_empty_of_size_eq_zero
        rw [Md5.Proofs.RFC1321.size_wordsOfBytes, hSize]
      rw [hWords, Md5.Proofs.RFC1321.processBlocks_empty]
      exact compress_readOutput_of_external_eq hBuffer
        (hFrame.external (by simp [Component.Covers]))
  · obtain ⟨middle, hAdvance, hReady', hCode', hRip, hFrame⟩ :=
      compression_nonempty hReady hCode hEntry hZero hBoundaryOutside
    have hGpr : middle.GPR = initial.GPR := hFrame.gprUnchanged (by simp)
    have hMem : middle.external = initial.external := hFrame.external (by simp [Component.Covers])
    have hReg (r : Syntax.Reg) : middle.regValue r = initial.regValue r := by
      simp only [State.regValue, hGpr]
    have hInput' : Call.Compress.ValidInput middle input := by
      simpa only [Call.Compress.ValidInput, Compress.inputRegion, registerRegion, hReg, hMem] using hInput
    have hBuffer' : Call.Compress.ValidBuffer middle buffer := by
      simpa only [Call.Compress.ValidBuffer, Compress.outputRegion, registerRegion, hReg, hMem] using hBuffer
    have hStack' : Stack.Valid middle Compress.minStackBytes := by
      simpa only [Stack.Valid, Stack.region, Stack.NoUnderflow, Stack.returnSlot, hReg, hMem] using hStack
    have hSeparation' : Call.Compress.MemorySeparation middle input := by
      simpa only [Call.Compress.MemorySeparation, Compress.inputRegion, Compress.outputRegion,
        registerRegion, Stack.region, hReg] using hSeparation
    have hRet : returnBoundary middle = returnBoundary initial := by
      simp only [returnBoundary, stackPtr, Operand.read, hGpr, hMem]
    obtain ⟨fuel, final, hReturns, hAdvances, hFinalRip, hFinalRsp, hFinalReady,
        hFinalCode, hFinalFrame, hOutput⟩ :=
      compression_positive boundary hReady' hCode' hRip hInput' hBuffer' hStack' hSeparation'
        (by rwa [hReg]) (hRet ▸ hReturnLow) hBoundaryOutside
    rw [hRet] at hReturns hAdvances hFinalRip hFinalRsp
    have hComponents : compressionComponents middle = compressionComponents initial := by
      simp only [compressionComponents, Stack.region, hReg]
    rw [hComponents] at hFinalFrame
    refine ⟨2 + fuel, final, fun hb ↦ hAdvance.returns (hReturns hb),
      fun hb ↦ hAdvance.trans (hAdvances hb), hFinalRip, hFinalRsp, hFinalReady, hFinalCode, ?_, ?_⟩
    · exact (hFrame.trans hFinalFrame).mono (by simp [compressionComponents])
    · simpa only [Compress.readOutput, readRegion, Compress.outputRegion, registerRegion, hReg] using hOutput

theorem compress_subroutine [bindings : Bindings]
    {initial : RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hEntry : initial.RIP = 0x101ba0)
    (hInput : Call.Compress.ValidInput initial input)
    (hBuffer : Call.Compress.ValidBuffer initial buffer)
    (hStack : Stack.Valid initial Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation initial input)
    (hReturnLow : (returnBoundary initial).rip.toNat < userAddressLimit)
    (hReturnOutside : OutsideCompression (returnBoundary initial).rip) :
    ∃ (fuel : Nat) (final : RamState),
      Returns (returnBoundary initial) fuel initial final ∧
      ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      AgreesExcept (compressionComponents initial) initial final ∧
      Compress.readOutput initial final =
        .ok (Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input)).toBytes := by
  obtain ⟨fuel, final, hReturn, _, _, _, hReady', hCode', hAgrees, hOutput⟩ :=
    compress_run (returnBoundary initial) hReady hCode hEntry hInput hBuffer hStack hSeparation
      hReturnLow hReturnOutside hReturnOutside
  exact ⟨fuel, final, hReturn rfl, hReady', hCode', hAgrees, hOutput⟩

theorem compress_subroutine_advance [bindings : Bindings] (boundary : ReturnBoundary)
    {initial : RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hEntry : initial.RIP = 0x101ba0)
    (hInput : Call.Compress.ValidInput initial input)
    (hBuffer : Call.Compress.ValidBuffer initial buffer)
    (hStack : Stack.Valid initial Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation initial input)
    (hReturnLow : (returnBoundary initial).rip.toNat < userAddressLimit)
    (hReturnOutside : OutsideCompression (returnBoundary initial).rip)
    (hBoundaryOutside : OutsideCompression boundary.rip)
    (hDifferent : boundary.rip ≠ (returnBoundary initial).rip) :
    ∃ (fuel : Nat) (final : RamState),
      Advances boundary fuel initial final ∧
      final.RIP = (returnBoundary initial).rip ∧
      stackPtr final = (returnBoundary initial).rsp ∧
      ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      AgreesExcept (compressionComponents initial) initial final ∧
      Compress.readOutput initial final =
        .ok (Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input)).toBytes := by
  obtain ⟨fuel, final, _, hAdvance, hRip, hRsp, hReady', hCode', hAgrees, hOutput⟩ :=
    compress_run boundary hReady hCode hEntry hInput hBuffer hStack hSeparation
      hReturnLow hReturnOutside hBoundaryOutside
  exact ⟨fuel, final, hAdvance hDifferent, hRip, hRsp, hReady', hCode', hAgrees, hOutput⟩

end Md5.Proofs.Block
