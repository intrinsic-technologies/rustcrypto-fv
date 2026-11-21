import Md5.Proofs.Block.Restore

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem memLoad_of_output_frame {s t : RamState} {stack output : BitVec 64}
    (hFrame : AgreesExcept [.reg 6, .mem output 16, .rip] s t)
    (hApart : RangeApart stack 192 output 16) (offset : Nat) (hEnd : offset + 8 ≤ 192) :
    memLoad t.external (stack + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stack + BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun byte : Option UInt8 ↦ byte.getD 0)
  apply hFrame.byte
  intro c hc hCov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact hCov.elim
  obtain ⟨j, hj, he⟩ := hCov
  apply hApart (offset + i) (by omega) j hj
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

theorem compression_positive [Bindings] (boundary : ReturnBoundary)
    {initial : RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hEntry : initial.RIP = 0x101ba9) (hInput : Call.Compress.ValidInput initial input)
    (hBuffer : Call.Compress.ValidBuffer initial buffer)
    (hStack : Stack.Valid initial Compress.minStackBytes)
    (hSeparation : Call.Compress.MemorySeparation initial input)
    (hNonzero : initial.regValue .rdx ≠ 0)
    (hReturnLow : (returnBoundary initial).rip.toNat < userAddressLimit)
    (hBoundary : OutsideCompression boundary.rip) :
    ∃ fuel final,
      (boundary = returnBoundary initial → Returns boundary fuel initial final) ∧
      (boundary.rip ≠ (returnBoundary initial).rip → Advances boundary fuel initial final) ∧
      final.RIP = (returnBoundary initial).rip ∧
      stackPtr final = (returnBoundary initial).rsp ∧
      ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      AgreesExcept (compressionComponents initial) initial final ∧
      Compress.readOutput initial final =
        .ok (Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input)).toBytes := by
  obtain ⟨fuel, prepared, mid, hBody, hMidReady, hMidCode, hMidRip, hRegisters, hMidRsp,
      hPrologue, hBlocksFrame⟩ :=
    compression_body hReady hCode hEntry hInput hBuffer hStack hSeparation hNonzero hBoundary
  have hBodyFrame := (prologue_compression_frame hStack hPrologue).trans
    (blocks_compression_frame hStack hBlocksFrame)
  have hFrameWrite : Memory.MemWritable mid (stackPtr initial - 184) 192 := by
    have hw := compression_stack_writable hStack hSeparation
    exact ⟨hw.low, fun i hi ↦ hBodyFrame.grow _ (hw.bytes i hi), hw.tables⟩
  have hOutputWrite : Memory.MemWritable mid (initial.regValue .rdi) 16 := by
    have hw := compression_output_writable hBuffer hSeparation
    exact ⟨hw.low, fun i hi ↦ hBodyFrame.grow _ (hw.bytes i hi), hw.tables⟩
  have hOutputAvoid : ∀ i < 16, ¬ InProgram (initial.regValue .rdi + BitVec.ofNat 64 i) := by
    intro i hi hProgram
    apply hSeparation.2 _ (by simp) _
      (contains_offset_of_subrange hBuffer.1 (Nat.le_refl _) (Nat.le_refl _) i hi)
    exact .inl hProgram
  have hPointer := blocks_output_pointer hPrologue hBlocksFrame
  have hRead : MemReadable mid (mid.regValue .rsp + 96) 8 := by
    rw [hMidRsp]
    exact MemoryRoutines.memReadable_slice hFrameWrite.readable 96 8 (by decide +kernel)
  obtain ⟨outputFuel, out, hOutput, hOutReady, hOutCode, hOutRip, _, hA, hB, hC, hD,
      hOutputFrame⟩ := compression_output hMidReady hMidCode hMidRip hRead
        (by rw [hMidRsp]; exact hPointer) hOutputWrite hOutputAvoid hRegisters hBoundary
  have hOutRsp : stackPtr out = stackPtr initial - 184 :=
    (hOutputFrame.read (n := 64) (r := 4) (by simp)).trans hMidRsp
  have hApart := compression_stack_output_apart hBuffer hStack hSeparation
  have hReturn : memLoad out.external (stackPtr out + 184) 64 = stackTop initial := by
    rw [hOutRsp]
    exact (memLoad_of_output_frame hOutputFrame hApart 184 (by decide +kernel)).trans
      (blocks_return_pointer hPrologue hBlocksFrame)
  have hSaved (i : Fin 6) :
      memLoad out.external (stackPtr out + BitVec.ofNat 64 (136 + 8 * i.val)) 64 =
        (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val]! : Operand 64).read initial := by
    rw [hOutRsp]
    exact (memLoad_of_output_frame hOutputFrame hApart (136 + 8 * i.val)
      (by have := i.isLt; omega)).trans (blocks_saved hPrologue hBlocksFrame i)
  have hEpilogueRead : MemReadable out (stackPtr out + 136) 56 := by
    rw [hOutRsp]
    have hr := MemoryRoutines.memReadable_slice hFrameWrite.readable 136 56 (by decide +kernel)
    exact ⟨hr.low, fun i hi ↦ hOutputFrame.grow _ (hr.mem i hi)⟩
  obtain ⟨returnFuel, beforeRet, final, hReturns, hAdvances, hFinalReady, hFinalCode,
      hEpilogue, hRet, hFinalRip, hFinalRsp⟩ :=
    compression_epilogue_return boundary hOutReady hOutCode ⟨hOutRip, hEpilogueRead⟩
      hBoundary (by
        change (memLoad out.external (stackPtr out + 184) 64).toNat < 2^32
        rw [hReturn]
        exact hReturnLow)
  have hFinalSaved (i : Fin 6) :
      (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val]! : Operand 64).read final =
        (Operand.reg (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[i.val]! : Operand 64).read initial := by
    have hn : ∀ j : Fin 6, (#[3, 12, 13, 14, 15, 5] : Array (BitVec 5))[j.val]! ≠ 4 := by
      decide +kernel
    exact (hRet.agrees.read (by
      simp only [retEffect_components, List.mem_cons, List.not_mem_nil, or_false]
      rintro (he | he)
      · exact hn i (Component.reg.inj he)
      · cases he)).trans
      ((epilogueEffect_saved hEpilogue i).trans (hSaved i))
  have hCallee : CalleeSavedRegistersUnchanged initial final := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hFinalSaved 0
    · exact hFinalSaved 5
    · exact hFinalSaved 1
    · exact hFinalSaved 2
    · exact hFinalSaved 3
    · exact hFinalSaved 4
  have hFullFrame : AgreesExcept (compressionWorkComponents initial) initial final := by
    apply (((hBodyFrame.trans hOutputFrame).trans hEpilogue.agrees).trans hRet.agrees).mono
    simp only [retEffect_components]
    simp [compressionWorkComponents, compressionComponents, epilogueEffect, Effect.components]
  have hMem : final.external = out.external :=
    (hEpilogue.agrees.trans hRet.agrees).external (by
      simp only [retEffect_components]
      simp [epilogueEffect, Effect.components, Component.Covers])
  have hRspReturn : stackPtr out + 192 = (returnBoundary initial).rsp := by
    rw [hOutRsp]
    change stackPtr initial - 184 + 192 = stackPtr initial + 8
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
  refine ⟨fuel + outputFuel + returnFuel, final, ?_, ?_, ?_, hFinalRsp.trans hRspReturn,
    hFinalReady, hFinalCode, compression_frame_of_restored hFullFrame hCallee, ?_⟩
  · intro hb
    apply (hBody.trans hOutput).returns
    apply hReturns
    constructor
    · rw [hb]
      exact hReturn.symm
    · rw [hb]
      exact hRspReturn.symm
  · intro hb
    apply (hBody.trans hOutput).trans
    apply hAdvances
    rwa [show (Operand.mem (stackPtr out + 184) : Operand 64).read out =
      (returnBoundary initial).rip from hReturn]
  · exact hFinalRip.trans hReturn
  · apply readOutput_of_bufferBytes
    all_goals rw [hMem]
    · exact hA
    · exact hB
    · exact hC
    · exact hD

end Md5.Proofs.Block
