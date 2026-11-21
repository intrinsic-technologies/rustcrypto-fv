import Md5.Proofs.Streaming.Loop
import Md5.Proofs.NewEntries.FinalizeReset.Transition

namespace Md5.Proofs.NewEntries.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Buffered Streaming

theorem reset_second_absorb [bindings : Bindings] {boundary : ReturnBoundary}
    (operations : LoopOperations .finalizeResetSecond boundary) {initial s : RamState}
    {inputs : Array Slices.Input} {first : Nat}
    (h : StreamingState .finalizeResetSecond initial ByteArray.empty s)
    (hCall : (TwoMessages.ValidCall TwoMessages.finalizeIntoResetSlices) bindings initial inputs first)
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = 0x101019)
    (hIndex : (Operand.reg 5 : Operand 64).read s = BitVec.ofNat 64 (min first inputs.size))
    (hCount : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 inputs.size)
    (hTotal : stackWord s 192 = BitVec.ofNat 64 inputs.size) :
    ∃ fuel t, Advances boundary fuel s t ∧
      StreamingState .finalizeResetSecond initial (Slices.message (inputs.extract first inputs.size)) t ∧
      t.RIP = 0x101120 ∧
      MemoryWriteFrame s t #v[Stack.region initial TwoMessages.finalizeIntoResetSlices.minStackBytes] := by
  obtain ⟨n, t, hRun, hReady, hCode, ht⟩ := reset_transition_of_indices hOutside h.ready h.code
    hRip hIndex hCount (Nat.min_le_right ..)
    (by have := validInputs_size_lt hCall.inputsInMemory; omega)
  have htState : StreamingState .finalizeResetSecond initial ByteArray.empty t := by
    refine {
      storage := PrologueStorage.of_external_eq h.storage ht.rsp ht.memory
      ready := hReady
      code := hCode
      sse := SupportedSSE.of_agreesExcept ht.agrees h.sse
      df := ht.agrees.directionFlagClear (by simp) h.df
      absorbed := ?_
      grows := fun a ha ↦ ht.agrees.grow a (h.grows a ha)
      memoryFrame := ?_
    }
    · have hc : UpdateKind.finalizeResetSecond.context t = UpdateKind.finalizeResetSecond.context s := by
        simp only [UpdateKind.context, ht.rsp]
      rw [hc]
      exact absorbed_of_external_eq h.absorbed ht.memory
    · intro a ha
      rw [ht.memory]
      exact h.memoryFrame a ha
  have hFrame : MemoryWriteFrame s t #v[Stack.region initial TwoMessages.finalizeIntoResetSlices.minStackBytes] := by
    intro _ _
    rw [ht.memory]
  by_cases hi : min first inputs.size < inputs.size
  · have hLoop : LoopInvariant .finalizeResetSecond initial inputs (min first inputs.size)
        inputs.size (min first inputs.size) t := by
      refine {
        toStreamingState := ?_
        rip := ?_
        indexValue := ht.index.trans hIndex
        countValue := ?_
        resetTotal := fun hh ↦ by rcases hh with hh | hh <;> cases hh
        secondRegisters := ?_
        discardSecondMemcpy := fun hh ↦ by cases hh
        discardTotal := fun hh ↦ by cases hh
      }
      · simpa [Array.extract_eq_empty_of_le, message_empty] using htState
      · simpa only [decide_eq_true hi, Bool.true_eq, ite_true, ite_eq_left hi, LoopKind.entry]
          using ht.rip
      · simpa only [LoopKind.count, stackWord, ht.rsp, Operand.read, ht.memory] using hTotal
      · intro _
        refine ⟨?_, ht.memcpy (by simp [hi])⟩
        change (Operand.reg 3 : Operand 64).read t = stackPtr t + 8
        rw [ht.rsp]
        exact ht.context (by simp [hi])
    obtain ⟨m, u, hLoopRun, hu, hLoopFrame⟩ := loop_complete operations hLoop
      hCall.inputsInMemory hCall.stackAvailable hCall.separation hStride hOutside
      (Nat.min_le_right ..) (Nat.le_refl _)
    refine ⟨n + m, u, hRun.trans hLoopRun, ?_, ?_, memoryWriteFrame_trans hFrame hLoopFrame⟩
    · simpa only [message_suffix_clamp] using hu.toStreamingState
    · simpa [LoopKind.finalPC] using hu.rip
  · have hsize : inputs.size ≤ first := by omega
    refine ⟨n, t, hRun, ?_, ?_, hFrame⟩
    · simpa only [message_suffix_of_size_le inputs first hsize] using htState
    · simpa only [decide_eq_false hi, Bool.false_eq_true, ite_false] using ht.rip

end Md5.Proofs.NewEntries.FinalizeReset
