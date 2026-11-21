import Md5.Proofs.NewEntries.Reset.Start
import Md5.Proofs.NewEntries.Reset.BeforeReset

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Streaming Md5.Proofs.Block

structure FirstPassPost [Bindings] (initial : RamState) (inputs : Array Slices.Input)
    (first : Nat) (s : RamState) : Prop extends
    StreamingState .resetDiscardFirst initial (Slices.message (inputs.extract 0 first)) s where
  rip : s.RIP = 0x1014e0
  count : (Operand.reg 12 : Operand 64).read s = BitVec.ofNat 64 (min first inputs.size)
  total : stackWord s 8 = BitVec.ofNat 64 inputs.size
  totalRegister : (Operand.reg 6 : Operand 64).read s = BitVec.ofNat 64 inputs.size
  low : (Operand.reg 7 : Operand 64).read s = 0xefcdab8967452301
  high : (Operand.reg 2 : Operand 64).read s = 0x1032547698badcfe

theorem first_pass [bindings : Bindings] {boundary : ReturnBoundary}
    (operations : LoopOperations .resetDiscardFirst boundary) {initial : RamState}
    {inputs : Array Slices.Input} {first : Nat} (hReady : ReadyToStep initial)
    (hCode : CodeIn Extracted.programImage initial)
    (hSse : SupportedSSE bindings.processor initial) (hStride : UnitStringStride bindings)
    (hCall : ResetThenDigest.ValidCall ResetThenDigest.updateResetSlices bindings initial inputs first)
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel s, Advances boundary fuel initial s ∧ FirstPassPost initial inputs first s := by
  obtain ⟨n, s, hPrologue, hs, hCodeS, hp⟩ :=
    reset_prologue_of_ready boundary hReady hCode hCall hOutside
  by_cases hEmpty : min first inputs.size = 0
  · have hMessage : Slices.message (inputs.extract 0 first) = ByteArray.empty := by
      rw [← message_prefix_clamp, hEmpty, Array.extract_eq_empty_of_le (Nat.zero_le _),
        message_empty]
    refine ⟨n, s, hPrologue, ?_⟩
    refine {
      toStreamingState := ?_
      rip := by simpa only [hEmpty, ite_true] using hp.rip
      count := hp.count
      total := hp.total
      totalRegister := (hp.empty hEmpty).2.2
      low := (hp.empty hEmpty).2.1
      high := (hp.empty hEmpty).1
    }
    rw [hMessage]
    exact prologue_streaming_state hp hs hCodeS hSse hCall.directionFlagUnset
  · have hi := first_loop_initial hp hs hCodeS hSse hCall.directionFlagUnset hEmpty
    obtain ⟨m, t, hLoop, ht, _⟩ := loop_complete operations hi hCall.inputsInMemory
      hCall.stackAvailable hCall.stackSeparation hStride hOutside (Nat.zero_le _)
      (Nat.min_le_right _ _)
    have hState : StreamingState .resetDiscardFirst initial
        (Slices.message (inputs.extract 0 first)) t := by
      simpa only [message_prefix_clamp] using ht.toStreamingState
    have hRip : t.RIP = 0x1014c7 := by
      simpa only [Nat.lt_irrefl, ite_false, LoopKind.finalPC] using ht.rip
    obtain ⟨k, u, hBefore, hu, _, he⟩ := before_reset boundary hOutside t ht.ready
      (program_text_slice ht.code 0x14c7 25 (by decide +kernel))
      ⟨hRip, loopStorage_readable ht.storage hCall.stackAvailable ht.grows 8 8 (by decide)⟩
    have hRsp : stackPtr u = stackPtr t := he.agrees.read (n := 64) (r := 4)
      (by simp [beforeResetEffect, Effect.components])
    have hExt : u.external = t.external := he.agrees.external
      (by simp [beforeResetEffect, Effect.components, Component.Covers])
    have hCodeU := he.agrees.codeIn
      (by simp [beforeResetEffect, Effect.components, Component.Covers]) ht.code
    refine ⟨n + m + k, u, (hPrologue.trans hLoop).trans hBefore, ?_⟩
    refine {
      toStreamingState := ?_
      rip := he.rip
      count := ?_
      total := ?_
      totalRegister := he.writes.1.trans (ht.discardTotal rfl)
      low := he.writes.2.2
      high := he.writes.2.1
    }
    · refine ⟨ht.storage.of_external_eq hRsp hExt, hu, hCodeU,
        SupportedSSE.of_agreesExcept he.agrees ht.sse,
        he.agrees.directionFlagClear (by simp [beforeResetEffect, Effect.components]) ht.df,
        ?_, ?_, ?_⟩
      · have hc : Buffered.UpdateKind.context .resetDiscardFirst u =
            Buffered.UpdateKind.context .resetDiscardFirst t := by
          simp only [Buffered.UpdateKind.context, hRsp]
        rw [hc]
        exact absorbed_of_external_eq hState.absorbed hExt
      · exact fun address ha ↦ he.agrees.grow address (ht.grows address ha)
      · intro address ha
        rw [hExt]
        exact ht.memoryFrame address ha
    · exact (he.agrees.read (n := 64) (r := 12)
        (by simp [beforeResetEffect, Effect.components])).trans ht.countValue
    · simpa only [stackWord, hRsp, Operand.read, hExt] using ht.discardTotal rfl

end Md5.Proofs.NewEntries.Reset
