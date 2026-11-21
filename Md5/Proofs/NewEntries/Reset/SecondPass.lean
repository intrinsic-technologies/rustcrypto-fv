import Md5.Proofs.NewEntries.Reset.FirstPass
import Md5.Proofs.NewEntries.Reset.Restart

namespace Md5.Proofs.NewEntries.Reset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs Md5.Proofs.Streaming Md5.Proofs.Buffered

theorem second_pass [bindings : Bindings] {boundary : ReturnBoundary}
    {initial s : RamState} {inputs : Array Slices.Input} {first : Nat}
    (operations : LoopOperations .resetDiscardSecond boundary)
    (h : FirstPassPost initial inputs first s)
    (hCall : ResetThenDigest.ValidCall ResetThenDigest.updateResetSlices bindings initial inputs first)
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram boundary.rip) :
    ∃ fuel t, Advances boundary fuel s t ∧
      StreamingState .resetDiscardSecond initial
        (Slices.message (inputs.extract first inputs.size)) t ∧ t.RIP = 0x1015fd := by
  have hb := loopStorage_bounds h.storage hCall.stackAvailable
  have hregion := loopStorage_region h.storage hCall.stackAvailable
  have hContains : ∀ address, (Finalize.Kind.stackRegion .slices s).Contains address →
      (Stack.region initial ResetThenDigest.updateResetSlices.minStackBytes).Contains address := by
    intro address ha
    change (Stack.region initial (LoopKind.budget .resetDiscardFirst)).Contains address
    rw [hregion]
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + (312 + 376)
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + (320 + 280) at ha
    constructor <;> omega
  have hPre : ResetPre s := {
    stackLow := hb.1
    stackHigh := by
      have hh := hb.2
      change (stackPtr s).toNat + 280 < userAddressLimit
      change (stackPtr s).toNat + 312 + 56 < userAddressLimit at hh
      omega
    stackAligned := loopStorage_aligned h.storage hCall.stackAvailable
    stackAllocated := fun a ha ↦ Option.isSome_iff_exists.mp (h.grows a
      (Option.isSome_iff_exists.mpr (hCall.stackAvailable.2.1 a (hContains a.toNat ha))))
    stackAvoids := fun a ha ↦ (hCall.stackSeparation.2
      (Stack.region initial ResetThenDigest.updateResetSlices.minStackBytes) (by simp)).2
        a (hContains a.toNat ha)
    rip := h.rip
  }
  obtain ⟨n, u, t, hRun, ht, hCodeT, he, hAfter, hStorage, hAbsorbed⟩ :=
    reset_restart hOutside h.ready h.code hPre h.storage h.low h.high
  have hRsp : stackPtr t = stackPtr u :=
    hAfter.agrees.read (n := 64) (r := 4) (by simp)
  have hExt : t.external = u.external := hAfter.agrees.external (by simp [Component.Covers])
  have hIndex : (Operand.reg 12 : Operand 64).read t =
      BitVec.ofNat 64 (min first inputs.size) :=
    (hAfter.agrees.read (n := 64) (r := 12) (by simp)).trans
      ((he.agrees.read (n := 64) (r := 12)
        (by simp [resetEffect, Effect.components])).trans h.count)
  have hTotal : stackWord t 8 = BitVec.ofNat 64 inputs.size := by
    have hh := (reset_read he 8 (by decide) (by decide)).trans h.total
    simpa only [stackWord, hRsp, Operand.read, hExt, BitVec.ofNat_eq_ofNat] using hh
  have hSize : inputs.size < 2^64 := by
    have := validInputs_size_lt hCall.inputsInMemory
    omega
  have hTest : decide (((Operand.reg 12 : Operand 64).read s).toNat <
      ((Operand.reg 6 : Operand 64).read s).toNat) =
      decide (min first inputs.size < inputs.size) := by
    rw [h.count, h.totalRegister, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show min first inputs.size < 2^64 by omega), Nat.mod_eq_of_lt hSize]
  have hState : StreamingState .resetDiscardSecond initial ByteArray.empty t := by
    refine {
      storage := hStorage
      ready := ht
      code := hCodeT
      sse := SupportedSSE.of_agreesExcept hAfter.agrees
        (SupportedSSE.of_agreesExcept he.agrees h.sse)
      df := hAfter.agrees.directionFlagClear (by simp)
        (he.agrees.directionFlagClear (by simp [resetEffect, Effect.components]) h.df)
      absorbed := hAbsorbed
      grows := fun a ha ↦ hAfter.agrees.grow a (he.agrees.grow a (h.grows a ha))
      memoryFrame := ?_
    }
    have hResetFrame : MemoryWriteFrame s u
        #v[Stack.region initial ResetThenDigest.updateResetSlices.minStackBytes] := by
      intro a ha
      apply reset_frame hPre.toStorage he a
      intro region hr hin
      simp only [Vector.mem_singleton] at hr
      subst region
      exact ha _ (by simp) (hContains a.toNat hin)
    have hFrame := memoryWriteFrame_trans h.memoryFrame hResetFrame
    intro a ha
    rw [hExt]
    exact hFrame a ha
  by_cases hi : min first inputs.size < inputs.size
  · have hLoop : LoopInvariant .resetDiscardSecond initial inputs (min first inputs.size)
        inputs.size (min first inputs.size) t := by
      refine {
        toStreamingState := ?_
        rip := ?_
        indexValue := hIndex
        countValue := hTotal
        resetTotal := fun hh ↦ by rcases hh with hh | hh <;> cases hh
        secondRegisters := fun hh ↦ by rcases hh with hh | hh <;> cases hh
        discardSecondMemcpy := fun _ ↦ hAfter.memcpy (by rw [hTest]; simp only [decide_eq_true hi])
        discardTotal := fun hh ↦ by cases hh
      }
      · simpa [Array.extract_eq_empty_of_le, message_empty] using hState
      · simpa only [hTest, decide_eq_true hi, Bool.true_eq, ite_true,
          ite_eq_left hi, LoopKind.entry] using hAfter.rip
    obtain ⟨m, v, hLoopRun, hv, _⟩ := loop_complete operations hLoop
      hCall.inputsInMemory hCall.stackAvailable hCall.stackSeparation hStride hOutside
      (Nat.min_le_right ..) (Nat.le_refl _)
    refine ⟨n + m, v, hRun.trans hLoopRun, ?_, ?_⟩
    · simpa only [message_suffix_clamp] using hv.toStreamingState
    · simpa only [Nat.lt_irrefl, ite_false, LoopKind.finalPC] using hv.rip
  · have hsize : inputs.size ≤ first := by omega
    refine ⟨n, t, hRun, ?_, ?_⟩
    · simpa only [message_suffix_of_size_le inputs first hsize] using hState
    · simpa only [hTest, decide_eq_false hi, Bool.false_eq_true, ite_false] using hAfter.rip

end Md5.Proofs.NewEntries.Reset
