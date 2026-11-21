import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Positive.Prepare
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Positive.Finish

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem mixed_positive_run [Bindings] {initial : RamState} {input : List UInt8}
    {capacity : Nat} {boundary : ReturnBoundary}
    (hCall : MixedInternalCall initial input capacity boundary)
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hEven : input.length % 2 = 0) (hFit : input.length / 2 ≤ capacity)
    (hNonempty : input ≠ []) :
    ∃ fuel t, Returns boundary fuel initial t ∧ t.RIP = boundary.rip ∧
      stackPtr t = boundary.rsp ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      AgreesExcept (mixedCallChanges initial (input.length / 2) (mixedDecodeList input).isSome) initial t ∧
      t.regValue .rbx = initial.regValue .rbx ∧
      t.regValue .rbp = initial.regValue .rbp ∧
      t.regValue .r14 = initial.regValue .r14 ∧
      match mixedDecodeList input with
      | none => t.regValue .rax = 2
      | some output =>
          t.regValue .rax = 0 ∧
          (Operand.mem (initial.regValue .rdx) : Operand 64).read t =
            BitVec.ofNat 64 output.length ∧
          ∀ j (hj : j < output.length),
            t.external[initial.regValue .rcx + BitVec.ofNat 64 j]? = some output[j] := by
  obtain ⟨prefixFuel, u, hPrefix, hReadyU, hCodeU, hStart⟩ :=
    mixed_positive_start hCall hReady hCode hCall.returnOutside hEven hFit hNonempty
  obtain ⟨loopFuel, s, hLoopRun, hReadyS, hCodeS, hLoop⟩ :=
    mixed_loop_advances hReadyU hCodeU hCall.returnOutside hStart.pre hEven
  obtain ⟨tailFuel, final, hReturn, hRip, hRsp, hReadyFinal, hCodeFinal,
    hFrame, hRbx, hRbp, hR14, hResult⟩ :=
    mixed_positive_finish hCall hStart hLoop hReadyS hCodeS hFit
  exact ⟨prefixFuel + loopFuel + tailFuel, final,
    (hPrefix.trans hLoopRun).returns hReturn, hRip, hRsp,
    hReadyFinal, hCodeFinal, hFrame, hRbx, hRbp, hR14, hResult⟩

theorem mixed_internal_run [Bindings] {initial : RamState} {input : List UInt8}
    {capacity : Nat} {boundary : ReturnBoundary}
    (hCall : MixedInternalCall initial input capacity boundary)
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial) :
    ∃ fuel final, Returns boundary fuel initial final ∧ final.RIP = boundary.rip ∧
      stackPtr final = boundary.rsp ∧ ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      AgreesExcept (mixedCallChanges initial
        (if input.length % 2 ≠ 0 ∨ capacity < input.length / 2 then 0 else input.length / 2)
        (if input.length % 2 ≠ 0 ∨ capacity < input.length / 2 then false
          else (mixedDecodeList input).isSome))
        initial final ∧
      final.regValue .rbx = initial.regValue .rbx ∧
      final.regValue .rbp = initial.regValue .rbp ∧
      final.regValue .r14 = initial.regValue .r14 ∧
      if input.length % 2 ≠ 0 ∨ capacity < input.length / 2 then
        final.regValue .rax = 1
      else match mixedDecodeList input with
      | none => final.regValue .rax = 2
      | some output =>
          final.regValue .rax = 0 ∧
          (Operand.mem (initial.regValue .rdx) : Operand 64).read final =
            BitVec.ofNat 64 output.length ∧
          ∀ j (hj : j < output.length),
            final.external[initial.regValue .rcx + BitVec.ofNat 64 j]? = some output[j] := by
  by_cases hInvalid : input.length % 2 ≠ 0 ∨ capacity < input.length / 2
  · obtain ⟨fuel, final, hRun, hRip, hRsp, hReadyFinal, hCodeFinal,
      hFrame, hRbx, hRbp, hR14, hError⟩ :=
      mixed_length_error hCall hReady hCode (hInvalid := hInvalid)
    exact ⟨fuel, final, hRun, hRip, hRsp, hReadyFinal, hCodeFinal,
        by simpa only [hInvalid, ↓reduceIte] using hFrame,
      hRbx, hRbp, hR14, by simpa only [hInvalid, ↓reduceIte, BitVec.ofNat_eq_ofNat] using hError⟩
  · by_cases hEmpty : input = []
    · subst input
      obtain ⟨fuel, final, hRun, hRip, hRsp, hReadyFinal, hCodeFinal,
        hFrame, hRbx, hRbp, hR14, hLength, hStatus⟩ :=
        mixed_empty_return hCall hReady hCode
      refine ⟨fuel, final, hRun, hRip, hRsp, hReadyFinal, hCodeFinal, ?_, hRbx, hRbp, hR14, ?_⟩
      · simpa [mixedDecodeList_nil] using hFrame
      · simp only [hInvalid, ↓reduceIte, mixedDecodeList_nil, BitVec.ofNat_eq_ofNat]
        exact ⟨hStatus, hLength, fun j hj ↦ by simp only [List.length_nil] at hj; omega⟩
    · obtain ⟨fuel, final, hRun, hRip, hRsp, hReadyFinal, hCodeFinal,
        hFrame, hRbx, hRbp, hR14, hResult⟩ :=
        mixed_positive_run hCall hReady hCode (by omega) (by omega) hEmpty
      exact ⟨fuel, final, hRun, hRip, hRsp, hReadyFinal, hCodeFinal,
        by simpa only [hInvalid, ↓reduceIte] using hFrame,
        hRbx, hRbp, hR14, by simpa only [hInvalid, ↓reduceIte] using hResult⟩

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
