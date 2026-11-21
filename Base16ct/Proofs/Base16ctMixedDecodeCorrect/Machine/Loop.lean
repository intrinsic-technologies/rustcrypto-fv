import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Loop.Step
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Loop.Decode

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs

structure MixedLoopResult (dst : BitVec 64) (index : Nat) (input : List UInt8)
    (s t : RamState) : Prop where
  rip : t.RIP = 0x1002ec
  rax : t.regValue .rax = BitVec.ofNat 64 (index + input.length / 2)
  accumulator : t.regValue .rsi = s.regValue .rsi ||| mixedLoopMarker input
  bytes : ∀ j (hj : j < (mixedLoopBytes input).length),
    t.external[dst + BitVec.ofNat 64 index + BitVec.ofNat 64 j]? =
      some (mixedLoopBytes input)[j]
  frame : AgreesExcept (mixedLoopChanges (dst + BitVec.ofNat 64 index) (input.length / 2)) s t

theorem mixed_loop_advances [Bindings] {boundary : ReturnBoundary} {src dst : BitVec 64}
    {index : Nat} {input : List UInt8} {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : OutsideMixed boundary.rip) (h : MixedLoopPre src dst index input s)
    (hEven : input.length % 2 = 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      MixedLoopResult dst index input s t := by
  induction input using mixedDecodeList.induct generalizing index s with
  | case1 =>
      refine ⟨0, s, (advances_zero _ _ _).mpr rfl, hReady, hCode, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, AgreesExcept.refl _ _⟩
      · simpa [mixedLoopPC] using h.rip
      · simpa only [List.length_nil, Nat.zero_div, Nat.add_zero] using h.rax
      · simp only [mixedLoopMarker_nil, BitVec.ofNat_eq_ofNat, BitVec.or_zero]
      · intro j hj
        simp only [mixedLoopBytes_nil, List.length_nil] at hj
        omega
  | case2 c => simp only [List.length_cons, List.length_nil] at hEven; omega
  | case3 hi lo input ih =>
      have hTailEven : input.length % 2 = 0 := by
        simp only [List.length_cons] at hEven
        omega
      have hLength : (hi :: lo :: input).length / 2 = input.length / 2 + 1 := by
        simp only [List.length_cons]
        omega
      obtain ⟨firstFuel, u, hFirst, hReadyU, hCodeU, hNext, hAccumulatorU, hByteU, hFrameU⟩ :=
        mixedLoopStep hReady hCode hOutside h hTailEven
      obtain ⟨restFuel, t, hRest, hReadyT, hCodeT, hResult⟩ :=
        ih hReadyU hCodeU hNext hTailEven
      refine ⟨firstFuel + restFuel, t, hFirst.trans hRest, hReadyT, hCodeT,
        hResult.rip, ?_, ?_, ?_, ?_⟩
      · rw [hResult.rax, hLength]
        congr 1
        omega
      · rw [hResult.accumulator, hAccumulatorU, mixedLoopMarker_cons_cons, BitVec.or_assoc]
      · intro j hj
        simp only [mixedLoopBytes_cons_cons, List.length_cons] at hj
        cases j with
        | zero =>
            simp only [mixedLoopBytes_cons_cons, List.getElem_cons_zero, BitVec.add_zero]
            have hFrameRest : AgreesExcept
                (mixedLoopChanges ((dst + BitVec.ofNat 64 index) + 1#64)
                  (input.length / 2)) u t := by
              simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hResult.frame
            exact (mixedLoopChanges_preserve_head hFrameRest
              (by have hb := h.lengthBound; rw [hLength] at hb; omega)).trans hByteU
        | succ j =>
            have hj' : j < (mixedLoopBytes input).length := by omega
            have hb := hResult.bytes j hj'
            simpa only [mixedLoopBytes_cons_cons, List.getElem_cons_succ,
              Nat.succ_eq_add_one, BitVec.add_assoc, ← BitVec.ofNat_add,
              Nat.add_assoc, Nat.add_comm 1 j] using hb
      · have hFrameRest : AgreesExcept
            (mixedLoopChanges ((dst + BitVec.ofNat 64 index) + 1#64)
              (input.length / 2)) u t := by
          simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hResult.frame
        rw [hLength]
        exact mixedLoopChanges_trans hFrameU hFrameRest

theorem MixedLoopResult.accumulator_eq_zero_iff {dst : BitVec 64} {index : Nat}
    {input : List UInt8} {s t : RamState} (h : MixedLoopResult dst index input s t) :
    t.regValue .rsi = 0 ↔ s.regValue .rsi = 0 ∧ (mixedDecodeList input).isSome := by
  have hor : s.regValue .rsi ||| mixedLoopMarker input = 0 ↔
      s.regValue .rsi = 0 ∧ mixedLoopMarker input = 0 := BitVec.or_eq_zero_iff
  rw [h.accumulator, hor, mixedLoopMarker_eq_zero_iff]


theorem MixedLoopResult.accumulator_cases {dst : BitVec 64} {index : Nat}
    {input : List UInt8} {s t : RamState} (h : MixedLoopResult dst index input s t)
    (hAcc : s.regValue .rsi = 0 ∨ s.regValue .rsi = 255) :
    t.regValue .rsi = 0 ∨ t.regValue .rsi = 255 := by
  rw [h.accumulator]
  rcases hAcc with ha | ha <;>
    rcases mixedLoopMarker_eq_zero_or input with hm | hm <;> rw [ha, hm] <;> decide +kernel

theorem MixedLoopResult.bytes_of_decode {dst : BitVec 64} {index : Nat}
    {input output : List UInt8} {s t : RamState} (h : MixedLoopResult dst index input s t)
    (hDecode : mixedDecodeList input = some output) :
    ∀ j (hj : j < output.length),
      t.external[dst + BitVec.ofNat 64 index + BitVec.ofNat 64 j]? = some output[j] := by
  have he := mixedLoopBytes_eq_of_decode hDecode
  simpa only [he] using h.bytes

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
