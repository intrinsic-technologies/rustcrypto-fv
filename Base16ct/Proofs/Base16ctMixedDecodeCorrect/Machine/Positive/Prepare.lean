import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Dispatch
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Prologue
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Positive.Interface
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Loop.Invariant

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores

structure MixedPositiveStart (initial : RamState) (input : List UInt8) (s : RamState) : Prop where
  pre : MixedLoopPre (initial.regValue .rdi) (initial.regValue .rcx) 0 input s
  accumulator : s.regValue .rsi = 0
  stack : stackPtr s = stackPtr initial - 24
  savedRbx : memLoad s.external (stackPtr initial - 24) 64 = initial.regValue .rbx
  savedR14 : memLoad s.external (stackPtr initial - 16) 64 = initial.regValue .r14
  savedRbp : memLoad s.external (stackPtr initial - 8) 64 = initial.regValue .rbp
  readable : MemReadable s (stackPtr initial - 24) 24
  frame : AgreesExcept [.reg 0, .reg 6, .reg 4, .reg 9, .flags, .rip,
    .mem (stackPtr initial - 24) 24] initial s

theorem MixedInternalCall.loop_pre {initial s : RamState} {input : List UInt8}
    {capacity : Nat} {boundary : ReturnBoundary}
    (h : MixedInternalCall initial input capacity boundary)
    (hFit : input.length / 2 ≤ capacity) (hNonempty : input ≠ [])
    (hFrame : AgreesExcept [.reg 0, .reg 6, .reg 4, .reg 9, .flags, .rip,
      .mem (stackPtr initial - 24) 24] initial s)
    (hRip : s.RIP = 0x1001f0)
    (hR9 : s.regValue .r9 = BitVec.ofNat 64 (input.length / 2))
    (hIndex : s.regValue .rax = 0) (hAcc : s.regValue .rsi = 0) :
    MixedLoopPre (initial.regValue .rdi) (initial.regValue .rcx) 0 input s := by
  refine ⟨?_, ?_, ?_, hIndex, ?_, ?_, .inl hAcc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [mixedLoopPC, hNonempty, ↓reduceIte] using hRip
  · have hb := h.inputBound
    omega
  · simpa only [Nat.zero_add] using hR9
  · exact hFrame.read (n := 64) (r := 7) (by simp)
  · exact hFrame.read (n := 64) (r := 1) (by simp)
  · simpa only [Nat.mul_zero, BitVec.add_zero] using readable_of_agrees h.source hFrame
  · intro j hj
    simp only [Nat.mul_zero, BitVec.add_zero]
    refine (hFrame.byte ?_).trans (h.bytes j hj)
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    obtain ⟨k, hk, he⟩ := hcov
    exact h.sourceStack j hj k hk he
  · simpa only [BitVec.add_zero] using writable_of_agrees
      (writable_sub h.output 0 (input.length / 2) (by simpa only [Nat.zero_add] using hFit)) hFrame
  · intro j hj
    simp only [BitVec.add_zero]
    exact h.outputAvoids j (by omega)
  · intro j hj k hk
    simp only [Nat.mul_zero, BitVec.add_zero]
    exact h.sourceOutput j hj k (by omega)


theorem mixed_prologue_frame {s t : RamState}
    (h : (mixedPrologueEffect s).Holds s t) :
    AgreesExcept [.reg 6, .reg 4, .reg 0, .flags, .rip,
      .mem (stackPtr s - 24) 24] s t := by
  have hf : AgreesExcept [.reg 4, .mem (stackPtr s - 8) 8,
      .mem (stackPtr s - 16) 8, .mem (stackPtr s - 24) 8,
      .reg 6, .reg 0, .flags, .rip] s t := by
    simpa [mixedPrologueEffect, Effect.components] using h.agrees
  apply hf.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem]
  · intro address c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    all_goals obtain ⟨j, hj, rfl⟩ := hcov
    · refine ⟨.mem (stackPtr s - 24) 24, by simp, 16 + j, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_right_inj]
      rw [← BitVec.add_assoc]
      rfl
    · refine ⟨.mem (stackPtr s - 24) 24, by simp, 8 + j, by omega, ?_⟩
      simp only [BitVec.ofNat_add, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_right_inj]
      rw [← BitVec.add_assoc]
      rfl
    · exact ⟨.mem (stackPtr s - 24) 24, by simp, j, by omega, rfl⟩

theorem mixed_positive_start [Bindings] {initial : RamState} {input : List UInt8}
    {capacity : Nat} {boundary outer : ReturnBoundary}
    (hCall : MixedInternalCall initial input capacity boundary)
    (hReady : ReadyToStep initial) (hCode : CodeIn Extracted.programImage initial)
    (hOutside : OutsideMixed outer.rip)
    (hEven : input.length % 2 = 0) (hFit : input.length / 2 ≤ capacity)
    (hNonempty : input ≠ []) :
    ∃ fuel s, Advances outer fuel initial s ∧ ReadyToStep s ∧
      CodeIn Extracted.programImage s ∧ MixedPositiveStart initial input s := by
  have hLengthNe : initial.regValue .rsi ≠ 0 := by
    intro hz
    have hLenZero := hCall.length.symm.trans (congrArg BitVec.toNat hz)
    exact hNonempty (List.length_eq_zero_iff.mp hLenZero)
  obtain ⟨fuel, a, runA, readyA, codeA, effectA⟩ :=
    mixed_entry outer hOutside initial hReady hCode hCall.rip
  have ripA : a.RIP = 0x1001e7 := by
    simpa only [mixedEntryEffect, mixedDispatchEffect, hCall.length, hCall.capacityArgument,
      hEven, hFit, hLengthNe, ↓reduceIte] using effectA.rip
  have r9A : a.regValue .r9 = BitVec.ofNat 64 (input.length / 2) := by
    have hx := effectA.writes.2
    change a.regValue .r9 =
      (if (initial.regValue .rsi).toNat % 2 = 0 then initial.regValue .rsi >>> 1
        else initial.regValue .r9) at hx
    rw [hCall.length, ite_eq_left hEven] at hx
    rw [hx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, hCall.length, Nat.shiftRight_eq_div_pow,
      Nat.reducePow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show input.length / 2 < 2 ^ 64 by have := hCall.inputBound; omega)]
  have frameA : AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial a := effectA.agrees
  have stackA : stackPtr a = stackPtr initial := frameA.read (n := 64) (r := 4) (by simp)
  have memoryA : a.external = initial.external := frameA.external (by simp [Component.Covers])
  have preA : MixedProloguePre a := by
    refine ⟨ripA, ?_, ?_, ?_, ?_⟩
    · rw [stackA]
      have hw := (hCall.stack_word 16 (by decide) (by decide)).of_external_eq memoryA
      simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw
    · rw [stackA]
      have hw := (hCall.stack_word 8 (by decide) (by decide)).of_external_eq memoryA
      simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc] using hw
    · rw [stackA]
      simpa only [BitVec.add_zero] using
        (hCall.stack_word 0 (by decide) (by decide)).of_external_eq memoryA
    · rw [stackA]
      exact hCall.stackAvoids
  obtain ⟨s, runS, readyS, codeS, effectS⟩ :=
    mixed_loop_prologue readyA codeA preA hOutside
  have frameS := mixed_prologue_frame effectS
  rw [stackA] at frameS
  have frame : AgreesExcept [.reg 0, .reg 6, .reg 4, .reg 9, .flags, .rip,
      .mem (stackPtr initial - 24) 24] initial s :=
    (frameA.trans frameS).mono (by simp [or_assoc, or_left_comm, or_comm])
  have stackS : stackPtr s = stackPtr initial - 24 := by
    have hs : stackPtr s = stackPtr a - 24 := effectS.writes.1
    rwa [stackA] at hs
  have accS : s.regValue .rsi = 0 := effectS.writes.2.2.2.2.1
  have indexS : s.regValue .rax = 0 := effectS.writes.2.2.2.2.2
  refine ⟨fuel + 6, s, runA.trans runS, readyS, codeS, ?_, accS, stackS, ?_, ?_, ?_, ?_, frame⟩
  · apply hCall.loop_pre hFit hNonempty frame effectS.rip _ indexS accS
    exact (frameS.read (n := 64) (r := 9) (by simp)).trans r9A
  · rw [← stackA]
    exact effectS.writes.2.2.2.1.trans (frameA.read (n := 64) (r := 3) (by simp))
  · rw [← stackA]
    exact effectS.writes.2.2.1.trans (frameA.read (n := 64) (r := 14) (by simp))
  · rw [← stackA]
    exact effectS.writes.2.1.trans (frameA.read (n := 64) (r := 5) (by simp))
  · exact Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.readable_of_agrees hCall.stack.readable frame

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
