import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Frame
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstTop

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initialize_frame {p : BitVec 64} {s t : RamState}
    (h : (initializeEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  have hc : (initializeEffect p s).components =
      [.reg 14#5, .reg 9#5, .reg 2#5, .reg 10#5, .reg 15#5, .reg 11#5, .mem (stackPtr s+80#64) 8, .mem (stackPtr s+24#64) 8, .mem (stackPtr s+72#64) 8, .mem (stackPtr s+16#64) 8, .mem (stackPtr s+32#64) 8, .rip] := by simp [initializeEffect, Effect.components, Write.component, Operand.component] <;> rfl
  have ag := h.agrees
  rw [hc] at ag
  apply P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.agrees_of_footprint ag
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Reduction.scratchComponents, Component.isMem]
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 80) (len := 8) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 24) (len := 8) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 72) (len := 8) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 16) (len := 8) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 32) (len := 8) (by decide) ha⟩

theorem firstProducts_frame {p : BitVec 64} {s t : RamState}
    (h : (firstProductsEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  have hc : (firstProductsEffect p s).components =
      [.reg 0#5, .reg 2#5, .reg 6#5, .reg 3#5, .reg 14#5, .reg 12#5, .reg 13#5, .reg 15#5, .reg 8#5, .flags, .rip] := by simp [firstProductsEffect, Effect.components, Write.component, Operand.component] <;> rfl
  have ag := h.agrees
  rw [hc] at ag
  apply P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.agrees_of_footprint ag
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Reduction.scratchComponents, Component.isMem]
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim

theorem firstCarry_frame {p : BitVec 64} {s t : RamState}
    (h : (firstCarryEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  have hc : (firstCarryEffect p s).components =
      [.reg 0#5, .reg 2#5, .reg 5#5, .reg 10#5, .reg 13#5, .mem (stackPtr s+48#64) 8, .flags, .rip] := by simp [firstCarryEffect, Effect.components, Write.component, Operand.component] <;> rfl
  have ag := h.agrees
  rw [hc] at ag
  apply P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.agrees_of_footprint ag
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Reduction.scratchComponents, Component.isMem]
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 48) (len := 8) (by decide) ha⟩

theorem firstMiddle_frame {p : BitVec 64} {s t : RamState}
    (h : (firstMiddleEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  have hc : (firstMiddleEffect p s).components =
      [.reg 2#5, .mem (stackPtr s+88#64) 8, .reg 0#5, .reg 6#5, .reg 13#5, .mem (stackPtr s+40#64) 8, .reg 12#5, .reg 3#5, .reg 10#5, .reg 8#5, .reg 9#5, .mem (stackPtr s+64#64) 8, .flags, .rip] := by simp [firstMiddleEffect, Effect.components, Write.component, Operand.component] <;> rfl
  have ag := h.agrees
  rw [hc] at ag
  apply P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.agrees_of_footprint ag
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Reduction.scratchComponents, Component.isMem]
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 88) (len := 8) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 40) (len := 8) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 64) (len := 8) (by decide) ha⟩

theorem firstHigh_frame {p : BitVec 64} {s t : RamState}
    (h : (firstHighEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  have hc : (firstHighEffect p s).components =
      [.reg 0#5, .reg 2#5, .reg 11#5, .mem (stackPtr s+96#64) 8, .reg 1#5, .reg 8#5, .reg 9#5, .reg 15#5, .reg 3#5, .flags, .rip] := by simp [firstHighEffect, Effect.components, Write.component, Operand.component] <;> rfl
  have ag := h.agrees
  rw [hc] at ag
  apply P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.agrees_of_footprint ag
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Reduction.scratchComponents, Component.isMem]
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 96) (len := 8) (by decide) ha⟩

theorem firstTop_frame {p : BitVec 64} {s t : RamState}
    (h : (firstTopEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  have hc : (firstTopEffect p s).components =
      [.reg 0#5, .reg 14#5, .reg 2#5, .reg 15#5, .reg 9#5, .reg 1#5, .mem (stackPtr s+104#64) 8, .mem (stackPtr s+7#64) 1, .flags, .rip] := by simp [firstTopEffect, Effect.components, Write.component, Operand.component] <;> rfl
  have ag := h.agrees
  rw [hc] at ag
  apply P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.agrees_of_footprint ag
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Reduction.scratchComponents, Component.isMem]
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 104) (len := 8) (by decide) ha⟩
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 7) (len := 1) (by decide) ha⟩

end P256.Proofs.Sec1.SquareRoot.Montgomery
