import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.SecondStart
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.SecondMiddle
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.SecondHigh
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.SecondTop
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.ThirdStart
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.ThirdMiddle
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.ThirdHigh
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.ThirdTop
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.FourthStart
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.FourthMiddle
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.FourthHigh
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.FourthTop
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Interface

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem scratch_trans {s t u : RamState}
    (h : AgreesExcept (Reduction.scratchComponents s) s t)
    (j : AgreesExcept (Reduction.scratchComponents t) t u) :
    AgreesExcept (Reduction.scratchComponents s) s u := by
  have hr := Reduction.scratch_rsp h
  have he : Reduction.scratchComponents t = Reduction.scratchComponents s := by
    simp only [Reduction.scratchComponents, hr]
  rw [he] at j
  exact (h.trans j).mono (by simp)

theorem secondStart_components (p : BitVec 64) (s : RamState) :
    (secondStartEffect p s).components = [.reg 0, .reg 2, .reg 6, .reg 8, .reg 1, .reg 12, .reg 13, .reg 10, .reg 5, .reg 11, .mem (stackPtr s+56#64) 8, .flags, .rip] := by
  simp [Effect.components, Write.component, Operand.component, stackPtr, Operand.read, secondStartEffect]

theorem secondStart_frame {p : BitVec 64} {s t : RamState}
    (h : (secondStartEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [secondStart_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [secondStart_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 56) (len := 8) (by decide) hv⟩

theorem secondStart_read {p : BitVec 64} {s t : RamState}
    (h : (secondStartEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((secondStartEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [secondStartEffect, Write.Full, Operand.Full]) (by rw [secondStart_components]; simp) op

theorem secondMiddle_components (p : BitVec 64) (s : RamState) :
    (secondMiddleEffect p s).components = [.reg 0, .reg 2, .reg 12, .reg 8, .reg 10, .reg 6, .reg 11, .flags, .rip] := rfl

theorem secondMiddle_frame {p : BitVec 64} {s t : RamState}
    (h : (secondMiddleEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [secondMiddle_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [secondMiddle_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim

theorem secondMiddle_read {p : BitVec 64} {s t : RamState}
    (h : (secondMiddleEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((secondMiddleEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [secondMiddleEffect, Write.Full, Operand.Full]) (by rw [secondMiddle_components]; simp) op

theorem secondHigh_components (p : BitVec 64) (s : RamState) :
    (secondHighEffect p s).components = [.reg 0, .reg 2, .reg 14, .reg 1, .reg 8, .mem (stackPtr s+56#64) 8, .flags, .rip] := by
  simp [Effect.components, Write.component, Operand.component, stackPtr, Operand.read, secondHighEffect]

theorem secondHigh_frame {p : BitVec 64} {s t : RamState}
    (h : (secondHighEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [secondHigh_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [secondHigh_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 56) (len := 8) (by decide) hv⟩

theorem secondHigh_read {p : BitVec 64} {s t : RamState}
    (h : (secondHighEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((secondHighEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [secondHighEffect, Write.Full, Operand.Full]) (by rw [secondHigh_components]; simp) op

theorem secondTop_components (p : BitVec 64) (s : RamState) :
    (secondTopEffect p s).components = [.reg 6, .reg 12, .reg 0, .reg 14, .reg 1, .reg 2, .reg 15, .mem (stackPtr s+7#64) 1, .flags, .rip] := by
  simp [Effect.components, Write.component, Operand.component, stackPtr, Operand.read, secondTopEffect]

theorem secondTop_frame {p : BitVec 64} {s t : RamState}
    (h : (secondTopEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [secondTop_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [secondTop_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 7) (len := 1) (by decide) hv⟩

theorem secondTop_read {p : BitVec 64} {s t : RamState}
    (h : (secondTopEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((secondTopEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [secondTopEffect, Write.Full, Operand.Full]) (by rw [secondTop_components]; simp) op

theorem thirdStart_components (p : BitVec 64) (s : RamState) :
    (thirdStartEffect p s).components = [.reg 0, .reg 2, .reg 6, .reg 10, .reg 9, .reg 8, .reg 13, .reg 11, .reg 5, .reg 3, .flags, .rip] := rfl

theorem thirdStart_frame {p : BitVec 64} {s t : RamState}
    (h : (thirdStartEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [thirdStart_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [thirdStart_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim

theorem thirdStart_read {p : BitVec 64} {s t : RamState}
    (h : (thirdStartEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((thirdStartEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [thirdStartEffect, Write.Full, Operand.Full]) (by rw [thirdStart_components]; simp) op

theorem thirdMiddle_components (p : BitVec 64) (s : RamState) :
    (thirdMiddleEffect p s).components = [.reg 0, .reg 2, .reg 8, .reg 11, .reg 12, .reg 6, .reg 3, .flags, .rip] := rfl

theorem thirdMiddle_frame {p : BitVec 64} {s t : RamState}
    (h : (thirdMiddleEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [thirdMiddle_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [thirdMiddle_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim

theorem thirdMiddle_read {p : BitVec 64} {s t : RamState}
    (h : (thirdMiddleEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((thirdMiddleEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [thirdMiddleEffect, Write.Full, Operand.Full]) (by rw [thirdMiddle_components]; simp) op

theorem thirdHigh_components (p : BitVec 64) (s : RamState) :
    (thirdHighEffect p s).components = [.reg 0, .reg 2, .reg 10, .reg 9, .reg 11, .flags, .rip] := rfl

theorem thirdHigh_frame {p : BitVec 64} {s t : RamState}
    (h : (thirdHighEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [thirdHigh_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [thirdHigh_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim

theorem thirdHigh_read {p : BitVec 64} {s t : RamState}
    (h : (thirdHighEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((thirdHighEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [thirdHighEffect, Write.Full, Operand.Full]) (by rw [thirdHigh_components]; simp) op

theorem thirdTop_components (p : BitVec 64) (s : RamState) :
    (thirdTopEffect p s).components = [.reg 8, .reg 6, .reg 0, .reg 2, .reg 10, .reg 9, .reg 1, .reg 14, .mem (stackPtr s+24#64) 1, .flags, .rip] := by
  simp [Effect.components, Write.component, Operand.component, stackPtr, Operand.read, thirdTopEffect]

theorem thirdTop_frame {p : BitVec 64} {s t : RamState}
    (h : (thirdTopEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [thirdTop_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [thirdTop_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 24) (len := 1) (by decide) hv⟩

theorem thirdTop_read {p : BitVec 64} {s t : RamState}
    (h : (thirdTopEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((thirdTopEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [thirdTopEffect, Write.Full, Operand.Full]) (by rw [thirdTop_components]; simp) op

theorem fourthStart_components (p : BitVec 64) (s : RamState) :
    (fourthStartEffect p s).components = [.reg 0, .reg 2, .reg 1, .reg 12, .reg 15, .reg 5, .reg 8, .reg 3, .reg 13, .mem (stackPtr s+16#64) 8, .flags, .rip] := by
  simp [Effect.components, Write.component, Operand.component, stackPtr, Operand.read, fourthStartEffect]

theorem fourthStart_frame {p : BitVec 64} {s t : RamState}
    (h : (fourthStartEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [fourthStart_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [fourthStart_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 16) (len := 8) (by decide) hv⟩

theorem fourthStart_read {p : BitVec 64} {s t : RamState}
    (h : (fourthStartEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((fourthStartEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [fourthStartEffect, Write.Full, Operand.Full]) (by rw [fourthStart_components]; simp) op

theorem fourthMiddle_components (p : BitVec 64) (s : RamState) :
    (fourthMiddleEffect p s).components = [.reg 0, .reg 2, .reg 13, .reg 6, .reg 3, .reg 5, .reg 1, .flags, .rip] := rfl

theorem fourthMiddle_frame {p : BitVec 64} {s t : RamState}
    (h : (fourthMiddleEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [fourthMiddle_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [fourthMiddle_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim

theorem fourthMiddle_read {p : BitVec 64} {s t : RamState}
    (h : (fourthMiddleEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((fourthMiddleEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [fourthMiddleEffect, Write.Full, Operand.Full]) (by rw [fourthMiddle_components]; simp) op

theorem fourthHigh_components (p : BitVec 64) (s : RamState) :
    (fourthHighEffect p s).components = [.reg 0, .reg 12, .reg 2, .reg 6, .flags, .rip] := rfl

theorem fourthHigh_frame {p : BitVec 64} {s t : RamState}
    (h : (fourthHighEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [fourthHigh_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [fourthHigh_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim

theorem fourthHigh_read {p : BitVec 64} {s t : RamState}
    (h : (fourthHighEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((fourthHighEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [fourthHighEffect, Write.Full, Operand.Full]) (by rw [fourthHigh_components]; simp) op

theorem fourthTop_components (p : BitVec 64) (s : RamState) :
    (fourthTopEffect p s).components = [.reg 10, .reg 0, .reg 2, .mem (stackPtr s+16#64) 1, .reg 15, .flags, .rip] := by
  simp [Effect.components, Write.component, Operand.component, stackPtr, Operand.read, fourthTopEffect]

theorem fourthTop_frame {p : BitVec 64} {s t : RamState}
    (h : (fourthTopEffect p s).Holds s t) :
    AgreesExcept (Reduction.scratchComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hn
    rw [fourthTop_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Reduction.scratchComponents]
  · intro address c hc hv
    rw [fourthTop_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · exact ⟨.mem (stackPtr s) 112, by simp [Reduction.scratchComponents],
        Reduction.scratch_covered (offset := 16) (len := 1) (by decide) hv⟩

theorem fourthTop_read {p : BitVec 64} {s t : RamState}
    (h : (fourthTopEffect p s).Holds s t) {n : Nat} (op : Operand n) :
    op.read t = op.read ((fourthTopEffect p s).after s true) := by
  exact P256.Proofs.Common.EffectCompose.Effect.Holds.read_after h
    (by simp [fourthTopEffect, Write.Full, Operand.Full]) (by rw [fourthTop_components]; simp) op

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
