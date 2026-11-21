import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow.Low
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow.MiddleLow
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow.MiddleHigh
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Borrow.High

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction

open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem borrow_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : Fourth s t v) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ Difference s t u := by
  obtain ⟨u1, ⟨n1, run1⟩, f1, ip1, ag1, d1, b1⟩ := Borrow.low pre state.frame state.rip
  obtain ⟨u2, ⟨n2, run2⟩, f2, ip2, ag2, d2, b2⟩ := Borrow.middleLow pre f1 ip1
  obtain ⟨u3, ⟨n3, run3⟩, f3, ip3, ag3, d3, b3⟩ := Borrow.middleHigh pre f2 ip2
  obtain ⟨u4, ⟨n4, run4⟩, f4, ip4, ag4, d4, b4⟩ := Borrow.high pre f3 ip3
  have r1 : u1.regValue .rcx = t.regValue .rcx :=
    ag1.read (n := 64) (r := 1) (by simp [Borrow.changes])
  have r2 : u2.regValue .r8 = t.regValue .r8 :=
    (ag1.trans ag2).read (n := 64) (r := 8) (by simp [Borrow.changes])
  have r3 : u3.regValue .rax = t.regValue .rax :=
    ((ag1.trans ag2).trans ag3).read (n := 64) (r := 0) (by simp [Borrow.changes])
  have p1 := (Borrow.slot_preserved ag1 (offset := 48) (by unfold OffsetsApart; decide +kernel)).trans state.slots.p1
  have p2 := ((Borrow.slot_preserved ag2 (offset := 40) (by unfold OffsetsApart; decide +kernel)).trans (Borrow.slot_preserved ag1 (by unfold OffsetsApart; decide +kernel))).trans state.slots.p2
  have p3 := (((Borrow.slot_preserved ag3 (offset := 32) (by unfold OffsetsApart; decide +kernel)).trans (Borrow.slot_preserved ag2 (by unfold OffsetsApart; decide +kernel))).trans (Borrow.slot_preserved ag1 (by unfold OffsetsApart; decide +kernel))).trans state.slots.p3
  rw [state.r11] at d1 b1
  rw [r1, p1, b1] at d2 b2
  rw [r2, p2, b2] at d3 b3
  rw [r3, p3, b3] at d4 b4
  have all := ((ag1.trans ag2).trans ag3).trans ag4
  have keep_rdi : u4.regValue .rdi = t.regValue .rdi :=
    all.read (n := 64) (r := 7) (by simp [Borrow.changes])
  have keep_rbx : u4.regValue .rbx = t.regValue .rbx :=
    all.read (n := 64) (r := 3) (by simp [Borrow.changes])
  have keep_rcx : u4.regValue .rcx = t.regValue .rcx :=
    all.read (n := 64) (r := 1) (by simp [Borrow.changes])
  have keep_r8 : u4.regValue .r8 = t.regValue .r8 :=
    all.read (n := 64) (r := 8) (by simp [Borrow.changes])
  have keep_r12 : u4.regValue .r12 = t.regValue .r12 :=
    all.read (n := 64) (r := 12) (by simp [Borrow.changes])
  have keep_rdx : u4.regValue .rdx = t.regValue .rdx :=
    all.read (n := 64) (r := 2) (by simp [Borrow.changes])
  have keep16 := (((Borrow.slot_preserved ag4 (offset := 16) (by unfold OffsetsApart; decide +kernel)).trans (Borrow.slot_preserved ag3 (by unfold OffsetsApart; decide +kernel))).trans (Borrow.slot_preserved ag2 (by unfold OffsetsApart; decide +kernel))).trans (Borrow.slot_preserved ag1 (by unfold OffsetsApart; decide +kernel))
  have keep24 := (((Borrow.slot_preserved ag4 (offset := 24) (by unfold OffsetsApart; decide +kernel)).trans (Borrow.slot_preserved ag3 (by unfold OffsetsApart; decide +kernel))).trans (Borrow.slot_preserved ag2 (by unfold OffsetsApart; decide +kernel))).trans (Borrow.slot_preserved ag1 (by unfold OffsetsApart; decide +kernel))
  have out1 : u4.regValue .rsi = u1.regValue .rsi :=
    ((ag2.trans ag3).trans ag4).read (n := 64) (r := 6) (by simp [Borrow.changes])
  have out2 : u4.regValue .r9 = u2.regValue .r9 :=
    (ag3.trans ag4).read (n := 64) (r := 9) (by simp [Borrow.changes])
  have out3 : u4.regValue .r14 = u3.regValue .r14 :=
    ag4.read (n := 64) (r := 14) (by simp [Borrow.changes])
  refine ⟨u4, ⟨n1+n2+n3+n4, ((run1.trans run2).trans run3).trans run4⟩,
    ⟨f4, ip4, keep_rdi.trans state.rdi, keep_rbx, keep_rcx, keep_r8, keep_r12,
      ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [keep_rdx, keep24, keep16]
    exact state.top
  · exact out1.trans d1
  · exact out2.trans d2
  · exact out3.trans d3
  · exact d4
  · exact b4

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction
