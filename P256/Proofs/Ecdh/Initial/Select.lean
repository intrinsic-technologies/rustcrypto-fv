import P256.Proofs.Ecdh.Initial.Support
import P256.Proofs.Ecdh.Initial.Setup

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall Field
open Standards.SECG.ECC

set_option maxHeartbeats 800000 in
theorem select_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Curve.Point}
    (pre : Ecdh.Pre s boundary) (copied : Copied s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ Selected s u point := by
  let choose : Bool := decide (point = .infinity)
  have flag : (t.regValue .rax).setWidth 8 = if choose then 1 else 0 := by
    simpa only [choose, decide_eq_true_eq] using copied.choice
  have ax : frameBase s+248 = stackPtr s-1808 := frame_address s 248 (by decide)
  have ay : (frameBase s+248)+32 = stackPtr s-1776 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have az : (frameBase s+248)+64 = stackPtr s-1744 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have ix : frameBase s+1016 = stackPtr s-1040 := frame_address s 1016 (by decide)
  have iy : (frameBase s+1016)+32 = stackPtr s-1008 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have iz : (frameBase s+1016)+64 = stackPtr s-976 := by
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have x0 : MontgomeryAt t (stackPtr s-1808) (lifted point).x := ax ▸ copied.source.1
  have y0 : MontgomeryAt t (stackPtr s-1776) (lifted point).y := ay ▸ copied.source.2.1
  have z0 : MontgomeryAt t (stackPtr s-1744) (lifted point).z := az ▸ copied.source.2.2
  have ix0 : MontgomeryAt t (stackPtr s-1040) 0 := ix ▸ copied.identity.1
  have iy0 : MontgomeryAt t (stackPtr s-1008) 1 := iy ▸ copied.identity.2.1
  have iz0 : MontgomeryAt t (stackPtr s-976) 0 := iz ▸ copied.identity.2.2
  obtain ⟨n1,t1,run1,f1,e1,m1⟩ := registers (offset := 0xe6) (bytes := firstBytes) (effect := firstEffect) copied.toFrameState
    (first_setup boundary pre.outerBoundary) (by decide) (by decide +kernel) copied.rip
    (by simp [firstEffect,Effect.components,Component.Covers])
    (by simp [firstEffect,Effect.components]) (by simp [firstEffect,Effect.components])
    (by simp [firstEffect,Effect.components]) (by simp [firstEffect,Effect.components])
  have bp1 : t1.regValue .rbp = if choose then 1 else 0 := by
    have h := e1.writes.1
    change t1.regValue .rbp = ((t.regValue .rax).setWidth 8).setWidth 64 at h
    rw [flag] at h
    exact h.trans (by cases choose <;> rfl)
  have r151 : t1.regValue .r15 = stackPtr s-272 :=
    e1.writes.2.1.trans (scalar_stack_address copied.rsp (by decide) (by decide))
  have si1 : t1.regValue .rsi = stackPtr s-1808 :=
    e1.writes.2.2.1.trans (scalar_stack_address copied.rsp (by decide) (by decide))
  have di1 : t1.regValue .rdi = stackPtr s-272 :=
    e1.writes.2.2.2.1.trans (scalar_stack_address copied.rsp (by decide) (by decide))
  have dx1 : t1.regValue .rdx = stackPtr s-1040 :=
    e1.writes.2.2.2.2.1.trans (copied.r13.trans ix)
  have cx1 : (t1.regValue .rcx).setWidth 8 = if choose then 1 else 0 := by
    have h : t1.regValue .rcx =
        ((((t.regValue .rax).setWidth 8).setWidth 64).setWidth 32).setWidth 64 :=
      e1.writes.2.2.2.2.2
    rw [h,flag]
    cases choose <;> rfl
  obtain ⟨t2,c2⟩ := select_call pre f1 firstSite e1.rip si1 dx1 di1
    (x0.of_bytes_eq (by intro i hi; rw [m1] <;> rfl)) (ix0.of_bytes_eq (by intro i hi; rw [m1] <;> rfl)) cx1
  have bp2 : t2.regValue .rbp = if choose then 1 else 0 := (c2.registers .rbp (by simp)).trans bp1
  have r122 : t2.regValue .r12 = frameBase s+312 := (c2.registers .r12 (by simp)).trans
    ((e1.agrees.read (n := 64) (r := 12) (by simp [firstEffect,Effect.components])).trans copied.r12)
  have r142 : t2.regValue .r14 = frameBase s+280 := (c2.registers .r14 (by simp)).trans
    ((e1.agrees.read (n := 64) (r := 14) (by simp [firstEffect,Effect.components])).trans copied.r14)
  have r152 := (c2.registers .r15 (by simp)).trans r151
  have y2 := c2.memory (offset := 1776) (by decide) (by decide) (by decide)
    (y0.of_bytes_eq (by intro i hi; rw [m1] <;> rfl))
  have z2 := c2.memory (offset := 1744) (by decide) (by decide) (by decide)
    (z0.of_bytes_eq (by intro i hi; rw [m1] <;> rfl))
  have iy2 := c2.memory (offset := 1008) (by decide) (by decide) (by decide)
    (iy0.of_bytes_eq (by intro i hi; rw [m1] <;> rfl))
  have iz2 := c2.memory (offset := 976) (by decide) (by decide) (by decide)
    (iz0.of_bytes_eq (by intro i hi; rw [m1] <;> rfl))
  obtain ⟨n3,t3,run3,f3,e3,m3⟩ := registers (offset := 0x106) (bytes := secondBytes) (effect := secondEffect) c2.toFrameState
    (second_setup boundary pre.outerBoundary) (by decide) (by decide +kernel) c2.rip
    (by simp [secondEffect,Effect.components,Component.Covers])
    (by simp [secondEffect,Effect.components]) (by simp [secondEffect,Effect.components])
    (by simp [secondEffect,Effect.components]) (by simp [secondEffect,Effect.components])
  have dx3 : t3.regValue .rdx = stackPtr s-1008 :=
    e3.writes.1.trans (scalar_stack_address c2.rsp (by decide) (by decide))
  have di3 : t3.regValue .rdi = stackPtr s-240 :=
    e3.writes.2.1.trans (scalar_stack_address c2.rsp (by decide) (by decide))
  have si3 : t3.regValue .rsi = stackPtr s-1776 :=
    e3.writes.2.2.1.trans (r142.trans (frame_address s 280 (by decide)))
  have cx3 : (t3.regValue .rcx).setWidth 8 = if choose then 1 else 0 := by
    have h : t3.regValue .rcx = ((t2.regValue .rbp).setWidth 32).setWidth 64 := e3.writes.2.2.2
    rw [h,bp2]
    cases choose <;> rfl
  obtain ⟨t4,c4⟩ := select_call pre f3 secondSite e3.rip si3 dx3 di3
    (y2.of_bytes_eq (by intro i hi; rw [m3] <;> rfl)) (iy2.of_bytes_eq (by intro i hi; rw [m3] <;> rfl)) cx3
  have bp4 := (c4.registers .rbp (by simp)).trans
    ((e3.agrees.read (n := 64) (r := 5) (by simp [secondEffect,Effect.components])).trans bp2)
  have r124 := (c4.registers .r12 (by simp)).trans
    ((e3.agrees.read (n := 64) (r := 12) (by simp [secondEffect,Effect.components])).trans r122)
  have r154 := (c4.registers .r15 (by simp)).trans
    ((e3.agrees.read (n := 64) (r := 15) (by simp [secondEffect,Effect.components])).trans r152)
  have x4 := c4.memory (offset := 272) (by decide) (by decide) (by decide)
    (c2.value.of_bytes_eq (by intro i hi; rw [m3] <;> rfl))
  have z4 := c4.memory (offset := 1744) (by decide) (by decide) (by decide)
    (z2.of_bytes_eq (by intro i hi; rw [m3] <;> rfl))
  have iz4 := c4.memory (offset := 976) (by decide) (by decide) (by decide)
    (iz2.of_bytes_eq (by intro i hi; rw [m3] <;> rfl))
  obtain ⟨n5,t5,run5,f5,e5,m5⟩ := registers (offset := 0x120) (bytes := thirdBytes) (effect := thirdEffect) c4.toFrameState
    (third_setup boundary pre.outerBoundary) (by decide) (by decide +kernel) c4.rip
    (by simp [thirdEffect,Effect.components,Component.Covers])
    (by simp [thirdEffect,Effect.components]) (by simp [thirdEffect,Effect.components])
    (by simp [thirdEffect,Effect.components]) (by simp [thirdEffect,Effect.components])
  have dx5 : t5.regValue .rdx = stackPtr s-976 :=
    e5.writes.1.trans (scalar_stack_address c4.rsp (by decide) (by decide))
  have di5 : t5.regValue .rdi = stackPtr s-208 :=
    e5.writes.2.1.trans (scalar_stack_address c4.rsp (by decide) (by decide))
  have si5 : t5.regValue .rsi = stackPtr s-1744 :=
    e5.writes.2.2.1.trans (r124.trans (frame_address s 312 (by decide)))
  have cx5 : (t5.regValue .rcx).setWidth 8 = if choose then 1 else 0 := by
    have h : t5.regValue .rcx = ((t4.regValue .rbp).setWidth 32).setWidth 64 := e5.writes.2.2.2
    rw [h,bp4]
    cases choose <;> rfl
  obtain ⟨u,c6⟩ := select_call pre f5 thirdSite e5.rip si5 dx5 di5
    (z4.of_bytes_eq (by intro i hi; rw [m5] <;> rfl)) (iz4.of_bytes_eq (by intro i hi; rw [m5] <;> rfl)) cx5
  have x6 := c6.memory (offset := 272) (by decide) (by decide) (by decide)
    (x4.of_bytes_eq (by intro i hi; rw [m5] <;> rfl))
  have y6 := c6.memory (offset := 240) (by decide) (by decide) (by decide)
    (c4.value.of_bytes_eq (by intro i hi; rw [m5] <;> rfl))
  obtain ⟨n2,run2⟩ := c2.execution
  obtain ⟨n4,run4⟩ := c4.execution
  obtain ⟨n6,run6⟩ := c6.execution
  refine ⟨n1+n2+n3+n4+n5+n6,u,((((run1.trans run2).trans run3).trans run4).trans run5).trans run6,
    c6.toFrameState,c6.rip,?_,?_,?_,?_⟩
  · exact (c6.registers .rbx (by simp)).trans
      ((e5.agrees.read (n := 64) (r := 3) (by simp [thirdEffect,Effect.components])).trans
      ((c4.registers .rbx (by simp)).trans
      ((e3.agrees.read (n := 64) (r := 3) (by simp [secondEffect,Effect.components])).trans
      ((c2.registers .rbx (by simp)).trans
      ((e1.agrees.read (n := 64) (r := 3) (by simp [firstEffect,Effect.components])).trans copied.output)))))
  · rw [c6.scalar (by decide),m5,c4.scalar (by decide),m3,c2.scalar (by decide),m1]
    exact copied.scalar
  · have a1 : frameBase s+1784 = stackPtr s-272 := frame_address s 1784 (by decide)
    have a2 : (frameBase s+1784)+32 = stackPtr s-240 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    have a3 : (frameBase s+1784)+64 = stackPtr s-208 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    have z6 := c6.value
    cases point <;> simp only [choose,lifted,ProjectiveWrapper.Decode.projective,
      reduceCtorEq,decide_true,decide_false,Bool.false_eq_true,↓reduceIte] at x6 y6 z6 ⊢
    all_goals exact ⟨a1.symm ▸ x6,a2.symm ▸ y6,a3.symm ▸ z6⟩
  · have addr : frameBase s+1784 = stackPtr s-272 := frame_address s 1784 (by decide)
    rw [addr]
    exact (c6.registers .r15 (by simp)).trans
      ((e5.agrees.read (n := 64) (r := 15) (by simp [thirdEffect,Effect.components])).trans r154)

end P256.Proofs.Ecdh.Initial
