import ChaCha20Poly1305.Proofs.Encrypt.Append.Preserve

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def appendTailChanges : List Component :=
  [.reg 0, .reg 4, .reg 3, .reg 12, .reg 14, .reg 15, .flags, .rip]

theorem append_tail [Bindings] {s v : RamState} {boundary : ReturnBoundary}
    (hs : Stack.Valid s 48) (grow : Grows s v)
    (ready : ReadyToStep v) (code : CodeIn Extracted.programImage v)
    (rip : v.RIP = 0x101fe9) (rsp : stackPtr v = stackPtr s - BitVec.ofNat 64 40)
    (outside : ¬ InProgram boundary.rip)
    (different : (returnBoundary s).rip ≠ boundary.rip)
    (low : (returnBoundary s).rip.toNat < 2 ^ 32)
    (ret : wd v (stackPtr s) = (returnBoundary s).rip) :
    ∃ t, Advances boundary 7 v t ∧ GTrack appendTailChanges v t ∧
      t.RIP = (returnBoundary s).rip ∧ stackPtr t = stackPtr s + 8 ∧ rd t 0 = 0 ∧
      rd t 3 = wd v (stackPtr s - BitVec.ofNat 64 32) ∧
      rd t 12 = wd v (stackPtr s - BitVec.ofNat 64 24) ∧
      rd t 14 = wd v (stackPtr s - BitVec.ofNat 64 16) ∧
      rd t 15 = wd v (stackPtr s - BitVec.ofNat 64 8) := by
  have T0 : GTrack appendTailChanges v v := ⟨ready, code, AgreesExcept.refl _ _⟩
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step (xor_r32_r32_effect_step 0x101fe9 0xc0 (by decide))
    T0 (program_text_slice T0.code 0x1fe9 2 (by decide +kernel)) rip
    (code_ne_boundary outside 0x1feb (by omega)) (by fits [appendTailChanges])
  change (xorR32R32Effect 0x101fe9 2 0 0 v).Holds v u1 at e1
  have z1 : rd u1 0 = 0 := by
    have h : rd u1 0 = (((Operand.reg 0 : Operand 32).read v) ^^^
      ((Operand.reg 0 : Operand 32).read v)).setWidth 64 := e1.writes
    rw [BitVec.xor_self] at h
    exact h
  have sp1 : stackPtr u1 = stackPtr s - BitVec.ofNat 64 40 :=
    sp_keep e1.agrees (by simp) rsp
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (add_r64_imm8_effect_step 0x101feb 0x48 0xc4 8 (by unfold RexWPrefix; decide)
      (by decide) (by decide))
    T1 (program_text_slice T1.code 0x1feb 4 (by decide +kernel)) e1.rip
    (code_ne_boundary outside 0x1fef (by omega)) (by fits [appendTailChanges])
  change (addR64Imm8Effect 0x101feb 4 8 u1).Holds u1 u2 at e2
  have sp2 : stackPtr u2 = stackPtr s - BitVec.ofNat 64 32 := by
    have h : stackPtr u2 = stackPtr u1 + (8 : BitVec 8).signExtend 64 := e2.writes
    rw [h, sp1, show (8 : BitVec 8).signExtend 64 = BitVec.ofNat 64 8 from by decide]
    bv_omega
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step (pop_r64_effect_step 0x101fef 0x5b (by decide) (by decide))
    T2 (program_text_slice T2.code 0x1fef 1 (by decide +kernel))
    ⟨e2.rip, by
      rw [sp2]
      exact stack_slot_readable hs (grow.step T2.agrees) (by omega)⟩
    (code_ne_boundary outside 0x1ff0 (by omega)) (by fits [appendTailChanges])
  change (popR64Effect 0x101fef 1 3 u2).Holds u2 u3 at e3
  have sp3 : stackPtr u3 = stackPtr s - BitVec.ofNat 64 24 := by
    have h : stackPtr u3 = stackPtr u2 + 8 := e3.writes.2
    rw [h, sp2]
    bv_omega
  have v3 : rd u3 3 = wd v (stackPtr s - BitVec.ofNat 64 32) := by
    have h : rd u3 3 = wd u2 (stackPtr u2) := e3.writes.1
    rw [sp2] at h
    exact h.trans (gload T2.agrees (by simp [appendTailChanges, Component.Covers]))
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x101ff0 0x41 0x5c
      (by unfold RexPrefix; decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x1ff0 2 (by decide +kernel))
    ⟨e3.rip, by
      rw [sp3]
      exact stack_slot_readable hs (grow.step T3.agrees) (by omega)⟩
    (code_ne_boundary outside 0x1ff2 (by omega)) (by fits [appendTailChanges])
  change (popR64Effect 0x101ff0 2 12 u3).Holds u3 u4 at e4
  have sp4 : stackPtr u4 = stackPtr s - BitVec.ofNat 64 16 := by
    have h : stackPtr u4 = stackPtr u3 + 8 := e4.writes.2
    rw [h, sp3]
    bv_omega
  have v4 : rd u4 12 = wd v (stackPtr s - BitVec.ofNat 64 24) := by
    have h : rd u4 12 = wd u3 (stackPtr u3) := e4.writes.1
    rw [sp3] at h
    exact h.trans (gload T3.agrees (by simp [appendTailChanges, Component.Covers]))
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x101ff2 0x41 0x5e
      (by unfold RexPrefix; decide) (by decide) (by decide))
    T4 (program_text_slice T4.code 0x1ff2 2 (by decide +kernel))
    ⟨e4.rip, by
      rw [sp4]
      exact stack_slot_readable hs (grow.step T4.agrees) (by omega)⟩
    (code_ne_boundary outside 0x1ff4 (by omega)) (by fits [appendTailChanges])
  change (popR64Effect 0x101ff2 2 14 u4).Holds u4 u5 at e5
  have sp5 : stackPtr u5 = stackPtr s - BitVec.ofNat 64 8 := by
    have h : stackPtr u5 = stackPtr u4 + 8 := e5.writes.2
    rw [h, sp4]
    bv_omega
  have v5 : rd u5 14 = wd v (stackPtr s - BitVec.ofNat 64 16) := by
    have h : rd u5 14 = wd u4 (stackPtr u4) := e5.writes.1
    rw [sp4] at h
    exact h.trans (gload T4.agrees (by simp [appendTailChanges, Component.Covers]))
  obtain ⟨u6, a6, T6, e6⟩ := gtrack_step
    (pop_r64_rex_effect_step 0x101ff4 0x41 0x5f
      (by unfold RexPrefix; decide) (by decide) (by decide))
    T5 (program_text_slice T5.code 0x1ff4 2 (by decide +kernel))
    ⟨e5.rip, by
      rw [sp5]
      exact stack_slot_readable hs (grow.step T5.agrees) (by omega)⟩
    (code_ne_boundary outside 0x1ff6 (by omega)) (by fits [appendTailChanges])
  change (popR64Effect 0x101ff4 2 15 u5).Holds u5 u6 at e6
  have sp6 : stackPtr u6 = stackPtr s - BitVec.ofNat 64 0 := by
    have h : stackPtr u6 = stackPtr u5 + 8 := e6.writes.2
    rw [h, sp5]
    bv_omega
  have v6 : rd u6 15 = wd v (stackPtr s - BitVec.ofNat 64 8) := by
    have h : rd u6 15 = wd u5 (stackPtr u5) := e6.writes.1
    rw [sp5] at h
    exact h.trans (gload T5.agrees (by simp [appendTailChanges, Component.Covers]))
  have sp6' : stackPtr u6 = stackPtr s := by simpa using sp6
  have ret6 : wd u6 (stackPtr u6) = (returnBoundary s).rip := by
    rw [sp6']
    exact (gload T6.agrees (by simp [appendTailChanges, Component.Covers])).trans ret
  obtain ⟨u7, a7, T7, e7⟩ := gtrack_step (ret_effect_step 0x101ff6)
    T6 (program_text_slice T6.code 0x1ff6 1 (by decide +kernel))
    ⟨⟨e6.rip, by
      rw [sp6']
      have h := stack_slot_readable hs (grow.step T6.agrees) (k := 0) (by omega)
      simpa using h⟩, by change (wd u6 (stackPtr u6)).toNat < 2 ^ 32; rw [ret6]; exact low⟩
    (by change wd u6 (stackPtr u6) ≠ boundary.rip; rw [ret6]; exact different)
    (by fits [appendTailChanges])
  refine ⟨u7, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7))))), T7,
    e7.rip.trans ret6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : stackPtr u7 = stackPtr u6 + 8 := e7.writes
    rw [h, sp6']
  · exact ((((((e2.agrees.trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans
      e7.agrees).read (by simp)).trans z1
  · exact ((((e4.agrees.trans e5.agrees).trans e6.agrees).trans e7.agrees).read (by simp)).trans v3
  · exact (((e5.agrees.trans e6.agrees).trans e7.agrees).read (by simp)).trans v4
  · exact ((e6.agrees.trans e7.agrees).read (by simp)).trans v5
  · exact (e7.agrees.read (by simp)).trans v6

end ChaCha20Poly1305.Proofs.Encrypt
