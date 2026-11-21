import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

set_option maxHeartbeats 600000 in
theorem save_registers [Bindings] {s : RamState} (hs : EntryStack s)
    (outside : ¬ InProgram (returnBoundary s).rip) (t0 : Track s s)
    (entry : s.RIP = 0x101740) :
    ∃ t, Advances (returnBoundary s) 7 s t ∧ Track s t ∧
      t.RIP = 0x10174e ∧ stackPtr t = stackPtr s - 168 ∧
      (∀ r, r ≠ (4#5) → rd t r = rd s r) ∧
      wd t (stackPtr s - BitVec.ofNat 64 8) = rd s 5 ∧
      wd t (stackPtr s - BitVec.ofNat 64 16) = rd s 15 ∧
      wd t (stackPtr s - BitVec.ofNat 64 24) = rd s 14 ∧
      wd t (stackPtr s - BitVec.ofNat 64 32) = rd s 13 ∧
      wd t (stackPtr s - BitVec.ofNat 64 40) = rd s 12 ∧
      wd t (stackPtr s - BitVec.ofNat 64 48) = rd s 3 := by
  have P1 : pushAddr s = stackPtr s - BitVec.ofNat 64 8 := by
    rfl
  have W1 : StepWrites s 8 (pushR64Effect 0x101740 1 5 s).components := by
    step_writes [P1]
  obtain ⟨u1, a1, T1, e1⟩ := track_step hs
    (push_r64_effect_step 0x101740 0x55 (by decide))
    t0 (program_text_slice t0.code 0x1740 1 (by decide +kernel))
    (storePre_slot hs t0.grows entry P1 (by omega) (by omega)
      (code_inProgram 0x1740 1 (by omega)))
    (code_ne_boundary outside 0x1741 (by omega)) W1
  change (pushR64Effect 0x101740 1 5 s).Holds s u1 at e1
  have S1 : stackPtr u1 = stackPtr s - BitVec.ofNat 64 8 :=
    e1.writes.1.trans P1
  have P2 : pushAddr u1 = stackPtr s - BitVec.ofNat 64 16 := by
    rw [pushAddr, S1]; bv_omega
  have W2 : StepWrites s 16 (pushR64Effect 0x101741 2 15 u1).components := by
    step_writes [P2]
  obtain ⟨u2, a2, T2, e2⟩ := track_step hs
    (push_r64_rex_effect_step 0x101741 0x41 0x57 (by unfold RexPrefix; decide) (by decide))
    T1 (program_text_slice T1.code 0x1741 2 (by decide +kernel))
    (storePre_slot hs T1.grows e1.rip P2 (by omega) (by omega)
      (code_inProgram 0x1741 2 (by omega)))
    (code_ne_boundary outside 0x1743 (by omega)) W2
  change (pushR64Effect 0x101741 2 15 u1).Holds u1 u2 at e2
  have S2 : stackPtr u2 = stackPtr s - BitVec.ofNat 64 16 :=
    e2.writes.1.trans P2
  have P3 : pushAddr u2 = stackPtr s - BitVec.ofNat 64 24 := by
    rw [pushAddr, S2]; bv_omega
  have W3 : StepWrites s 24 (pushR64Effect 0x101743 2 14 u2).components := by
    step_writes [P3]
  obtain ⟨u3, a3, T3, e3⟩ := track_step hs
    (push_r64_rex_effect_step 0x101743 0x41 0x56 (by unfold RexPrefix; decide) (by decide))
    T2 (program_text_slice T2.code 0x1743 2 (by decide +kernel))
    (storePre_slot hs T2.grows e2.rip P3 (by omega) (by omega)
      (code_inProgram 0x1743 2 (by omega)))
    (code_ne_boundary outside 0x1745 (by omega)) W3
  change (pushR64Effect 0x101743 2 14 u2).Holds u2 u3 at e3
  have S3 : stackPtr u3 = stackPtr s - BitVec.ofNat 64 24 :=
    e3.writes.1.trans P3
  have P4 : pushAddr u3 = stackPtr s - BitVec.ofNat 64 32 := by
    rw [pushAddr, S3]; bv_omega
  have W4 : StepWrites s 32 (pushR64Effect 0x101745 2 13 u3).components := by
    step_writes [P4]
  obtain ⟨u4, a4, T4, e4⟩ := track_step hs
    (push_r64_rex_effect_step 0x101745 0x41 0x55 (by unfold RexPrefix; decide) (by decide))
    T3 (program_text_slice T3.code 0x1745 2 (by decide +kernel))
    (storePre_slot hs T3.grows e3.rip P4 (by omega) (by omega)
      (code_inProgram 0x1745 2 (by omega)))
    (code_ne_boundary outside 0x1747 (by omega)) W4
  change (pushR64Effect 0x101745 2 13 u3).Holds u3 u4 at e4
  have S4 : stackPtr u4 = stackPtr s - BitVec.ofNat 64 32 :=
    e4.writes.1.trans P4
  have P5 : pushAddr u4 = stackPtr s - BitVec.ofNat 64 40 := by
    rw [pushAddr, S4]; bv_omega
  have W5 : StepWrites s 40 (pushR64Effect 0x101747 2 12 u4).components := by
    step_writes [P5]
  obtain ⟨u5, a5, T5, e5⟩ := track_step hs
    (push_r64_rex_effect_step 0x101747 0x41 0x54 (by unfold RexPrefix; decide) (by decide))
    T4 (program_text_slice T4.code 0x1747 2 (by decide +kernel))
    (storePre_slot hs T4.grows e4.rip P5 (by omega) (by omega)
      (code_inProgram 0x1747 2 (by omega)))
    (code_ne_boundary outside 0x1749 (by omega)) W5
  change (pushR64Effect 0x101747 2 12 u4).Holds u4 u5 at e5
  have S5 : stackPtr u5 = stackPtr s - BitVec.ofNat 64 40 :=
    e5.writes.1.trans P5
  have P6 : pushAddr u5 = stackPtr s - BitVec.ofNat 64 48 := by
    rw [pushAddr, S5]; bv_omega
  have W6 : StepWrites s 48 (pushR64Effect 0x101749 1 3 u5).components := by
    step_writes [P6]
  obtain ⟨u6, a6, T6, e6⟩ := track_step hs
    (push_r64_effect_step 0x101749 0x53 (by decide))
    T5 (program_text_slice T5.code 0x1749 1 (by decide +kernel))
    (storePre_slot hs T5.grows e5.rip P6 (by omega) (by omega)
      (code_inProgram 0x1749 1 (by omega)))
    (code_ne_boundary outside 0x174a (by omega)) W6
  change (pushR64Effect 0x101749 1 3 u5).Holds u5 u6 at e6
  have S6 : stackPtr u6 = stackPtr s - BitVec.ofNat 64 48 :=
    e6.writes.1.trans P6
  have W7 : StepWrites s 0 (subR64Imm8Effect 0x10174a 4 0x78 u6).components := by
    step_writes []
  obtain ⟨u7, a7, T7, e7⟩ := track_step hs
    (sub_r64_imm8_effect_step 0x10174a 0x48 0xec 0x78
      (by unfold RexWPrefix; decide) (by decide) (by decide))
    T6 (program_text_slice T6.code 0x174a 4 (by decide +kernel)) e6.rip
    (code_ne_boundary outside 0x174e (by omega)) W7
  change (subR64Imm8Effect 0x10174a 4 0x78 u6).Holds u6 u7 at e7
  have S7 : stackPtr u7 = stackPtr s - 168 := by
    have h : stackPtr u7 = stackPtr u6 - (0x78 : BitVec 8).signExtend 64 := e7.writes
    rw [h, S6, show (0x78 : BitVec 8).signExtend 64 = 120#64 from rfl]
    bv_omega
  refine ⟨u7, (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))), T7, e7.rip, S7, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (e1.agrees.trans (e2.agrees.trans (e3.agrees.trans (e4.agrees.trans (e5.agrees.trans (e6.agrees.trans e7.agrees)))))).read (by
      simp [pushR64Effect_components, subR64Imm8Effect_components, hr])
  · have written : wd u1 (stackPtr s - BitVec.ofNat 64 8) = rd s 5 := by
      have h : wd u1 (pushAddr s) = rd s 5 := e1.writes.2
      simpa only [P1] using h
    exact ((W7.keep e7.agrees (by omega) (by omega : 8 ≤ 1104)).trans ((W6.keep e6.agrees (by omega) (by omega : 8 ≤ 1104)).trans ((W5.keep e5.agrees (by omega) (by omega : 8 ≤ 1104)).trans ((W4.keep e4.agrees (by omega) (by omega : 8 ≤ 1104)).trans ((W3.keep e3.agrees (by omega) (by omega : 8 ≤ 1104)).trans ((W2.keep e2.agrees (by omega) (by omega : 8 ≤ 1104)).trans written))))))
  · have written : wd u2 (stackPtr s - BitVec.ofNat 64 16) = rd u1 15 := by
      have h : wd u2 (pushAddr u1) = rd u1 15 := e2.writes.2
      simpa only [P2] using h
    exact ((W7.keep e7.agrees (by omega) (by omega : 16 ≤ 1104)).trans ((W6.keep e6.agrees (by omega) (by omega : 16 ≤ 1104)).trans ((W5.keep e5.agrees (by omega) (by omega : 16 ≤ 1104)).trans ((W4.keep e4.agrees (by omega) (by omega : 16 ≤ 1104)).trans ((W3.keep e3.agrees (by omega) (by omega : 16 ≤ 1104)).trans (written.trans (e1.agrees.read (by simp))))))))
  · have written : wd u3 (stackPtr s - BitVec.ofNat 64 24) = rd u2 14 := by
      have h : wd u3 (pushAddr u2) = rd u2 14 := e3.writes.2
      simpa only [P3] using h
    exact ((W7.keep e7.agrees (by omega) (by omega : 24 ≤ 1104)).trans ((W6.keep e6.agrees (by omega) (by omega : 24 ≤ 1104)).trans ((W5.keep e5.agrees (by omega) (by omega : 24 ≤ 1104)).trans ((W4.keep e4.agrees (by omega) (by omega : 24 ≤ 1104)).trans (written.trans ((e1.agrees.trans e2.agrees).read (by simp)))))))
  · have written : wd u4 (stackPtr s - BitVec.ofNat 64 32) = rd u3 13 := by
      have h : wd u4 (pushAddr u3) = rd u3 13 := e4.writes.2
      simpa only [P4] using h
    exact ((W7.keep e7.agrees (by omega) (by omega : 32 ≤ 1104)).trans ((W6.keep e6.agrees (by omega) (by omega : 32 ≤ 1104)).trans ((W5.keep e5.agrees (by omega) (by omega : 32 ≤ 1104)).trans (written.trans ((e1.agrees.trans (e2.agrees.trans e3.agrees)).read (by simp))))))
  · have written : wd u5 (stackPtr s - BitVec.ofNat 64 40) = rd u4 12 := by
      have h : wd u5 (pushAddr u4) = rd u4 12 := e5.writes.2
      simpa only [P5] using h
    exact ((W7.keep e7.agrees (by omega) (by omega : 40 ≤ 1104)).trans ((W6.keep e6.agrees (by omega) (by omega : 40 ≤ 1104)).trans (written.trans ((e1.agrees.trans (e2.agrees.trans (e3.agrees.trans e4.agrees))).read (by simp)))))
  · have written : wd u6 (stackPtr s - BitVec.ofNat 64 48) = rd u5 3 := by
      have h : wd u6 (pushAddr u5) = rd u5 3 := e6.writes.2
      simpa only [P6] using h
    exact ((W7.keep e7.agrees (by omega) (by omega : 48 ≤ 1104)).trans (written.trans ((e1.agrees.trans (e2.agrees.trans (e3.agrees.trans (e4.agrees.trans e5.agrees)))).read (by simp))))

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
