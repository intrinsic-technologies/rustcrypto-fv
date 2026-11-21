import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix
open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper
open MemoryRoutines.Machine

def saveChanges (sp : BitVec 64) : List Component :=
  [.rip, .reg 3, .reg 14, .reg 15, .reg 4, .mem (sp - BitVec.ofNat 64 176) 8]

theorem reserve_save [Bindings] {initial s : RamState} (hS : EntryStack initial)
    (hg : Grows initial s) {boundary : ReturnBoundary} (outside : ¬ InProgram boundary.rip)
    (T0 : GTrack (saveChanges (stackPtr initial)) s s)
    (rip : s.RIP = 0x1017aa) (rsp : stackPtr s = stackPtr initial - 168)
    (zf : (StatusFlags.ofRFLAGS s.RFLAGS).ZF = false) :
    ∃ t, Advances boundary 6 s t ∧ GTrack (saveChanges (stackPtr initial)) s t ∧
      t.RIP = 0x1017be ∧ stackPtr t = stackPtr initial - 168 ∧
      rd t 3 = rd s 9 ∧ rd t 14 = rd s 2 ∧ rd t 15 = rd s 6 := by
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x1017aa 0x4c 0xcb (by unfold RexWPrefix; decide) (by decide))
    T0 (program_text_slice T0.code 0x17aa 3 (by decide +kernel)) rip
    (code_ne_boundary outside 0x17ad (by omega)) (by fits [saveChanges])
  change (movR64R64Effect 0x1017aa 3 9 s).Holds s u1 at e1
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x1017ad 0x49 0xd6 (by unfold RexWPrefix; decide) (by decide))
    T1 (program_text_slice T1.code 0x17ad 3 (by decide +kernel)) e1.rip
    (code_ne_boundary outside 0x17b0 (by omega)) (by fits [saveChanges])
  change (movR64R64Effect 0x1017ad 14 2 u1).Holds u1 u2 at e2
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x1017b0 0x49 0xf7 (by unfold RexWPrefix; decide) (by decide))
    T2 (program_text_slice T2.code 0x17b0 3 (by decide +kernel)) e2.rip
    (code_ne_boundary outside 0x17b3 (by omega)) (by fits [saveChanges])
  change (movR64R64Effect 0x1017b0 15 6 u2).Holds u2 u3 at e3
  have hz3 : condHolds 4 (StatusFlags.ofRFLAGS u3.RFLAGS) = false := by
    rw [condHolds_4, T3.agrees.statusFlags (by simp [saveChanges])]
    exact zf
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (jcc_rel32_effect_step 0x1017b3 4 0x11d)
    T3 (program_text_slice T3.code 0x17b3 6 (by decide +kernel))
    ⟨e3.rip, fun _ => by decide⟩
    (by
      simp only [jccEffect, branchEffect, hz3, Bool.false_eq_true, ite_false]
      exact code_ne_boundary outside 0x17b9 (by omega))
    (by fits [saveChanges])
  have ip4 : u4.RIP = 0x1017b9 := (jccEffect_not_taken hz3 e4).rip
  have sp4 := sp_keep (((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees)
    (by simp [jccEffect]) rsp
  have pa : pushAddr u4 = stackPtr initial - BitVec.ofNat 64 176 := by
    rw [pushAddr, sp4]
    bv_omega
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step
    (call_rel32_effect_step 0x1017b9 0x2e2 (by decide))
    T4 (program_text_slice T4.code 0x17b9 5 (by decide +kernel))
    (storePre_slot (k := 176) hS (hg.step T4.agrees) ip4 pa (by omega) (by omega)
      (code_inProgram 0x17b9 5 (by omega)))
    (code_ne_boundary outside 0x1aa0 (by omega))
    (by
      simp only [Fits, callEffect, pushEffect_components, pa]
      simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      refine ⟨.inl ⟨rfl, by simp [saveChanges]⟩, .inr ⟨rfl, ?_⟩,
        .inl ⟨rfl, by simp [saveChanges]⟩⟩
      intro x hx
      refine ⟨⟨_, by simp [saveChanges], hx⟩, ?_⟩
      obtain ⟨i, hi, rfl⟩ := hx
      have hr := hS.room
      have ht := hS.top
      apply hS.outside <;> rw [slot_toNat (by omega) ht (by omega)] <;> omega)
  change (callEffect (fun _ => branchTarget 0x1017b9 5
    ((0x2e2 : BitVec 32).signExtend 64)) (0x1017b9 + 5) u4).Holds u4 u5 at e5
  have top5 : stackTop u5 = 0x1017be := (callEffect_stack e5).1
  have sp5 : stackPtr u5 = stackPtr initial - BitVec.ofNat 64 176 := e5.writes.1.trans pa
  have read5 : MemReadable u5 (stackPtr u5) 8 := by
    rw [sp5]
    have hw := slot_writable (k := 176) hS (hg.step T5.agrees) (by omega) (by omega)
    exact ⟨hw.low, hw.mem⟩
  obtain ⟨u6, a6, T6, e6⟩ := gtrack_step (ret_effect_step 0x101aa0)
    T5 (program_text_slice T5.code 0x1aa0 1 (by decide +kernel))
    ⟨⟨e5.rip, read5⟩, by rw [top5]; decide⟩
    (by change stackTop u5 ≠ _; rw [top5]; exact code_ne_boundary outside 0x17be (by omega))
    (by fits [saveChanges])
  refine ⟨u6, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans a6)))), T6,
    e6.rip.trans top5, ?_, ?_, ?_, ?_⟩
  · exact e6.writes.trans ((callEffect_stack e5).2.trans sp4)
  · exact (((((e2.agrees.trans e3.agrees).trans e4.agrees).trans e5.agrees).trans
      e6.agrees).read (by simp [jccEffect, pa])).trans e1.writes
  · exact ((((e3.agrees.trans e4.agrees).trans e5.agrees).trans e6.agrees).read
      (by simp [jccEffect, pa])).trans
      (e2.writes.trans (e1.agrees.read (by simp)))
  · exact (((e4.agrees.trans e5.agrees).trans e6.agrees).read
      (by simp [jccEffect, pa])).trans
      (e3.writes.trans (T2.agrees.read (by simp [saveChanges])))

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
