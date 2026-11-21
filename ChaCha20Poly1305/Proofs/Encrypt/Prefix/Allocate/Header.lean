import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def headerChanges (sp : BitVec 64) : List Component :=
  [.rip, .mem (sp - BitVec.ofNat 64 168) 8, .mem (sp - BitVec.ofNat 64 160) 8, .mem (sp - BitVec.ofNat 64 152) 8]

theorem header_slot_fits {initial : RamState} (hS : EntryStack initial) {k : Nat}
    (hk : k = 168 ∨ k = 160 ∨ k = 152) :
    ∀ x, (Component.mem (stackPtr initial - BitVec.ofNat 64 k) 8).Covers x →
      (∃ d ∈ headerChanges (stackPtr initial), d.Covers x) ∧ ¬ InProgram x := by
  intro x hx
  refine ⟨⟨_, ?_, hx⟩, ?_⟩
  · rcases hk with rfl | rfl | rfl <;> simp [headerChanges]
  · obtain ⟨i, hi, rfl⟩ := hx
    have hr := hS.room
    have ht := hS.top
    apply hS.outside <;> rw [slot_toNat (by omega) ht (by omega)] <;> omega

set_option maxHeartbeats 600000 in
theorem write_header [Bindings] {initial s : RamState} (hS : EntryStack initial)
    (hg : Grows initial s) {boundary : ReturnBoundary} (outside : ¬ InProgram boundary.rip)
    (T0 : GTrack (headerChanges (stackPtr initial)) s s)
    (rip : s.RIP = 0x1017f6) (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 168) :
    ∃ t, Advances boundary 3 s t ∧ GTrack (headerChanges (stackPtr initial)) s t ∧
      t.RIP = 0x101808 ∧
      wd t (stackPtr initial - BitVec.ofNat 64 168) = rd s 5 ∧
      wd t (stackPtr initial - BitVec.ofNat 64 160) = rd s 7 ∧
      wd t (stackPtr initial - BitVec.ofNat 64 152) = 0 := by
  have p1 := rsp_addr0 (k := 168) rsp
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x1017f6 0x48 (by unfold RexWPrefix; decide) 5
      (.sib 4 none 0 .none) (by decide) (by decide) (by decide))
    T0 (program_text_slice T0.code 0x17f6 4 (by decide +kernel))
    (storePre_slot (k := 168) hS hg rip (by simp only [storeAddrAt, p1]) (by omega) (by omega)
      (code_inProgram 0x17f6 4 (by omega)))
    (code_ne_boundary outside 0x17fa (by omega))
    (by fits [headerChanges, p1]; exact .inr ⟨rfl, header_slot_fits hS (.inl rfl)⟩)
  change (movM64R64Effect 0x1017f6 5 (.sib 4 none 0 .none) s).Holds s u1 at e1
  have sp1 := sp_keep e1.agrees (by simp) rsp
  have p2 : ∀ x, (AddrMode.sib 4 none 0 (.d8 8)).addr u1 x =
      stackPtr initial - BitVec.ofNat 64 160 := rsp_addr (k := 168) sp1 8 8 rfl (by omega)
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x1017fa 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide))
    T1 (program_text_slice T1.code 0x17fa 5 (by decide +kernel))
    (storePre_slot (k := 160) hS (hg.step T1.agrees) e1.rip (by simp only [storeAddrAt, p2])
      (by omega) (by omega) (code_inProgram 0x17fa 5 (by omega)))
    (code_ne_boundary outside 0x17ff (by omega))
    (by fits [headerChanges, p2]; exact .inr ⟨rfl, header_slot_fits hS (.inr (.inl rfl))⟩)
  change (movM64R64Effect 0x1017fa 7 (.sib 4 none 0 (.d8 8)) u1).Holds u1 u2 at e2
  have sp2 := sp_keep e2.agrees (by simp) sp1
  have p3 : ∀ x, (AddrMode.sib 4 none 0 (.d8 16)).addr u2 x =
      stackPtr initial - BitVec.ofNat 64 152 := rsp_addr (k := 168) sp2 16 16 rfl (by omega)
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_m64_imm32_effect_step 0x1017ff 0x48 (by unfold RexWPrefix; decide)
      (.sib 4 none 0 (.d8 16)) (by decide) (by decide) (by decide) 0)
    T2 (program_text_slice T2.code 0x17ff 9 (by decide +kernel))
    (storePre_slot (k := 152) hS (hg.step T2.agrees) e2.rip (by simp only [storeAddrAt, p3])
      (by omega) (by omega) (code_inProgram 0x17ff 9 (by omega)))
    (code_ne_boundary outside 0x1808 (by omega))
    (by
      simp only [movM64Imm32Effect_components]
      fits [headerChanges, p3]
      exact .inr ⟨rfl, header_slot_fits hS (.inr (.inr rfl))⟩)
  change (movM64Imm32Effect 0x1017ff (.sib 4 none 0 (.d8 16)) 0 u2).Holds u2 u3 at e3
  refine ⟨u3, a1.trans (a2.trans a3), T3, e3.rip, ?_, ?_, ?_⟩
  · have keep3 : wd u3 (stackPtr initial - BitVec.ofNat 64 168) = wd u2 (stackPtr initial - BitVec.ofNat 64 168) := by
      apply gload e3.agrees
      intro c hc i hi
      simp only [movM64Imm32Effect_components, storeAddrAt, p3, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact slot_not_covers hi (by omega) (by omega) (by omega)
      · exact fun h => h
    have keep2 : wd u2 (stackPtr initial - BitVec.ofNat 64 168) = wd u1 (stackPtr initial - BitVec.ofNat 64 168) := by
      apply gload e2.agrees
      intro c hc i hi
      simp only [movM64R64Effect_components, storeAddrAt, p2, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact slot_not_covers hi (by omega) (by omega) (by omega)
      · exact fun h => h
    rw [keep3, keep2, ← p1 (0x1017f6 + 4)]
    exact e1.writes
  · have keep3 : wd u3 (stackPtr initial - BitVec.ofNat 64 160) = wd u2 (stackPtr initial - BitVec.ofNat 64 160) := by
      apply gload e3.agrees
      intro c hc i hi
      simp only [movM64Imm32Effect_components, storeAddrAt, p3, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact slot_not_covers hi (by omega) (by omega) (by omega)
      · exact fun h => h
    rw [keep3, ← p2 (0x1017fa + 5)]
    exact e2.writes.trans (e1.agrees.read (by simp))
  · rw [← p3 (0x1017ff + 9)]
    exact e3.writes

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
