import ChaCha20Poly1305.Proofs.Wrapper
import ChaCha20Poly1305.Proofs.MemoryContracts
import X86Proofs.Instructions.Add.Generated.RR.Triple

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def copySetupChanges (sp : BitVec 64) : List Component :=
  [.reg 7, .reg 6, .reg 2, .reg 4, .flags, .rip, .mem (sp - BitVec.ofNat 64 176) 8]

theorem memcpy_pointer_readable {s : RamState} (hc : CodeIn Extracted.programImage s) :
    MemReadable s 0x2013a8 8 := by
  have hb := (hc.slice_of_section (sec := ⟨Extracted.rodataAddress, Extracted.rodataBytes⟩)
    (by simp [Extracted.programSections]) 0x13a8 8 (by decide +kernel)).bytesAt
  refine ⟨by decide, fun i hi => ?_⟩
  have h := hb i (by simpa only [chunked_toListFrom_length] using hi)
  have ha : Extracted.rodataAddress + BitVec.ofNat 64 0x13a8 = 0x2013a8 := by decide +kernel
  change s.external[Extracted.rodataAddress + BitVec.ofNat 64 0x13a8 + BitVec.ofNat 64 i]? = _ at h
  rw [ha] at h
  rw [h]
  rfl

set_option maxHeartbeats 600000 in
theorem call_copy [Bindings] {initial s : RamState} (hS : EntryStack initial)
    (hg : Grows initial s) {boundary : ReturnBoundary} (outside : ¬ InProgram boundary.rip)
    (T0 : GTrack (copySetupChanges (stackPtr initial)) s s)
    (rip : s.RIP = 0x101819) (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 168)
    (rbp : rd s 5 = 0) :
    ∃ t, Advances boundary 4 s t ∧ GTrack (copySetupChanges (stackPtr initial)) s t ∧
      t.RIP = 0x102dc0 ∧ stackPtr t = stackPtr initial - BitVec.ofNat 64 176 ∧
      rd t 7 = rd s 7 ∧ rd t 6 = rd s 12 ∧ rd t 2 = rd s 13 ∧
      wd t (stackPtr initial - BitVec.ofNat 64 176) = 0x101828 := by
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (add_r64_r64_effect_step 0x101819 0x48 0xef (by unfold RexWPrefix; decide) (by decide))
    T0 (program_text_slice T0.code 0x1819 3 (by decide +kernel)) rip
    (code_ne_boundary outside 0x181c (by omega))
    (by simp only [addR64R64Effect_components]; fits [copySetupChanges])
  change (addR64R64Effect 0x101819 7 5 s).Holds s u1 at e1
  have v1 : rd u1 7 = rd s 7 := by
    rw [show rd u1 7 = _ from e1.writes]
    simp only [rbp]
    exact BitVec.add_zero _
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x10181c 0x4c 0xe6 (by unfold RexWPrefix; decide) (by decide))
    T1 (program_text_slice T1.code 0x181c 3 (by decide +kernel)) e1.rip
    (code_ne_boundary outside 0x181f (by omega)) (by fits [copySetupChanges])
  change (movR64R64Effect 0x10181c 6 12 u1).Holds u1 u2 at e2
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x10181f 0x4c 0xea (by unfold RexWPrefix; decide) (by decide))
    T2 (program_text_slice T2.code 0x181f 3 (by decide +kernel)) e2.rip
    (code_ne_boundary outside 0x1822 (by omega)) (by fits [copySetupChanges])
  change (movR64R64Effect 0x10181f 2 13 u2).Holds u2 u3 at e3
  have sp3 := sp_keep ((e1.agrees.trans e2.agrees).trans e3.agrees) (by simp) rsp
  have pa : pushAddr u3 = stackPtr initial - BitVec.ofNat 64 176 := by
    rw [pushAddr, sp3]; bv_omega
  have ptr : callMemPtr 0x101822 (.rip 0xffb80) u3 = 0x102dc0 :=
    MemoryContracts.memcpy_slot u3 T3.code
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (call_m64_effect_step 0x101822 (.rip 0xffb80) (by decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x1822 6 (by decide +kernel))
    ⟨⟨storePre_slot (k := 176) hS (hg.step T3.agrees) e3.rip pa (by omega) (by omega)
      (code_inProgram 0x1822 6 (by omega)), by rw [ptr]; decide⟩,
      memcpy_pointer_readable T3.code⟩
    (by change callMemPtr _ _ _ ≠ _; rw [ptr]; exact code_ne_boundary outside 0x2dc0 (by omega))
    (by
      simp only [Fits, callEffect, pushEffect_components, pa]
      simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      refine ⟨.inl ⟨rfl, by simp [copySetupChanges]⟩, .inr ⟨rfl, ?_⟩,
        .inl ⟨rfl, by simp [copySetupChanges]⟩⟩
      intro x hx
      refine ⟨⟨_, by simp [copySetupChanges], hx⟩, ?_⟩
      obtain ⟨i, hi, rfl⟩ := hx
      have hr := hS.room
      have ht := hS.top
      apply hS.outside <;> rw [slot_toNat (by omega) ht (by omega)] <;> omega)
  change (callEffect (callMemPtr 0x101822 (.rip 0xffb80)) (0x101822 + BitVec.ofNat 64 6) u3).Holds u3 u4 at e4
  refine ⟨u4, a1.trans (a2.trans (a3.trans a4)), T4, e4.rip.trans ptr,
    e4.writes.1.trans pa, ?_, ?_, ?_, ?_⟩
  · exact (((e2.agrees.trans e3.agrees).trans e4.agrees).read (by simp [pa])).trans v1
  · exact ((e3.agrees.trans e4.agrees).read (by simp [pa])).trans
      (e2.writes.trans (e1.agrees.read (by simp)))
  · exact (e4.agrees.read (by simp [pa])).trans
      (e3.writes.trans (T2.agrees.read (by simp [copySetupChanges])))
  · rw [← pa]
    exact e4.writes.2

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
