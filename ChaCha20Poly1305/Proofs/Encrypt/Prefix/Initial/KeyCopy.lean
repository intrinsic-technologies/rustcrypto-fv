import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def keyCopyChanges (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .rip, .mem (stackPtr initial - 80) 32]

theorem key_copy [Bindings] {initial s : RamState} (hs : EntryStack initial)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (track : GTrack (keyCopyChanges initial) s s)
    (grows : Grows initial s)
    (entry : s.RIP = 0x10177a) (sp : stackPtr s = stackPtr initial - 168)
    (kb : (rd s 7).toNat + 32 < 2^32)
    (kr : ∀ j < 32, (s.external[rd s 7 + BitVec.ofNat 64 j]?).isSome)
    (ks : (stackPtr initial).toNat + 8 ≤ (rd s 7).toNat ∨
      (rd s 7).toNat + 32 ≤ (stackPtr initial).toNat - 1104) :
    ∃ t, Advances (returnBoundary initial) 8 s t ∧
      GTrack (keyCopyChanges initial) s t ∧ t.RIP = 0x10179d ∧
      ∀ j : Fin 4, wd t (stackPtr initial - 80 + BitVec.ofNat 64 (8*j.val)) =
        wd s (rd s 7 + BitVec.ofNat 64 (8*j.val)) := by
  have hfit (u : RamState) (p : BitVec 64) (r : BitVec 5) (d : BitVec 8)
      (k : Nat) (hk : 56 ≤ k ∧ k ≤ 80)
      (ha : ∀ x, (AddrMode.sib 4 none 0 (.d8 d)).addr u x =
        stackPtr initial - BitVec.ofNat 64 k) :
      Fits (keyCopyChanges initial)
        (movM64R64Effect p r (.sib 4 none 0 (.d8 d)) u).components := by
    fits [ha, keyCopyChanges]
    apply Or.inr
    refine ⟨rfl, ?_⟩
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hx
    constructor
    · refine ⟨.mem (stackPtr initial - 80) 32, by simp,
        80 - k + j, by omega, ?_⟩
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
        show (80 : BitVec 64).toNat = 80 from rfl]
      have := (stackPtr initial).isLt
      omega
    · have := hs.room
      apply hs.outside <;> rw [slot_toNat (by omega) hs.top (by omega)] <;> omega
  have hsp {u : RamState} (T : GTrack (keyCopyChanges initial) s u) :
      stackPtr u = stackPtr initial - 168 :=
    sp_keep T.agrees (by simp [keyCopyChanges]) sp
  have hkey {u : RamState} (T : GTrack (keyCopyChanges initial) s u) :
      rd u 7 = rd s 7 := T.agrees.read (by simp [keyCopyChanges])
  have hload {u : RamState} (T : GTrack (keyCopyChanges initial) s u)
      (d : Nat) (hd : d + 8 ≤ 32) :
      wd u (rd s 7 + BitVec.ofNat 64 d) = wd s (rd s 7 + BitVec.ofNat 64 d) := by
    apply gload T.agrees
    intro c hc i hi
    simp only [keyCopyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals first
      | exact nonmem_not_covers rfl _
      | (have hr := hs.room; have ht := hs.top
         apply mem_not_covers <;>
           simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
             show (80 : BitVec 64).toNat = 80 from rfl] <;> omega)
  obtain ⟨s1, a1, T1, e1⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x10177a 0x48 (by unfold RexWPrefix; decide) 0
      (.base 7 (.d8 0x18)) (by decide) (by decide) (by decide))
    track (program_text_slice track.code 0x177a 4 (by decide +kernel))
    ⟨entry, by
      rw [rdi_addr (hkey track) 0x18 24 rfl]
      exact key_readable track.agrees.grow kb kr 24 (by omega)⟩
    (code_ne_boundary outside 0x177e (by omega))
    (by fits [keyCopyChanges])
  change (movR64M64Effect 0x10177a 0 (.base 7 (.d8 0x18)) s).Holds s s1 at e1
  have L1 : rd s1 0 = wd s (rd s 7 + BitVec.ofNat 64 24) := by
    have h : rd s1 0 = wd s
        ((AddrMode.base 7 (.d8 0x18)).addr s (0x10177a + BitVec.ofNat 64 4)) := e1.writes
    rw [h]
    change wd s _ = _
    rw [rdi_addr (hkey track) 0x18 24 rfl]
  have A2 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x70)).addr s1 x =
      stackPtr initial - BitVec.ofNat 64 56 :=
    rsp_addr (k := 168) (hsp T1) 0x70 112 rfl (by omega)
  obtain ⟨s2, a2, T2, e2⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x10177e 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide))
    T1 (program_text_slice T1.code 0x177e 5 (by decide +kernel))
    (storePre_slot hs (grows.step T1.agrees) e1.rip (A2 _) (by omega) (by omega)
      (code_inProgram 0x177e 5 (by omega)))
    (code_ne_boundary outside 0x1783 (by omega))
    (hfit s1 _ 0 0x70 56 (by omega) A2)
  change (movM64R64Effect 0x10177e 0 (.sib 4 none 0 (.d8 0x70)) s1).Holds s1 s2 at e2
  have M2 : wd s2 (stackPtr initial - BitVec.ofNat 64 56) = rd s1 0 := by
    rw [← A2 (0x10177e + BitVec.ofNat 64 5)]
    exact e2.writes
  obtain ⟨s3, a3, T3, e3⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x101783 0x48 (by unfold RexWPrefix; decide) 0
      (.base 7 (.d8 0x10)) (by decide) (by decide) (by decide))
    T2 (program_text_slice T2.code 0x1783 4 (by decide +kernel))
    ⟨e2.rip, by
      rw [rdi_addr (hkey T2) 0x10 16 rfl]
      exact key_readable T2.agrees.grow kb kr 16 (by omega)⟩
    (code_ne_boundary outside 0x1787 (by omega))
    (by fits [keyCopyChanges])
  change (movR64M64Effect 0x101783 0 (.base 7 (.d8 0x10)) s2).Holds s2 s3 at e3
  have L3 : rd s3 0 = wd s (rd s 7 + BitVec.ofNat 64 16) := by
    have h : rd s3 0 = wd s2
        ((AddrMode.base 7 (.d8 0x10)).addr s2 (0x101783 + BitVec.ofNat 64 4)) := e3.writes
    rw [h]
    change wd s2 _ = _
    rw [rdi_addr (hkey T2) 0x10 16 rfl]
    exact hload T2 16 (by omega)
  have A4 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x68)).addr s3 x =
      stackPtr initial - BitVec.ofNat 64 64 :=
    rsp_addr (k := 168) (hsp T3) 0x68 104 rfl (by omega)
  obtain ⟨s4, a4, T4, e4⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x101787 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x68)) (by decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x1787 5 (by decide +kernel))
    (storePre_slot hs (grows.step T3.agrees) e3.rip (A4 _) (by omega) (by omega)
      (code_inProgram 0x1787 5 (by omega)))
    (code_ne_boundary outside 0x178c (by omega))
    (hfit s3 _ 0 0x68 64 (by omega) A4)
  change (movM64R64Effect 0x101787 0 (.sib 4 none 0 (.d8 0x68)) s3).Holds s3 s4 at e4
  have W4 : StepWrites initial 64
      (movM64R64Effect 0x101787 0 (.sib 4 none 0 (.d8 0x68)) s3).components := by
    step_writes [A4]
  have M4 : wd s4 (stackPtr initial - BitVec.ofNat 64 64) = rd s3 0 := by
    rw [← A4 (0x101787 + BitVec.ofNat 64 5)]
    exact e4.writes
  obtain ⟨s5, a5, T5, e5⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x10178c 0x48 (by unfold RexWPrefix; decide) 0
      (.base 7 .none) (by decide) (by decide) (by decide))
    T4 (program_text_slice T4.code 0x178c 3 (by decide +kernel))
    ⟨e4.rip, by
      rw [rdi_addr0 (hkey T4)]
      exact key_readable T4.agrees.grow kb kr 0 (by omega)⟩
    (code_ne_boundary outside 0x178f (by omega))
    (by fits [keyCopyChanges])
  change (movR64M64Effect 0x10178c 0 (.base 7 .none) s4).Holds s4 s5 at e5
  have L5 : rd s5 0 = wd s (rd s 7 + BitVec.ofNat 64 0) := by
    have h : rd s5 0 = wd s4
        ((AddrMode.base 7 .none).addr s4 (0x10178c + BitVec.ofNat 64 3)) := e5.writes
    rw [h]
    change wd s4 _ = _
    rw [rdi_addr0 (hkey T4)]
    exact hload T4 0 (by omega)
  obtain ⟨s6, a6, T6, e6⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x10178f 0x48 (by unfold RexWPrefix; decide) 1
      (.base 7 (.d8 0x8)) (by decide) (by decide) (by decide))
    T5 (program_text_slice T5.code 0x178f 4 (by decide +kernel))
    ⟨e5.rip, by
      rw [rdi_addr (hkey T5) 0x8 8 rfl]
      exact key_readable T5.agrees.grow kb kr 8 (by omega)⟩
    (code_ne_boundary outside 0x1793 (by omega))
    (by fits [keyCopyChanges])
  change (movR64M64Effect 0x10178f 1 (.base 7 (.d8 0x8)) s5).Holds s5 s6 at e6
  have L6 : rd s6 1 = wd s (rd s 7 + BitVec.ofNat 64 8) := by
    have h : rd s6 1 = wd s5
        ((AddrMode.base 7 (.d8 0x8)).addr s5 (0x10178f + BitVec.ofNat 64 4)) := e6.writes
    rw [h]
    change wd s5 _ = _
    rw [rdi_addr (hkey T5) 0x8 8 rfl]
    exact hload T5 8 (by omega)
  have A7 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x60)).addr s6 x =
      stackPtr initial - BitVec.ofNat 64 72 :=
    rsp_addr (k := 168) (hsp T6) 0x60 96 rfl (by omega)
  obtain ⟨s7, a7, T7, e7⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x101793 0x48 (by unfold RexWPrefix; decide) 1
      (.sib 4 none 0 (.d8 0x60)) (by decide) (by decide) (by decide))
    T6 (program_text_slice T6.code 0x1793 5 (by decide +kernel))
    (storePre_slot hs (grows.step T6.agrees) e6.rip (A7 _) (by omega) (by omega)
      (code_inProgram 0x1793 5 (by omega)))
    (code_ne_boundary outside 0x1798 (by omega))
    (hfit s6 _ 1 0x60 72 (by omega) A7)
  change (movM64R64Effect 0x101793 1 (.sib 4 none 0 (.d8 0x60)) s6).Holds s6 s7 at e7
  have W7 : StepWrites initial 72
      (movM64R64Effect 0x101793 1 (.sib 4 none 0 (.d8 0x60)) s6).components := by
    step_writes [A7]
  have M7 : wd s7 (stackPtr initial - BitVec.ofNat 64 72) = rd s6 1 := by
    rw [← A7 (0x101793 + BitVec.ofNat 64 5)]
    exact e7.writes
  have A8 : ∀ x, (AddrMode.sib 4 none 0 (.d8 0x58)).addr s7 x =
      stackPtr initial - BitVec.ofNat 64 80 :=
    rsp_addr (k := 168) (hsp T7) 0x58 88 rfl (by omega)
  obtain ⟨s8, a8, T8, e8⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x101798 0x48 (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide))
    T7 (program_text_slice T7.code 0x1798 5 (by decide +kernel))
    (storePre_slot hs (grows.step T7.agrees) e7.rip (A8 _) (by omega) (by omega)
      (code_inProgram 0x1798 5 (by omega)))
    (code_ne_boundary outside 0x179d (by omega))
    (hfit s7 _ 0 0x58 80 (by omega) A8)
  change (movM64R64Effect 0x101798 0 (.sib 4 none 0 (.d8 0x58)) s7).Holds s7 s8 at e8
  have W8 : StepWrites initial 80
      (movM64R64Effect 0x101798 0 (.sib 4 none 0 (.d8 0x58)) s7).components := by
    step_writes [A8]
  have M8 : wd s8 (stackPtr initial - BitVec.ofNat 64 80) = rd s7 0 := by
    rw [← A8 (0x101798 + BitVec.ofNat 64 5)]
    exact e8.writes
  have V0 : wd s8 (stackPtr initial - BitVec.ofNat 64 80) =
      wd s (rd s 7 + BitVec.ofNat 64 0) := by
    rw [M8]
    exact (e7.agrees.read (r := 0) (by simp)).trans
      ((e6.agrees.read (r := 0) (by simp)).trans L5)
  have V1 : wd s8 (stackPtr initial - BitVec.ofNat 64 72) =
      wd s (rd s 7 + BitVec.ofNat 64 8) := by
    exact (W8.keep e8.agrees (k' := 72) (by omega) (by omega)).trans
      (M7.trans L6)
  have V2 : wd s8 (stackPtr initial - BitVec.ofNat 64 64) =
      wd s (rd s 7 + BitVec.ofNat 64 16) := by
    exact (W8.keep e8.agrees (k' := 64) (by omega) (by omega)).trans
      ((W7.keep e7.agrees (k' := 64) (by omega) (by omega)).trans
      ((mem_keep e6.agrees
        (by simp [movR64M64Effect_components, Component.isMem]) _).trans
      ((mem_keep e5.agrees
        (by simp [movR64M64Effect_components, Component.isMem]) _).trans
      (M4.trans L3))))
  have V3 : wd s8 (stackPtr initial - BitVec.ofNat 64 56) =
      wd s (rd s 7 + BitVec.ofNat 64 24) := by
    exact (W8.keep e8.agrees (k' := 56) (by omega) (by omega)).trans
      ((W7.keep e7.agrees (k' := 56) (by omega) (by omega)).trans
      ((mem_keep e6.agrees
        (by simp [movR64M64Effect_components, Component.isMem]) _).trans
      ((mem_keep e5.agrees
        (by simp [movR64M64Effect_components, Component.isMem]) _).trans
      ((W4.keep e4.agrees (k' := 56) (by omega) (by omega)).trans
      ((mem_keep e3.agrees
        (by simp [movR64M64Effect_components, Component.isMem]) _).trans
      (M2.trans L1))))))
  refine ⟨s8, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans
    (a6.trans (a7.trans a8)))))), T8, e8.rip, ?_⟩
  intro j
  rcases j with ⟨j, hj⟩
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · change wd s8 (stackPtr initial - 80 + BitVec.ofNat 64 (8 * 0)) =
        wd s (rd s 7 + BitVec.ofNat 64 0)
    rw [show stackPtr initial - 80 + BitVec.ofNat 64 (8 * 0) =
      stackPtr initial - BitVec.ofNat 64 80 from by bv_omega]
    exact V0
  · change wd s8 (stackPtr initial - 80 + BitVec.ofNat 64 (8 * 1)) =
        wd s (rd s 7 + BitVec.ofNat 64 8)
    rw [show stackPtr initial - 80 + BitVec.ofNat 64 (8 * 1) =
      stackPtr initial - BitVec.ofNat 64 72 from by bv_omega]
    exact V1
  · change wd s8 (stackPtr initial - 80 + BitVec.ofNat 64 (8 * 2)) =
        wd s (rd s 7 + BitVec.ofNat 64 16)
    rw [show stackPtr initial - 80 + BitVec.ofNat 64 (8 * 2) =
      stackPtr initial - BitVec.ofNat 64 64 from by bv_omega]
    exact V2
  · change wd s8 (stackPtr initial - 80 + BitVec.ofNat 64 (8 * 3)) =
        wd s (rd s 7 + BitVec.ofNat 64 24)
    rw [show stackPtr initial - 80 + BitVec.ofNat 64 (8 * 3) =
      stackPtr initial - BitVec.ofNat 64 56 from by bv_omega]
    exact V3

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
