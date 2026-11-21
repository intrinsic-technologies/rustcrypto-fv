import ChaCha20Poly1305.Proofs.Wrapper
import ChaCha20Poly1305.Proofs.Encrypt.Append.Stack
import X86Proofs.Instructions.Add.Generated.RR.Triple

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix
open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def setupChanges (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .flags, .rip,
    .mem (stackPtr initial - 152) 8, .mem (stackPtr initial - 104) 8,
    .mem (stackPtr initial - 96) 8, .mem (stackPtr initial - 88) 8,
    .mem (stackPtr initial - 176) 8]

theorem setup_slot_fits {initial : RamState}
    (hS : Stack.Valid initial 1168)
    (hA : (Stack.region initial 1168).Avoids
      (fun a => InProgram a ∨ pageTables.Contains a.toNat))
    {k : Nat} (hk : k ∈ [152, 104, 96, 88, 176]) :
    ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 k) 8).Covers a →
      (∃ c ∈ setupChanges initial, c.Covers a) ∧ ¬ InProgram a := by
  intro a ha
  refine ⟨⟨_, ?_, ha⟩, stack_slot_avoids hS hA ?_ a ha⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [setupChanges]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega

theorem setup_word_keep {cs : List Component} {u v : RamState} {I : BitVec 64}
    {k : Nat} (he : AgreesExcept cs u v) (hk : k ≤ 1104)
    (hc : ∀ c ∈ cs, c.isMem = false ∨ ∃ j : Nat,
      c = .mem (I - BitVec.ofNat 64 j) 8 ∧ (j + 8 ≤ k ∨ k + 8 ≤ j) ∧ j ≤ 1104) :
    wd v (I - BitVec.ofNat 64 k) = wd u (I - BitVec.ofNat 64 k) := by
  apply memLoad_congr
  intro i hi
  change i < 8 at hi
  simp only [memByte]
  congr 1
  apply he.byte
  intro c hm
  rcases hc c hm with hn | ⟨j, rfl, hj, hb⟩
  · exact nonmem_not_covers hn _
  · exact slot_not_covers hi (by omega) hk hb

theorem setup_run [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (hS : Stack.Valid initial 1168)
    (hA : (Stack.region initial 1168).Avoids
      (fun a => InProgram a ∨ pageTables.Contains a.toNat))
    (hG : Grows initial s) (R : ReadyToStep s) (C : CodeIn Extracted.programImage s)
    (hO : ¬ InProgram boundary.rip) (hRip : s.RIP = 0x101828)
    (hSp : stackPtr s = stackPtr initial - 168)
    (hRead : MemReadable s (stackPtr initial + 8) 8) :
    ∃ fuel t, Advances boundary fuel s t ∧
      GTrack (setupChanges initial) s t ∧ t.RIP = 0x100650 ∧
      stackPtr t = stackPtr initial - 176 ∧
      rd t 7 = stackPtr initial - 137 ∧ rd t 6 = stackPtr initial - 80 ∧
      rd t 9 = stackPtr initial - 104 ∧ rd t 2 = rd s 15 ∧ rd t 1 = rd s 14 ∧
      rd t 8 = wd s (stackPtr initial + 8) ∧
      wd t (stackPtr initial - 152) = rd s 5 + rd s 13 ∧
      wd t (stackPtr initial - 104) = wd s (stackPtr initial - 160) ∧
      wd t (stackPtr initial - 96) = wd s (stackPtr initial - 160) ∧
      wd t (stackPtr initial - 88) = rd s 5 + rd s 13 ∧
      wd t (stackPtr initial - 176) = 0x101866 := by
  have T0 : GTrack (setupChanges initial) s s := ⟨R, C, AgreesExcept.refl _ _⟩
  let u0 := s
  have S0 : stackPtr u0 = stackPtr initial - 168 := hSp
  have A1 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 0xb0)).addr u0 x = stackPtr initial + 8 := by
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    rw [show ((4 : BitVec 4).setWidth 5) = (4 : BitVec 5) from rfl, ← stackPtr_eq_read, S0, show (0xb0 : BitVec 32).signExtend 64 = (176 : BitVec 64) from rfl]
    bv_omega
  have F1 : Fits (setupChanges initial) (movR64M64Effect 0x101828 8 (.sib 4 none 0 (.d32 0xb0)) u0).components := by
    intro c hc
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step (mov_r64_m64_effect_step 0x101828 0x4c (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide))
    T0 (program_text_slice T0.code 0x1828 8 (by decide +kernel))
    ⟨hRip, by rw [A1]; exact hRead⟩ (code_ne_boundary hO 0x1830 (by omega)) F1
  change (movR64M64Effect 0x101828 8 (.sib 4 none 0 (.d32 0xb0)) u0).Holds u0 u1 at e1
  have S1 : stackPtr u1 = stackPtr initial - 168 := sp_keep e1.agrees (by simp) S0
  have F2 : Fits (setupChanges initial) (addR64R64Effect 0x101830 5 13 u1).components := by
    intro c hc
    simp only [addR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step (add_r64_r64_effect_step 0x101830 0x4c 0xed (by unfold RexWPrefix; decide) (by decide))
    T1 (program_text_slice T1.code 0x1830 3 (by decide +kernel))
    e1.rip (code_ne_boundary hO 0x1833 (by omega)) F2
  change (addR64R64Effect 0x101830 5 13 u1).Holds u1 u2 at e2
  have S2 : stackPtr u2 = stackPtr initial - 168 := sp_keep e2.agrees (by simp) S1
  have A3 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 0x10)).addr u2 x = stackPtr initial - 152 := by
    exact rsp_addr (k := 168) S2 0x10 16 rfl (by omega) x
  have F3 : Fits (setupChanges initial) (movM64R64Effect 0x101833 5 (.sib 4 none 0 (.d8 0x10)) u2).components := by
    simp only [Fits, movM64R64Effect_components, storeAddrAt, A3]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact .inr ⟨rfl, setup_slot_fits hS hA (k := 152) (by simp)⟩
    · exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step (mov_m64_r64_effect_step 0x101833 0x48 (by unfold RexWPrefix; decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
    T2 (program_text_slice T2.code 0x1833 5 (by decide +kernel))
    (stack_store_pre hS hA (fun a ha => T2.agrees.grow a (hG a ha)) (k := 152) (by omega) e2.rip (A3 _) (code_inProgram 0x1833 5 (by omega))) (code_ne_boundary hO 0x1838 (by omega)) F3
  change (movM64R64Effect 0x101833 5 (.sib 4 none 0 (.d8 0x10)) u2).Holds u2 u3 at e3
  have S3 : stackPtr u3 = stackPtr initial - 168 := sp_keep e3.agrees (by simp) S2
  have A4 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 0x8)).addr u3 x = stackPtr initial - 160 := by
    exact rsp_addr (k := 168) S3 0x8 8 rfl (by omega) x
  have F4 : Fits (setupChanges initial) (movR64M64Effect 0x101838 0 (.sib 4 none 0 (.d8 0x8)) u3).components := by
    intro c hc
    simp only [movR64M64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step (mov_r64_m64_effect_step 0x101838 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x1838 5 (by decide +kernel))
    ⟨e3.rip, by rw [A4]; exact stack_slot_readable (k := 160) hS (fun a ha => T3.agrees.grow a (hG a ha)) (by omega)⟩ (code_ne_boundary hO 0x183d (by omega)) F4
  change (movR64M64Effect 0x101838 0 (.sib 4 none 0 (.d8 0x8)) u3).Holds u3 u4 at e4
  have S4 : stackPtr u4 = stackPtr initial - 168 := sp_keep e4.agrees (by simp) S3
  have A5 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 0x40)).addr u4 x = stackPtr initial - 104 := by
    exact rsp_addr (k := 168) S4 0x40 64 rfl (by omega) x
  have F5 : Fits (setupChanges initial) (movM64R64Effect 0x10183d 0 (.sib 4 none 0 (.d8 0x40)) u4).components := by
    simp only [Fits, movM64R64Effect_components, storeAddrAt, A5]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact .inr ⟨rfl, setup_slot_fits hS hA (k := 104) (by simp)⟩
    · exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step (mov_m64_r64_effect_step 0x10183d 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide))
    T4 (program_text_slice T4.code 0x183d 5 (by decide +kernel))
    (stack_store_pre hS hA (fun a ha => T4.agrees.grow a (hG a ha)) (k := 104) (by omega) e4.rip (A5 _) (code_inProgram 0x183d 5 (by omega))) (code_ne_boundary hO 0x1842 (by omega)) F5
  change (movM64R64Effect 0x10183d 0 (.sib 4 none 0 (.d8 0x40)) u4).Holds u4 u5 at e5
  have S5 : stackPtr u5 = stackPtr initial - 168 := sp_keep e5.agrees (by simp) S4
  have A6 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 0x48)).addr u5 x = stackPtr initial - 96 := by
    exact rsp_addr (k := 168) S5 0x48 72 rfl (by omega) x
  have F6 : Fits (setupChanges initial) (movM64R64Effect 0x101842 0 (.sib 4 none 0 (.d8 0x48)) u5).components := by
    simp only [Fits, movM64R64Effect_components, storeAddrAt, A6]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact .inr ⟨rfl, setup_slot_fits hS hA (k := 96) (by simp)⟩
    · exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u6, a6, T6, e6⟩ := gtrack_step (mov_m64_r64_effect_step 0x101842 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide))
    T5 (program_text_slice T5.code 0x1842 5 (by decide +kernel))
    (stack_store_pre hS hA (fun a ha => T5.agrees.grow a (hG a ha)) (k := 96) (by omega) e5.rip (A6 _) (code_inProgram 0x1842 5 (by omega))) (code_ne_boundary hO 0x1847 (by omega)) F6
  change (movM64R64Effect 0x101842 0 (.sib 4 none 0 (.d8 0x48)) u5).Holds u5 u6 at e6
  have S6 : stackPtr u6 = stackPtr initial - 168 := sp_keep e6.agrees (by simp) S5
  have A7 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 0x50)).addr u6 x = stackPtr initial - 88 := by
    exact rsp_addr (k := 168) S6 0x50 80 rfl (by omega) x
  have F7 : Fits (setupChanges initial) (movM64R64Effect 0x101847 5 (.sib 4 none 0 (.d8 0x50)) u6).components := by
    simp only [Fits, movM64R64Effect_components, storeAddrAt, A7]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact .inr ⟨rfl, setup_slot_fits hS hA (k := 88) (by simp)⟩
    · exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u7, a7, T7, e7⟩ := gtrack_step (mov_m64_r64_effect_step 0x101847 0x48 (by unfold RexWPrefix; decide) 5 (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide))
    T6 (program_text_slice T6.code 0x1847 5 (by decide +kernel))
    (stack_store_pre hS hA (fun a ha => T6.agrees.grow a (hG a ha)) (k := 88) (by omega) e6.rip (A7 _) (code_inProgram 0x1847 5 (by omega))) (code_ne_boundary hO 0x184c (by omega)) F7
  change (movM64R64Effect 0x101847 5 (.sib 4 none 0 (.d8 0x50)) u6).Holds u6 u7 at e7
  have S7 : stackPtr u7 = stackPtr initial - 168 := sp_keep e7.agrees (by simp) S6
  have A8 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 0x1f)).addr u7 x = stackPtr initial - 137 := by
    exact rsp_addr (k := 168) S7 0x1f 31 rfl (by omega) x
  have F8 : Fits (setupChanges initial) (leaR64Effect 0x10184c 7 (.sib 4 none 0 (.d8 0x1f)) u7).components := by
    intro c hc
    simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u8, a8, T8, e8⟩ := gtrack_step (lea_r64_effect_step 0x10184c 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x1f)) (by decide) (by decide) (by decide))
    T7 (program_text_slice T7.code 0x184c 5 (by decide +kernel))
    e7.rip (code_ne_boundary hO 0x1851 (by omega)) F8
  change (leaR64Effect 0x10184c 7 (.sib 4 none 0 (.d8 0x1f)) u7).Holds u7 u8 at e8
  have S8 : stackPtr u8 = stackPtr initial - 168 := sp_keep e8.agrees (by simp) S7
  have A9 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 0x58)).addr u8 x = stackPtr initial - 80 := by
    exact rsp_addr (k := 168) S8 0x58 88 rfl (by omega) x
  have F9 : Fits (setupChanges initial) (leaR64Effect 0x101851 6 (.sib 4 none 0 (.d8 0x58)) u8).components := by
    intro c hc
    simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u9, a9, T9, e9⟩ := gtrack_step (lea_r64_effect_step 0x101851 0x48 (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide))
    T8 (program_text_slice T8.code 0x1851 5 (by decide +kernel))
    e8.rip (code_ne_boundary hO 0x1856 (by omega)) F9
  change (leaR64Effect 0x101851 6 (.sib 4 none 0 (.d8 0x58)) u8).Holds u8 u9 at e9
  have S9 : stackPtr u9 = stackPtr initial - 168 := sp_keep e9.agrees (by simp) S8
  have A10 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d8 0x40)).addr u9 x = stackPtr initial - 104 := by
    exact rsp_addr (k := 168) S9 0x40 64 rfl (by omega) x
  have F10 : Fits (setupChanges initial) (leaR64Effect 0x101856 9 (.sib 4 none 0 (.d8 0x40)) u9).components := by
    intro c hc
    simp only [leaR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u10, a10, T10, e10⟩ := gtrack_step (lea_r64_effect_step 0x101856 0x4c (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide))
    T9 (program_text_slice T9.code 0x1856 5 (by decide +kernel))
    e9.rip (code_ne_boundary hO 0x185b (by omega)) F10
  change (leaR64Effect 0x101856 9 (.sib 4 none 0 (.d8 0x40)) u9).Holds u9 u10 at e10
  have S10 : stackPtr u10 = stackPtr initial - 168 := sp_keep e10.agrees (by simp) S9
  have F11 : Fits (setupChanges initial) (movR64R64Effect 0x10185b 2 15 u10).components := by
    intro c hc
    simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u11, a11, T11, e11⟩ := gtrack_step (mov_r64_r64_effect_step 0x10185b 0x4c 0xfa (by unfold RexWPrefix; decide) (by decide))
    T10 (program_text_slice T10.code 0x185b 3 (by decide +kernel))
    e10.rip (code_ne_boundary hO 0x185e (by omega)) F11
  change (movR64R64Effect 0x10185b 2 15 u10).Holds u10 u11 at e11
  have S11 : stackPtr u11 = stackPtr initial - 168 := sp_keep e11.agrees (by simp) S10
  have F12 : Fits (setupChanges initial) (movR64R64Effect 0x10185e 1 14 u11).components := by
    intro c hc
    simp only [movR64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u12, a12, T12, e12⟩ := gtrack_step (mov_r64_r64_effect_step 0x10185e 0x4c 0xf1 (by unfold RexWPrefix; decide) (by decide))
    T11 (program_text_slice T11.code 0x185e 3 (by decide +kernel))
    e11.rip (code_ne_boundary hO 0x1861 (by omega)) F12
  change (movR64R64Effect 0x10185e 1 14 u11).Holds u11 u12 at e12
  have S12 : stackPtr u12 = stackPtr initial - 168 := sp_keep e12.agrees (by simp) S11
  have A13 : pushAddr u12 = stackPtr initial - 176 := by
    rw [pushAddr, S12, BitVec.sub_sub]; rfl
  have F13 : Fits (setupChanges initial) (callEffect (fun _ => branchTarget 0x101861 5 ((0xffffedea : BitVec 32).signExtend 64)) (0x101861 + BitVec.ofNat 64 5) u12).components := by
    simp only [Fits, callEffect, pushEffect_components, A13]
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact .inl ⟨rfl, by simp [setupChanges]⟩
    · exact .inr ⟨rfl, setup_slot_fits hS hA (k := 176) (by simp)⟩
    · exact .inl ⟨rfl, by simp [setupChanges]⟩
  obtain ⟨u13, a13, T13, e13⟩ := gtrack_step (call_rel32_effect_step 0x101861 0xffffedea (by decide))
    T12 (program_text_slice T12.code 0x1861 5 (by decide +kernel))
    (stack_store_pre hS hA (fun a ha => T12.agrees.grow a (hG a ha)) (k := 176) (by omega) e12.rip A13 (code_inProgram 0x1861 5 (by omega))) (code_ne_boundary hO 0x650 (by omega)) F13
  change (callEffect (fun _ => branchTarget 0x101861 5 ((0xffffedea : BitVec 32).signExtend 64)) (0x101861 + BitVec.ofNat 64 5) u12).Holds u12 u13 at e13
  have K152 : wd u13 (stackPtr initial - 152) = wd u3 (stackPtr initial - 152) := by
      apply setup_word_keep (k := 152) (((((((((e4.agrees.trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees) (by omega)
      intro c hc
      simp only [List.mem_append, movR64M64Effect_components, movM64R64Effect_components, leaR64Effect_components, movR64R64Effect_components, callEffect, pushEffect_components, storeAddrAt, A5, A6, A7, A13, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Or.inl rfl
        | exact Or.inr ⟨152, rfl, by omega, by omega⟩
        | exact Or.inr ⟨104, rfl, by omega, by omega⟩
        | exact Or.inr ⟨96, rfl, by omega, by omega⟩
        | exact Or.inr ⟨88, rfl, by omega, by omega⟩
        | exact Or.inr ⟨176, rfl, by omega, by omega⟩
  have K104 : wd u13 (stackPtr initial - 104) = wd u5 (stackPtr initial - 104) := by
      apply setup_word_keep (k := 104) (((((((e6.agrees.trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees) (by omega)
      intro c hc
      simp only [List.mem_append, movM64R64Effect_components, leaR64Effect_components, movR64R64Effect_components, callEffect, pushEffect_components, storeAddrAt, A6, A7, A13, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Or.inl rfl
        | exact Or.inr ⟨152, rfl, by omega, by omega⟩
        | exact Or.inr ⟨104, rfl, by omega, by omega⟩
        | exact Or.inr ⟨96, rfl, by omega, by omega⟩
        | exact Or.inr ⟨88, rfl, by omega, by omega⟩
        | exact Or.inr ⟨176, rfl, by omega, by omega⟩
  have K96 : wd u13 (stackPtr initial - 96) = wd u6 (stackPtr initial - 96) := by
      apply setup_word_keep (k := 96) ((((((e7.agrees.trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees) (by omega)
      intro c hc
      simp only [List.mem_append, movM64R64Effect_components, leaR64Effect_components, movR64R64Effect_components, callEffect, pushEffect_components, storeAddrAt, A7, A13, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Or.inl rfl
        | exact Or.inr ⟨152, rfl, by omega, by omega⟩
        | exact Or.inr ⟨104, rfl, by omega, by omega⟩
        | exact Or.inr ⟨96, rfl, by omega, by omega⟩
        | exact Or.inr ⟨88, rfl, by omega, by omega⟩
        | exact Or.inr ⟨176, rfl, by omega, by omega⟩
  have K88 : wd u13 (stackPtr initial - 88) = wd u7 (stackPtr initial - 88) := by
      apply setup_word_keep (k := 88) (((((e8.agrees.trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees) (by omega)
      intro c hc
      simp only [List.mem_append, leaR64Effect_components, movR64R64Effect_components, callEffect, pushEffect_components, A13, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact Or.inl rfl
        | exact Or.inr ⟨152, rfl, by omega, by omega⟩
        | exact Or.inr ⟨104, rfl, by omega, by omega⟩
        | exact Or.inr ⟨96, rfl, by omega, by omega⟩
        | exact Or.inr ⟨88, rfl, by omega, by omega⟩
        | exact Or.inr ⟨176, rfl, by omega, by omega⟩
  have V2 : rd u2 5 = rd s 5 + rd s 13 := by
    simp only [rd]
    rw [e2.writes, e1.agrees.read (by simp), e1.agrees.read (by simp)]
  have V4 : rd u4 0 = wd s (stackPtr initial - 160) := by
    simp only [rd, wd]
    rw [e4.writes, A4]
    apply setup_word_keep (k := 160) ((e1.agrees.trans e2.agrees).trans e3.agrees) (by omega)
    intro c hc
    simp only [List.mem_append, movR64M64Effect_components, addR64R64Effect_components,
      movM64R64Effect_components, storeAddrAt, A3,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr ⟨152, rfl, by omega, by omega⟩
  refine ⟨_, u13, ((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13), T13, e13.rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (show stackPtr u13 = pushAddr u12 from e13.writes.1).trans A13
  · simp only [rd]
    rw [(((((e9.agrees.trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees)).read (by simp), e8.writes, A8]
  · simp only [rd]
    rw [((((e10.agrees.trans e11.agrees).trans e12.agrees).trans e13.agrees)).read (by simp), e9.writes, A9]
  · simp only [rd]
    rw [(((e11.agrees.trans e12.agrees).trans e13.agrees)).read (by simp), e10.writes, A10]
  · simp only [rd]
    rw [((e12.agrees.trans e13.agrees)).read (by simp), e11.writes]
    exact ((((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees)).read (by simp)
  · simp only [rd]
    rw [(e13.agrees).read (by simp), e12.writes]
    exact (((((((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees)).read (by simp)
  · simp only [rd, wd]
    rw [((((((((((((e2.agrees.trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).trans e12.agrees).trans e13.agrees)).read (by simp), e1.writes, A1]
  · rw [K152]
    have W : wd u3 (storeAddrAt 0x101833 (.sib 4 none 0 (.d8 0x10)) 5 u2) = rd u2 5 := e3.writes
    simp only [storeAddrAt, A3] at W
    rw [W]
    exact V2
  · rw [K104]
    have W : wd u5 (storeAddrAt 0x10183d (.sib 4 none 0 (.d8 0x40)) 5 u4) = rd u4 0 := e5.writes
    simp only [storeAddrAt, A5] at W
    rw [W]
    exact V4
  · rw [K96]
    have W : wd u6 (storeAddrAt 0x101842 (.sib 4 none 0 (.d8 0x48)) 5 u5) = rd u5 0 := e6.writes
    simp only [storeAddrAt, A6] at W
    rw [W]
    simp only [rd]
    rw [e5.agrees.read (by simp)]
    exact V4
  · rw [K88]
    have W : wd u7 (storeAddrAt 0x101847 (.sib 4 none 0 (.d8 0x50)) 5 u6) = rd u6 5 := e7.writes
    simp only [storeAddrAt, A7] at W
    rw [W]
    simp only [rd]
    rw [((((e3.agrees.trans e4.agrees).trans e5.agrees).trans e6.agrees)).read (by simp)]
    exact V2
  · have W : wd u13 (pushAddr u12) = 0x101866 := e13.writes.2
    rw [A13] at W
    exact W

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
