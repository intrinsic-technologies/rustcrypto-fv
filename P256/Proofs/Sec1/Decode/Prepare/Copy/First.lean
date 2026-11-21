import P256.Proofs.Sec1.Decode.Prepare.Copy.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare.Copy

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def copyFirstWindow {α : Type} (f : Nat → α) : Nat → α :=
  let f3 := update f (fun i ↦ f (0+i)) 156 4
  let f4 := update f3 (fun i ↦ f (3+i)) 159 4
  let f7 := update f4 (fun i ↦ f4 (11+i)) 80 8
  let f9 := update f7 (fun i ↦ f7 (19+i)) 88 8
  let f11 := update f9 (fun i ↦ f9 (27+i)) 96 8
  let f13 := update f11 (fun i ↦ f11 (35+i)) 104 8
  let f15 := update f13 (fun i ↦ f13 (43+i)) 112 8
  let f17 := update f15 (fun i ↦ f15 (51+i)) 120 8
  let f19 := update f17 (fun i ↦ f17 (57+i)) 126 8
  f19

set_option maxHeartbeats 1600000 in
theorem runFirst [Bindings] {initial s0 : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {f : Nat → UInt8} (pre : DecodePre initial boundary bytes)
    (fr0 : Frame initial s0) (w0 : Window s0 f) (rip : s0.RIP = 0x10e561) :
    ∃ t fuel, Advances boundary fuel s0 t ∧ Frame initial t ∧ t.RIP = 0x10e5c0 ∧
      Window t (copyFirstWindow f) ∧ t.regValue .r12 = s0.regValue .r12 ∧
      t.regValue .r15 = s0.regValue .r15 ∧
      (t.regValue .rax).setWidth 32 = memLoad t.external (stackPtr t + 7) 32 := by
  obtain ⟨s1, a1, ready1, e1⟩ := (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10e561 0 (.sib 4 none 0 .none) (by decide) rfl rfl).advances
    (readyToStep fr0.machine fr0.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr0.loaded) 0xe561 _
      (by decide) (by decide +kernel))
    (show _ from ⟨rip, stack_readable pre fr0 (offset := 0) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe564 (by decide)))
  have g1 : AgreesExcept [.reg 0, .rip] s0 s1 := e1.agrees
  have fr1 := fr0.after_registers pre ready1 g1
    (by simp [Component.Covers]) (by simp)
  have w1 := window_registers w0 g1 (by simp) (by simp [Component.Covers])
  have v1 : s1.regValue .rax =
      (memLoad s0.external (stackPtr s0 + 0) 32).setWidth 64 := e1.writes
  have r12_1 : s1.regValue .r12 = s0.regValue .r12 :=
    (g1.read (n := 64) (r := 12) (by simp)).trans rfl
  have r15_1 : s1.regValue .r15 = s0.regValue .r15 :=
    (g1.read (n := 64) (r := 15) (by simp)).trans rfl
  obtain ⟨s2, a2, ready2, e2⟩ := (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10e564 1 (.sib 4 none 0 (.d8 3)) (by decide) rfl rfl).advances
    (readyToStep fr1.machine fr1.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr1.loaded) 0xe564 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e1.rip, stack_readable pre fr1 (offset := 3) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe568 (by decide)))
  have g2 : AgreesExcept [.reg 1, .rip] s1 s2 := e2.agrees
  have fr2 := fr1.after_registers pre ready2 g2
    (by simp [Component.Covers]) (by simp)
  have w2 := window_registers w1 g2 (by simp) (by simp [Component.Covers])
  have v2 : s2.regValue .rcx =
      (memLoad s1.external (stackPtr s1 + 3) 32).setWidth 64 := e2.writes
  have r12_2 : s2.regValue .r12 = s0.regValue .r12 :=
    (g2.read (n := 64) (r := 12) (by simp)).trans r12_1
  have r15_2 : s2.regValue .r15 = s0.regValue .r15 :=
    (g2.read (n := 64) (r := 15) (by simp)).trans r15_1
  obtain ⟨s3, a3, ready3, e3⟩ := (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10e568 0 (.sib 4 none 0 (.d32 156)) (by decide) rfl rfl).advances
    (readyToStep fr2.machine fr2.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr2.loaded) 0xe568 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e2.rip, stack_writable pre fr2 (offset := 156) (by decide) (by decide), stack_code pre fr2 (offset := 156) (codeOffset := 0xe568) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe56f (by decide)))
  have g3 : AgreesExcept [.mem (stackPtr s2 + 156) 4, .rip] s2 s3 := by
    have h := e3.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr3 := frame_store pre fr2 ready3 g3 (by decide)
  have value3 : memLoad s3.external (stackPtr s2 + 156) 32 =
      memLoad s0.external (stackPtr s0 + 0) 32 := by
    have h : memLoad s3.external (stackPtr s2 + 156) 32 =
      (s2.regValue .rax).setWidth 32 := e3.writes
    have reg : s2.regValue .rax =
      (memLoad s0.external (stackPtr s0 + 0) 32).setWidth 64 := (g2.read (n := 64) (r := 0) (by simp)).trans v1
    rw [h, reg]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  let f3 := update f (fun i ↦ f (0+i)) 156 4
  have w3 : Window s3 f3 := window_store w2 w0
    (by decide) (by decide) g3 value3
  have r12_3 : s3.regValue .r12 = s0.regValue .r12 :=
    (g3.read (n := 64) (r := 12) (by simp)).trans r12_2
  have r15_3 : s3.regValue .r15 = s0.regValue .r15 :=
    (g3.read (n := 64) (r := 15) (by simp)).trans r15_2
  obtain ⟨s4, a4, ready4, e4⟩ := (CrossPageStore.mov_m32_r32_legacy_effect_step_any 0x10e56f 1 (.sib 4 none 0 (.d32 159)) (by decide) rfl rfl).advances
    (readyToStep fr3.machine fr3.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr3.loaded) 0xe56f _
      (by decide) (by decide +kernel))
    (show _ from ⟨e3.rip, stack_writable pre fr3 (offset := 159) (by decide) (by decide), stack_code pre fr3 (offset := 159) (codeOffset := 0xe56f) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe576 (by decide)))
  have g4 : AgreesExcept [.mem (stackPtr s3 + 159) 4, .rip] s3 s4 := by
    have h := e4.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr4 := frame_store pre fr3 ready4 g4 (by decide)
  have value4 : memLoad s4.external (stackPtr s3 + 159) 32 =
      memLoad s1.external (stackPtr s1 + 3) 32 := by
    have h : memLoad s4.external (stackPtr s3 + 159) 32 =
      (s3.regValue .rcx).setWidth 32 := e4.writes
    have reg : s3.regValue .rcx =
      (memLoad s1.external (stackPtr s1 + 3) 32).setWidth 64 := (g3.read (n := 64) (r := 1) (by simp)).trans v2
    rw [h, reg]
    simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  let f4 := update f3 (fun i ↦ f (3+i)) 159 4
  have w4 : Window s4 f4 := window_store w3 w1
    (by decide) (by decide) g4 value4
  have r12_4 : s4.regValue .r12 = s0.regValue .r12 :=
    (g4.read (n := 64) (r := 12) (by simp)).trans r12_3
  have r15_4 : s4.regValue .r15 = s0.regValue .r15 :=
    (g4.read (n := 64) (r := 15) (by simp)).trans r15_3
  obtain ⟨s5, a5, ready5, e5⟩ := (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10e576 0 (.sib 4 none 0 (.d8 7)) (by decide) rfl rfl).advances
    (readyToStep fr4.machine fr4.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr4.loaded) 0xe576 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e4.rip, stack_readable pre fr4 (offset := 7) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe57a (by decide)))
  have g5 : AgreesExcept [.reg 0, .rip] s4 s5 := e5.agrees
  have fr5 := fr4.after_registers pre ready5 g5
    (by simp [Component.Covers]) (by simp)
  have w5 := window_registers w4 g5 (by simp) (by simp [Component.Covers])
  have v5 : s5.regValue .rax =
      (memLoad s4.external (stackPtr s4 + 7) 32).setWidth 64 := e5.writes
  have r12_5 : s5.regValue .r12 = s0.regValue .r12 :=
    (g5.read (n := 64) (r := 12) (by simp)).trans r12_4
  have r15_5 : s5.regValue .r15 = s0.regValue .r15 :=
    (g5.read (n := 64) (r := 15) (by simp)).trans r15_4
  obtain ⟨s6, a6, ready6, e6⟩ := (mov_r64_m64_effect_step 0x10e57a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances
    (readyToStep fr5.machine fr5.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr5.loaded) 0xe57a _
      (by decide) (by decide +kernel))
    (show _ from ⟨e5.rip, stack_readable pre fr5 (offset := 11) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe57f (by decide)))
  have g6 : AgreesExcept [.reg 1, .rip] s5 s6 := e6.agrees
  have fr6 := fr5.after_registers pre ready6 g6
    (by simp [Component.Covers]) (by simp)
  have w6 := window_registers w5 g6 (by simp) (by simp [Component.Covers])
  have v6 : s6.regValue .rcx =
      (memLoad s5.external (stackPtr s5 + 11) 64) := e6.writes
  have r12_6 : s6.regValue .r12 = s0.regValue .r12 :=
    (g6.read (n := 64) (r := 12) (by simp)).trans r12_5
  have r15_6 : s6.regValue .r15 = s0.regValue .r15 :=
    (g6.read (n := 64) (r := 15) (by simp)).trans r15_5
  obtain ⟨s7, a7, ready7, e7⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e57f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances
    (readyToStep fr6.machine fr6.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr6.loaded) 0xe57f _
      (by decide) (by decide +kernel))
    (show _ from ⟨e6.rip, stack_writable pre fr6 (offset := 80) (by decide) (by decide), stack_code pre fr6 (offset := 80) (codeOffset := 0xe57f) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe584 (by decide)))
  have g7 : AgreesExcept [.mem (stackPtr s6 + 80) 8, .rip] s6 s7 := by
    have h := e7.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr7 := frame_store pre fr6 ready7 g7 (by decide)
  have value7 : memLoad s7.external (stackPtr s6 + 80) 64 =
      memLoad s5.external (stackPtr s5 + 11) 64 := by
    have h : memLoad s7.external (stackPtr s6 + 80) 64 =
      (s6.regValue .rcx) := e7.writes
    have reg : s6.regValue .rcx =
      (memLoad s5.external (stackPtr s5 + 11) 64) := v6
    rw [h, reg]

  let f7 := update f4 (fun i ↦ f4 (11+i)) 80 8
  have w7 : Window s7 f7 := window_store w6 w5
    (by decide) (by decide) g7 value7
  have r12_7 : s7.regValue .r12 = s0.regValue .r12 :=
    (g7.read (n := 64) (r := 12) (by simp)).trans r12_6
  have r15_7 : s7.regValue .r15 = s0.regValue .r15 :=
    (g7.read (n := 64) (r := 15) (by simp)).trans r15_6
  obtain ⟨s8, a8, ready8, e8⟩ := (mov_r64_m64_effect_step 0x10e584 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 19)) (by decide) rfl rfl).advances
    (readyToStep fr7.machine fr7.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr7.loaded) 0xe584 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e7.rip, stack_readable pre fr7 (offset := 19) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe589 (by decide)))
  have g8 : AgreesExcept [.reg 1, .rip] s7 s8 := e8.agrees
  have fr8 := fr7.after_registers pre ready8 g8
    (by simp [Component.Covers]) (by simp)
  have w8 := window_registers w7 g8 (by simp) (by simp [Component.Covers])
  have v8 : s8.regValue .rcx =
      (memLoad s7.external (stackPtr s7 + 19) 64) := e8.writes
  have r12_8 : s8.regValue .r12 = s0.regValue .r12 :=
    (g8.read (n := 64) (r := 12) (by simp)).trans r12_7
  have r15_8 : s8.regValue .r15 = s0.regValue .r15 :=
    (g8.read (n := 64) (r := 15) (by simp)).trans r15_7
  obtain ⟨s9, a9, ready9, e9⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e589 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl).advances
    (readyToStep fr8.machine fr8.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr8.loaded) 0xe589 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e8.rip, stack_writable pre fr8 (offset := 88) (by decide) (by decide), stack_code pre fr8 (offset := 88) (codeOffset := 0xe589) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe58e (by decide)))
  have g9 : AgreesExcept [.mem (stackPtr s8 + 88) 8, .rip] s8 s9 := by
    have h := e9.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr9 := frame_store pre fr8 ready9 g9 (by decide)
  have value9 : memLoad s9.external (stackPtr s8 + 88) 64 =
      memLoad s7.external (stackPtr s7 + 19) 64 := by
    have h : memLoad s9.external (stackPtr s8 + 88) 64 =
      (s8.regValue .rcx) := e9.writes
    have reg : s8.regValue .rcx =
      (memLoad s7.external (stackPtr s7 + 19) 64) := v8
    rw [h, reg]

  let f9 := update f7 (fun i ↦ f7 (19+i)) 88 8
  have w9 : Window s9 f9 := window_store w8 w7
    (by decide) (by decide) g9 value9
  have r12_9 : s9.regValue .r12 = s0.regValue .r12 :=
    (g9.read (n := 64) (r := 12) (by simp)).trans r12_8
  have r15_9 : s9.regValue .r15 = s0.regValue .r15 :=
    (g9.read (n := 64) (r := 15) (by simp)).trans r15_8
  obtain ⟨s10, a10, ready10, e10⟩ := (mov_r64_m64_effect_step 0x10e58e 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 27)) (by decide) rfl rfl).advances
    (readyToStep fr9.machine fr9.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr9.loaded) 0xe58e _
      (by decide) (by decide +kernel))
    (show _ from ⟨e9.rip, stack_readable pre fr9 (offset := 27) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe593 (by decide)))
  have g10 : AgreesExcept [.reg 1, .rip] s9 s10 := e10.agrees
  have fr10 := fr9.after_registers pre ready10 g10
    (by simp [Component.Covers]) (by simp)
  have w10 := window_registers w9 g10 (by simp) (by simp [Component.Covers])
  have v10 : s10.regValue .rcx =
      (memLoad s9.external (stackPtr s9 + 27) 64) := e10.writes
  have r12_10 : s10.regValue .r12 = s0.regValue .r12 :=
    (g10.read (n := 64) (r := 12) (by simp)).trans r12_9
  have r15_10 : s10.regValue .r15 = s0.regValue .r15 :=
    (g10.read (n := 64) (r := 15) (by simp)).trans r15_9
  obtain ⟨s11, a11, ready11, e11⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e593 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl).advances
    (readyToStep fr10.machine fr10.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr10.loaded) 0xe593 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e10.rip, stack_writable pre fr10 (offset := 96) (by decide) (by decide), stack_code pre fr10 (offset := 96) (codeOffset := 0xe593) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe598 (by decide)))
  have g11 : AgreesExcept [.mem (stackPtr s10 + 96) 8, .rip] s10 s11 := by
    have h := e11.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr11 := frame_store pre fr10 ready11 g11 (by decide)
  have value11 : memLoad s11.external (stackPtr s10 + 96) 64 =
      memLoad s9.external (stackPtr s9 + 27) 64 := by
    have h : memLoad s11.external (stackPtr s10 + 96) 64 =
      (s10.regValue .rcx) := e11.writes
    have reg : s10.regValue .rcx =
      (memLoad s9.external (stackPtr s9 + 27) 64) := v10
    rw [h, reg]

  let f11 := update f9 (fun i ↦ f9 (27+i)) 96 8
  have w11 : Window s11 f11 := window_store w10 w9
    (by decide) (by decide) g11 value11
  have r12_11 : s11.regValue .r12 = s0.regValue .r12 :=
    (g11.read (n := 64) (r := 12) (by simp)).trans r12_10
  have r15_11 : s11.regValue .r15 = s0.regValue .r15 :=
    (g11.read (n := 64) (r := 15) (by simp)).trans r15_10
  obtain ⟨s12, a12, ready12, e12⟩ := (mov_r64_m64_effect_step 0x10e598 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 35)) (by decide) rfl rfl).advances
    (readyToStep fr11.machine fr11.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr11.loaded) 0xe598 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e11.rip, stack_readable pre fr11 (offset := 35) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe59d (by decide)))
  have g12 : AgreesExcept [.reg 1, .rip] s11 s12 := e12.agrees
  have fr12 := fr11.after_registers pre ready12 g12
    (by simp [Component.Covers]) (by simp)
  have w12 := window_registers w11 g12 (by simp) (by simp [Component.Covers])
  have v12 : s12.regValue .rcx =
      (memLoad s11.external (stackPtr s11 + 35) 64) := e12.writes
  have r12_12 : s12.regValue .r12 = s0.regValue .r12 :=
    (g12.read (n := 64) (r := 12) (by simp)).trans r12_11
  have r15_12 : s12.regValue .r15 = s0.regValue .r15 :=
    (g12.read (n := 64) (r := 15) (by simp)).trans r15_11
  obtain ⟨s13, a13, ready13, e13⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e59d 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl).advances
    (readyToStep fr12.machine fr12.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr12.loaded) 0xe59d _
      (by decide) (by decide +kernel))
    (show _ from ⟨e12.rip, stack_writable pre fr12 (offset := 104) (by decide) (by decide), stack_code pre fr12 (offset := 104) (codeOffset := 0xe59d) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5a2 (by decide)))
  have g13 : AgreesExcept [.mem (stackPtr s12 + 104) 8, .rip] s12 s13 := by
    have h := e13.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr13 := frame_store pre fr12 ready13 g13 (by decide)
  have value13 : memLoad s13.external (stackPtr s12 + 104) 64 =
      memLoad s11.external (stackPtr s11 + 35) 64 := by
    have h : memLoad s13.external (stackPtr s12 + 104) 64 =
      (s12.regValue .rcx) := e13.writes
    have reg : s12.regValue .rcx =
      (memLoad s11.external (stackPtr s11 + 35) 64) := v12
    rw [h, reg]

  let f13 := update f11 (fun i ↦ f11 (35+i)) 104 8
  have w13 : Window s13 f13 := window_store w12 w11
    (by decide) (by decide) g13 value13
  have r12_13 : s13.regValue .r12 = s0.regValue .r12 :=
    (g13.read (n := 64) (r := 12) (by simp)).trans r12_12
  have r15_13 : s13.regValue .r15 = s0.regValue .r15 :=
    (g13.read (n := 64) (r := 15) (by simp)).trans r15_12
  obtain ⟨s14, a14, ready14, e14⟩ := (mov_r64_m64_effect_step 0x10e5a2 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 43)) (by decide) rfl rfl).advances
    (readyToStep fr13.machine fr13.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr13.loaded) 0xe5a2 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e13.rip, stack_readable pre fr13 (offset := 43) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5a7 (by decide)))
  have g14 : AgreesExcept [.reg 1, .rip] s13 s14 := e14.agrees
  have fr14 := fr13.after_registers pre ready14 g14
    (by simp [Component.Covers]) (by simp)
  have w14 := window_registers w13 g14 (by simp) (by simp [Component.Covers])
  have v14 : s14.regValue .rcx =
      (memLoad s13.external (stackPtr s13 + 43) 64) := e14.writes
  have r12_14 : s14.regValue .r12 = s0.regValue .r12 :=
    (g14.read (n := 64) (r := 12) (by simp)).trans r12_13
  have r15_14 : s14.regValue .r15 = s0.regValue .r15 :=
    (g14.read (n := 64) (r := 15) (by simp)).trans r15_13
  obtain ⟨s15, a15, ready15, e15⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e5a7 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl).advances
    (readyToStep fr14.machine fr14.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr14.loaded) 0xe5a7 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e14.rip, stack_writable pre fr14 (offset := 112) (by decide) (by decide), stack_code pre fr14 (offset := 112) (codeOffset := 0xe5a7) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5ac (by decide)))
  have g15 : AgreesExcept [.mem (stackPtr s14 + 112) 8, .rip] s14 s15 := by
    have h := e15.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr15 := frame_store pre fr14 ready15 g15 (by decide)
  have value15 : memLoad s15.external (stackPtr s14 + 112) 64 =
      memLoad s13.external (stackPtr s13 + 43) 64 := by
    have h : memLoad s15.external (stackPtr s14 + 112) 64 =
      (s14.regValue .rcx) := e15.writes
    have reg : s14.regValue .rcx =
      (memLoad s13.external (stackPtr s13 + 43) 64) := v14
    rw [h, reg]

  let f15 := update f13 (fun i ↦ f13 (43+i)) 112 8
  have w15 : Window s15 f15 := window_store w14 w13
    (by decide) (by decide) g15 value15
  have r12_15 : s15.regValue .r12 = s0.regValue .r12 :=
    (g15.read (n := 64) (r := 12) (by simp)).trans r12_14
  have r15_15 : s15.regValue .r15 = s0.regValue .r15 :=
    (g15.read (n := 64) (r := 15) (by simp)).trans r15_14
  obtain ⟨s16, a16, ready16, e16⟩ := (mov_r64_m64_effect_step 0x10e5ac 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 51)) (by decide) rfl rfl).advances
    (readyToStep fr15.machine fr15.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr15.loaded) 0xe5ac _
      (by decide) (by decide +kernel))
    (show _ from ⟨e15.rip, stack_readable pre fr15 (offset := 51) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5b1 (by decide)))
  have g16 : AgreesExcept [.reg 1, .rip] s15 s16 := e16.agrees
  have fr16 := fr15.after_registers pre ready16 g16
    (by simp [Component.Covers]) (by simp)
  have w16 := window_registers w15 g16 (by simp) (by simp [Component.Covers])
  have v16 : s16.regValue .rcx =
      (memLoad s15.external (stackPtr s15 + 51) 64) := e16.writes
  have r12_16 : s16.regValue .r12 = s0.regValue .r12 :=
    (g16.read (n := 64) (r := 12) (by simp)).trans r12_15
  have r15_16 : s16.regValue .r15 = s0.regValue .r15 :=
    (g16.read (n := 64) (r := 15) (by simp)).trans r15_15
  obtain ⟨s17, a17, ready17, e17⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e5b1 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl).advances
    (readyToStep fr16.machine fr16.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr16.loaded) 0xe5b1 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e16.rip, stack_writable pre fr16 (offset := 120) (by decide) (by decide), stack_code pre fr16 (offset := 120) (codeOffset := 0xe5b1) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5b6 (by decide)))
  have g17 : AgreesExcept [.mem (stackPtr s16 + 120) 8, .rip] s16 s17 := by
    have h := e17.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr17 := frame_store pre fr16 ready17 g17 (by decide)
  have value17 : memLoad s17.external (stackPtr s16 + 120) 64 =
      memLoad s15.external (stackPtr s15 + 51) 64 := by
    have h : memLoad s17.external (stackPtr s16 + 120) 64 =
      (s16.regValue .rcx) := e17.writes
    have reg : s16.regValue .rcx =
      (memLoad s15.external (stackPtr s15 + 51) 64) := v16
    rw [h, reg]

  let f17 := update f15 (fun i ↦ f15 (51+i)) 120 8
  have w17 : Window s17 f17 := window_store w16 w15
    (by decide) (by decide) g17 value17
  have r12_17 : s17.regValue .r12 = s0.regValue .r12 :=
    (g17.read (n := 64) (r := 12) (by simp)).trans r12_16
  have r15_17 : s17.regValue .r15 = s0.regValue .r15 :=
    (g17.read (n := 64) (r := 15) (by simp)).trans r15_16
  obtain ⟨s18, a18, ready18, e18⟩ := (mov_r64_m64_effect_step 0x10e5b6 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 57)) (by decide) rfl rfl).advances
    (readyToStep fr17.machine fr17.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr17.loaded) 0xe5b6 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e17.rip, stack_readable pre fr17 (offset := 57) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5bb (by decide)))
  have g18 : AgreesExcept [.reg 1, .rip] s17 s18 := e18.agrees
  have fr18 := fr17.after_registers pre ready18 g18
    (by simp [Component.Covers]) (by simp)
  have w18 := window_registers w17 g18 (by simp) (by simp [Component.Covers])
  have v18 : s18.regValue .rcx =
      (memLoad s17.external (stackPtr s17 + 57) 64) := e18.writes
  have r12_18 : s18.regValue .r12 = s0.regValue .r12 :=
    (g18.read (n := 64) (r := 12) (by simp)).trans r12_17
  have r15_18 : s18.regValue .r15 = s0.regValue .r15 :=
    (g18.read (n := 64) (r := 15) (by simp)).trans r15_17
  obtain ⟨s19, a19, ready19, e19⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e5bb 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 126)) (by decide) rfl rfl).advances
    (readyToStep fr18.machine fr18.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr18.loaded) 0xe5bb _
      (by decide) (by decide +kernel))
    (show _ from ⟨e18.rip, stack_writable pre fr18 (offset := 126) (by decide) (by decide), stack_code pre fr18 (offset := 126) (codeOffset := 0xe5bb) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5c0 (by decide)))
  have g19 : AgreesExcept [.mem (stackPtr s18 + 126) 8, .rip] s18 s19 := by
    have h := e19.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr19 := frame_store pre fr18 ready19 g19 (by decide)
  have value19 : memLoad s19.external (stackPtr s18 + 126) 64 =
      memLoad s17.external (stackPtr s17 + 57) 64 := by
    have h : memLoad s19.external (stackPtr s18 + 126) 64 =
      (s18.regValue .rcx) := e19.writes
    have reg : s18.regValue .rcx =
      (memLoad s17.external (stackPtr s17 + 57) 64) := v18
    rw [h, reg]

  let f19 := update f17 (fun i ↦ f17 (57+i)) 126 8
  have w19 : Window s19 f19 := window_store w18 w17
    (by decide) (by decide) g19 value19
  have r12_19 : s19.regValue .r12 = s0.regValue .r12 :=
    (g19.read (n := 64) (r := 12) (by simp)).trans r12_18
  have r15_19 : s19.regValue .r15 = s0.regValue .r15 :=
    (g19.read (n := 64) (r := 15) (by simp)).trans r15_18
  have ax : (s19.regValue .rax).setWidth 32 =
      memLoad s4.external (stackPtr s4 + 7) 32 := by
    have reg : s19.regValue .rax =
        (memLoad s4.external (stackPtr s4 + 7) 32).setWidth 64 :=
      ((((((((((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).trans g17).trans g18).trans g19).read (n := 64) (r := 0) (by simp)).trans v5
    rw [reg, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have same : memLoad s19.external (stackPtr s19 + 7) 32 =
      memLoad s4.external (stackPtr s4 + 7) 32 := by
    apply memLoad_congr
    intro i hi
    have h19 := w19 (7+i) (by omega)
    have h4 := w4 (7+i) (by omega)
    change (s19.external[stackPtr s19 + 7#64 + BitVec.ofNat 64 i]?).getD 0 =
      (s4.external[stackPtr s4 + 7#64 + BitVec.ofNat 64 i]?).getD 0
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [h19, h4]
    simp only [Option.getD_some]
    congr 1
    simp only [f19, f17, f15, f13, f11, f9, f7, update]
    repeat rw [ite_eq_right (by omega)]
  exact ⟨s19, 19, ((((((((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16).trans a17).trans a18).trans a19), fr19, e19.rip, w19, r12_19, r15_19, ax.trans same.symm⟩

end P256.Proofs.Sec1.Decode.Prepare.Copy
