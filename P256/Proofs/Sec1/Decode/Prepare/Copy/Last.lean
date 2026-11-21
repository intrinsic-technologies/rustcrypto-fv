import P256.Proofs.Sec1.Decode.Prepare.Copy.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare.Copy

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def copyLastWindow {α : Type} (f : Nat → α) : Nat → α :=
  let f3 := update f (fun i ↦ f (80+i)) 167 8
  let f4 := update f3 (fun i ↦ f (88+i)) 175 8
  let f6 := update f4 (fun i ↦ f4 (96+i)) 183 8
  let f8 := update f6 (fun i ↦ f6 (104+i)) 191 8
  let f10 := update f8 (fun i ↦ f8 (112+i)) 199 8
  let f12 := update f10 (fun i ↦ f10 (120+i)) 207 8
  let f14 := update f12 (fun i ↦ f12 (126+i)) 213 8
  update f14 (fun i ↦ f (7+i)) 163 4

set_option maxHeartbeats 1600000 in
theorem runLast [Bindings] {initial s0 : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {f : Nat → UInt8} (pre : DecodePre initial boundary bytes)
    (fr0 : Frame initial s0) (w0 : Window s0 f) (rip : s0.RIP = 0x10e5c0)
    (ax : (s0.regValue .rax).setWidth 32 = memLoad s0.external (stackPtr s0 + 7) 32) :
    ∃ t fuel, Advances boundary fuel s0 t ∧ Frame initial t ∧ t.RIP = 0x10e622 ∧
      Window t (copyLastWindow f) ∧ t.regValue .r12 = s0.regValue .r12 ∧
      t.regValue .r15 = s0.regValue .r15 := by
  obtain ⟨s1, a1, ready1, e1⟩ := (mov_r64_m64_effect_step 0x10e5c0 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl).advances
    (readyToStep fr0.machine fr0.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr0.loaded) 0xe5c0 _
      (by decide) (by decide +kernel))
    (show _ from ⟨rip, stack_readable pre fr0 (offset := 80) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5c5 (by decide)))
  have g1 : AgreesExcept [.reg 1, .rip] s0 s1 := e1.agrees
  have fr1 := fr0.after_registers pre ready1 g1
    (by simp [Component.Covers]) (by simp)
  have w1 := window_registers w0 g1 (by simp) (by simp [Component.Covers])
  have v1 : s1.regValue .rcx =
      (memLoad s0.external (stackPtr s0 + 80) 64) := e1.writes
  have r12_1 : s1.regValue .r12 = s0.regValue .r12 :=
    (g1.read (n := 64) (r := 12) (by simp)).trans rfl
  have r15_1 : s1.regValue .r15 = s0.regValue .r15 :=
    (g1.read (n := 64) (r := 15) (by simp)).trans rfl
  obtain ⟨s2, a2, ready2, e2⟩ := (mov_r64_m64_effect_step 0x10e5c5 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl).advances
    (readyToStep fr1.machine fr1.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr1.loaded) 0xe5c5 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e1.rip, stack_readable pre fr1 (offset := 88) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5ca (by decide)))
  have g2 : AgreesExcept [.reg 2, .rip] s1 s2 := e2.agrees
  have fr2 := fr1.after_registers pre ready2 g2
    (by simp [Component.Covers]) (by simp)
  have w2 := window_registers w1 g2 (by simp) (by simp [Component.Covers])
  have v2 : s2.regValue .rdx =
      (memLoad s1.external (stackPtr s1 + 88) 64) := e2.writes
  have r12_2 : s2.regValue .r12 = s0.regValue .r12 :=
    (g2.read (n := 64) (r := 12) (by simp)).trans r12_1
  have r15_2 : s2.regValue .r15 = s0.regValue .r15 :=
    (g2.read (n := 64) (r := 15) (by simp)).trans r15_1
  obtain ⟨s3, a3, ready3, e3⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e5ca 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 167)) (by decide) rfl rfl).advances
    (readyToStep fr2.machine fr2.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr2.loaded) 0xe5ca _
      (by decide) (by decide +kernel))
    (show _ from ⟨e2.rip, stack_writable pre fr2 (offset := 167) (by decide) (by decide), stack_code pre fr2 (offset := 167) (codeOffset := 0xe5ca) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5d2 (by decide)))
  have g3 : AgreesExcept [.mem (stackPtr s2 + 167) 8, .rip] s2 s3 := by
    have h := e3.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr3 := frame_store pre fr2 ready3 g3 (by decide)
  have value3 : memLoad s3.external (stackPtr s2 + 167) 64 =
      memLoad s0.external (stackPtr s0 + 80) 64 := by
    have h : memLoad s3.external (stackPtr s2 + 167) 64 =
      (s2.regValue .rcx) := e3.writes
    have reg : s2.regValue .rcx =
      (memLoad s0.external (stackPtr s0 + 80) 64) := (g2.read (n := 64) (r := 1) (by simp)).trans v1
    rw [h, reg]

  let f3 := update f (fun i ↦ f (80+i)) 167 8
  have w3 : Window s3 f3 := window_store w2 w0
    (by decide) (by decide) g3 value3
  have r12_3 : s3.regValue .r12 = s0.regValue .r12 :=
    (g3.read (n := 64) (r := 12) (by simp)).trans r12_2
  have r15_3 : s3.regValue .r15 = s0.regValue .r15 :=
    (g3.read (n := 64) (r := 15) (by simp)).trans r15_2
  obtain ⟨s4, a4, ready4, e4⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e5d2 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 175)) (by decide) rfl rfl).advances
    (readyToStep fr3.machine fr3.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr3.loaded) 0xe5d2 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e3.rip, stack_writable pre fr3 (offset := 175) (by decide) (by decide), stack_code pre fr3 (offset := 175) (codeOffset := 0xe5d2) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5da (by decide)))
  have g4 : AgreesExcept [.mem (stackPtr s3 + 175) 8, .rip] s3 s4 := by
    have h := e4.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr4 := frame_store pre fr3 ready4 g4 (by decide)
  have value4 : memLoad s4.external (stackPtr s3 + 175) 64 =
      memLoad s1.external (stackPtr s1 + 88) 64 := by
    have h : memLoad s4.external (stackPtr s3 + 175) 64 =
      (s3.regValue .rdx) := e4.writes
    have reg : s3.regValue .rdx =
      (memLoad s1.external (stackPtr s1 + 88) 64) := (g3.read (n := 64) (r := 2) (by simp)).trans v2
    rw [h, reg]

  let f4 := update f3 (fun i ↦ f (88+i)) 175 8
  have w4 : Window s4 f4 := window_store w3 w1
    (by decide) (by decide) g4 value4
  have r12_4 : s4.regValue .r12 = s0.regValue .r12 :=
    (g4.read (n := 64) (r := 12) (by simp)).trans r12_3
  have r15_4 : s4.regValue .r15 = s0.regValue .r15 :=
    (g4.read (n := 64) (r := 15) (by simp)).trans r15_3
  obtain ⟨s5, a5, ready5, e5⟩ := (mov_r64_m64_effect_step 0x10e5da 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl).advances
    (readyToStep fr4.machine fr4.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr4.loaded) 0xe5da _
      (by decide) (by decide +kernel))
    (show _ from ⟨e4.rip, stack_readable pre fr4 (offset := 96) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5df (by decide)))
  have g5 : AgreesExcept [.reg 1, .rip] s4 s5 := e5.agrees
  have fr5 := fr4.after_registers pre ready5 g5
    (by simp [Component.Covers]) (by simp)
  have w5 := window_registers w4 g5 (by simp) (by simp [Component.Covers])
  have v5 : s5.regValue .rcx =
      (memLoad s4.external (stackPtr s4 + 96) 64) := e5.writes
  have r12_5 : s5.regValue .r12 = s0.regValue .r12 :=
    (g5.read (n := 64) (r := 12) (by simp)).trans r12_4
  have r15_5 : s5.regValue .r15 = s0.regValue .r15 :=
    (g5.read (n := 64) (r := 15) (by simp)).trans r15_4
  obtain ⟨s6, a6, ready6, e6⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e5df 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 183)) (by decide) rfl rfl).advances
    (readyToStep fr5.machine fr5.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr5.loaded) 0xe5df _
      (by decide) (by decide +kernel))
    (show _ from ⟨e5.rip, stack_writable pre fr5 (offset := 183) (by decide) (by decide), stack_code pre fr5 (offset := 183) (codeOffset := 0xe5df) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5e7 (by decide)))
  have g6 : AgreesExcept [.mem (stackPtr s5 + 183) 8, .rip] s5 s6 := by
    have h := e6.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr6 := frame_store pre fr5 ready6 g6 (by decide)
  have value6 : memLoad s6.external (stackPtr s5 + 183) 64 =
      memLoad s4.external (stackPtr s4 + 96) 64 := by
    have h : memLoad s6.external (stackPtr s5 + 183) 64 =
      (s5.regValue .rcx) := e6.writes
    have reg : s5.regValue .rcx =
      (memLoad s4.external (stackPtr s4 + 96) 64) := v5
    rw [h, reg]

  let f6 := update f4 (fun i ↦ f4 (96+i)) 183 8
  have w6 : Window s6 f6 := window_store w5 w4
    (by decide) (by decide) g6 value6
  have r12_6 : s6.regValue .r12 = s0.regValue .r12 :=
    (g6.read (n := 64) (r := 12) (by simp)).trans r12_5
  have r15_6 : s6.regValue .r15 = s0.regValue .r15 :=
    (g6.read (n := 64) (r := 15) (by simp)).trans r15_5
  obtain ⟨s7, a7, ready7, e7⟩ := (mov_r64_m64_effect_step 0x10e5e7 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl).advances
    (readyToStep fr6.machine fr6.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr6.loaded) 0xe5e7 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e6.rip, stack_readable pre fr6 (offset := 104) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5ec (by decide)))
  have g7 : AgreesExcept [.reg 1, .rip] s6 s7 := e7.agrees
  have fr7 := fr6.after_registers pre ready7 g7
    (by simp [Component.Covers]) (by simp)
  have w7 := window_registers w6 g7 (by simp) (by simp [Component.Covers])
  have v7 : s7.regValue .rcx =
      (memLoad s6.external (stackPtr s6 + 104) 64) := e7.writes
  have r12_7 : s7.regValue .r12 = s0.regValue .r12 :=
    (g7.read (n := 64) (r := 12) (by simp)).trans r12_6
  have r15_7 : s7.regValue .r15 = s0.regValue .r15 :=
    (g7.read (n := 64) (r := 15) (by simp)).trans r15_6
  obtain ⟨s8, a8, ready8, e8⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e5ec 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 191)) (by decide) rfl rfl).advances
    (readyToStep fr7.machine fr7.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr7.loaded) 0xe5ec _
      (by decide) (by decide +kernel))
    (show _ from ⟨e7.rip, stack_writable pre fr7 (offset := 191) (by decide) (by decide), stack_code pre fr7 (offset := 191) (codeOffset := 0xe5ec) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5f4 (by decide)))
  have g8 : AgreesExcept [.mem (stackPtr s7 + 191) 8, .rip] s7 s8 := by
    have h := e8.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr8 := frame_store pre fr7 ready8 g8 (by decide)
  have value8 : memLoad s8.external (stackPtr s7 + 191) 64 =
      memLoad s6.external (stackPtr s6 + 104) 64 := by
    have h : memLoad s8.external (stackPtr s7 + 191) 64 =
      (s7.regValue .rcx) := e8.writes
    have reg : s7.regValue .rcx =
      (memLoad s6.external (stackPtr s6 + 104) 64) := v7
    rw [h, reg]

  let f8 := update f6 (fun i ↦ f6 (104+i)) 191 8
  have w8 : Window s8 f8 := window_store w7 w6
    (by decide) (by decide) g8 value8
  have r12_8 : s8.regValue .r12 = s0.regValue .r12 :=
    (g8.read (n := 64) (r := 12) (by simp)).trans r12_7
  have r15_8 : s8.regValue .r15 = s0.regValue .r15 :=
    (g8.read (n := 64) (r := 15) (by simp)).trans r15_7
  obtain ⟨s9, a9, ready9, e9⟩ := (mov_r64_m64_effect_step 0x10e5f4 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl).advances
    (readyToStep fr8.machine fr8.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr8.loaded) 0xe5f4 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e8.rip, stack_readable pre fr8 (offset := 112) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe5f9 (by decide)))
  have g9 : AgreesExcept [.reg 1, .rip] s8 s9 := e9.agrees
  have fr9 := fr8.after_registers pre ready9 g9
    (by simp [Component.Covers]) (by simp)
  have w9 := window_registers w8 g9 (by simp) (by simp [Component.Covers])
  have v9 : s9.regValue .rcx =
      (memLoad s8.external (stackPtr s8 + 112) 64) := e9.writes
  have r12_9 : s9.regValue .r12 = s0.regValue .r12 :=
    (g9.read (n := 64) (r := 12) (by simp)).trans r12_8
  have r15_9 : s9.regValue .r15 = s0.regValue .r15 :=
    (g9.read (n := 64) (r := 15) (by simp)).trans r15_8
  obtain ⟨s10, a10, ready10, e10⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e5f9 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 199)) (by decide) rfl rfl).advances
    (readyToStep fr9.machine fr9.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr9.loaded) 0xe5f9 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e9.rip, stack_writable pre fr9 (offset := 199) (by decide) (by decide), stack_code pre fr9 (offset := 199) (codeOffset := 0xe5f9) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe601 (by decide)))
  have g10 : AgreesExcept [.mem (stackPtr s9 + 199) 8, .rip] s9 s10 := by
    have h := e10.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr10 := frame_store pre fr9 ready10 g10 (by decide)
  have value10 : memLoad s10.external (stackPtr s9 + 199) 64 =
      memLoad s8.external (stackPtr s8 + 112) 64 := by
    have h : memLoad s10.external (stackPtr s9 + 199) 64 =
      (s9.regValue .rcx) := e10.writes
    have reg : s9.regValue .rcx =
      (memLoad s8.external (stackPtr s8 + 112) 64) := v9
    rw [h, reg]

  let f10 := update f8 (fun i ↦ f8 (112+i)) 199 8
  have w10 : Window s10 f10 := window_store w9 w8
    (by decide) (by decide) g10 value10
  have r12_10 : s10.regValue .r12 = s0.regValue .r12 :=
    (g10.read (n := 64) (r := 12) (by simp)).trans r12_9
  have r15_10 : s10.regValue .r15 = s0.regValue .r15 :=
    (g10.read (n := 64) (r := 15) (by simp)).trans r15_9
  obtain ⟨s11, a11, ready11, e11⟩ := (mov_r64_m64_effect_step 0x10e601 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl).advances
    (readyToStep fr10.machine fr10.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr10.loaded) 0xe601 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e10.rip, stack_readable pre fr10 (offset := 120) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe606 (by decide)))
  have g11 : AgreesExcept [.reg 1, .rip] s10 s11 := e11.agrees
  have fr11 := fr10.after_registers pre ready11 g11
    (by simp [Component.Covers]) (by simp)
  have w11 := window_registers w10 g11 (by simp) (by simp [Component.Covers])
  have v11 : s11.regValue .rcx =
      (memLoad s10.external (stackPtr s10 + 120) 64) := e11.writes
  have r12_11 : s11.regValue .r12 = s0.regValue .r12 :=
    (g11.read (n := 64) (r := 12) (by simp)).trans r12_10
  have r15_11 : s11.regValue .r15 = s0.regValue .r15 :=
    (g11.read (n := 64) (r := 15) (by simp)).trans r15_10
  obtain ⟨s12, a12, ready12, e12⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e606 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 207)) (by decide) rfl rfl).advances
    (readyToStep fr11.machine fr11.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr11.loaded) 0xe606 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e11.rip, stack_writable pre fr11 (offset := 207) (by decide) (by decide), stack_code pre fr11 (offset := 207) (codeOffset := 0xe606) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe60e (by decide)))
  have g12 : AgreesExcept [.mem (stackPtr s11 + 207) 8, .rip] s11 s12 := by
    have h := e12.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr12 := frame_store pre fr11 ready12 g12 (by decide)
  have value12 : memLoad s12.external (stackPtr s11 + 207) 64 =
      memLoad s10.external (stackPtr s10 + 120) 64 := by
    have h : memLoad s12.external (stackPtr s11 + 207) 64 =
      (s11.regValue .rcx) := e12.writes
    have reg : s11.regValue .rcx =
      (memLoad s10.external (stackPtr s10 + 120) 64) := v11
    rw [h, reg]

  let f12 := update f10 (fun i ↦ f10 (120+i)) 207 8
  have w12 : Window s12 f12 := window_store w11 w10
    (by decide) (by decide) g12 value12
  have r12_12 : s12.regValue .r12 = s0.regValue .r12 :=
    (g12.read (n := 64) (r := 12) (by simp)).trans r12_11
  have r15_12 : s12.regValue .r15 = s0.regValue .r15 :=
    (g12.read (n := 64) (r := 15) (by simp)).trans r15_11
  obtain ⟨s13, a13, ready13, e13⟩ := (mov_r64_m64_effect_step 0x10e60e 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 126)) (by decide) rfl rfl).advances
    (readyToStep fr12.machine fr12.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr12.loaded) 0xe60e _
      (by decide) (by decide +kernel))
    (show _ from ⟨e12.rip, stack_readable pre fr12 (offset := 126) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe613 (by decide)))
  have g13 : AgreesExcept [.reg 1, .rip] s12 s13 := e13.agrees
  have fr13 := fr12.after_registers pre ready13 g13
    (by simp [Component.Covers]) (by simp)
  have w13 := window_registers w12 g13 (by simp) (by simp [Component.Covers])
  have v13 : s13.regValue .rcx =
      (memLoad s12.external (stackPtr s12 + 126) 64) := e13.writes
  have r12_13 : s13.regValue .r12 = s0.regValue .r12 :=
    (g13.read (n := 64) (r := 12) (by simp)).trans r12_12
  have r15_13 : s13.regValue .r15 = s0.regValue .r15 :=
    (g13.read (n := 64) (r := 15) (by simp)).trans r15_12
  obtain ⟨s14, a14, ready14, e14⟩ := (CrossPageStore.mov_m64_r64_effect_step_any 0x10e613 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 213)) (by decide) rfl rfl).advances
    (readyToStep fr13.machine fr13.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr13.loaded) 0xe613 _
      (by decide) (by decide +kernel))
    (show _ from ⟨e13.rip, stack_writable pre fr13 (offset := 213) (by decide) (by decide), stack_code pre fr13 (offset := 213) (codeOffset := 0xe613) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe61b (by decide)))
  have g14 : AgreesExcept [.mem (stackPtr s13 + 213) 8, .rip] s13 s14 := by
    have h := e14.agrees
    x86_norm [movM64R64Effect, CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr14 := frame_store pre fr13 ready14 g14 (by decide)
  have value14 : memLoad s14.external (stackPtr s13 + 213) 64 =
      memLoad s12.external (stackPtr s12 + 126) 64 := by
    have h : memLoad s14.external (stackPtr s13 + 213) 64 =
      (s13.regValue .rcx) := e14.writes
    have reg : s13.regValue .rcx =
      (memLoad s12.external (stackPtr s12 + 126) 64) := v13
    rw [h, reg]

  let f14 := update f12 (fun i ↦ f12 (126+i)) 213 8
  have w14 : Window s14 f14 := window_store w13 w12
    (by decide) (by decide) g14 value14
  have r12_14 : s14.regValue .r12 = s0.regValue .r12 :=
    (g14.read (n := 64) (r := 12) (by simp)).trans r12_13
  have r15_14 : s14.regValue .r15 = s0.regValue .r15 :=
    (g14.read (n := 64) (r := 15) (by simp)).trans r15_13
  obtain ⟨s15, a15, ready15, e15⟩ := (CrossPageStore.mov_m32_r32_legacy_effect_step_any
    0x10e61b 0 (.sib 4 none 0 (.d32 163)) (by decide) rfl rfl).advances
    (readyToStep fr14.machine fr14.bindingsSupported)
    (programText_slice (programLoaded_codeIn fr14.loaded) 0xe61b _
      (by decide) (by decide +kernel))
    (show _ from ⟨e14.rip, stack_writable pre fr14 (offset := 163) (by decide) (by decide),
      stack_code pre fr14 (offset := 163) (codeOffset := 0xe61b) (by decide) (by decide)⟩)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xe622 (by decide)))
  have g15 : AgreesExcept [.mem (stackPtr s14 + 163) 4, .rip] s14 s15 := by
    have h := e15.agrees
    x86_norm [CrossPageStore.movM32R32LegacyEffect, stackPtr] at h ⊢
    exact h
  have fr15 := frame_store pre fr14 ready15 g15 (by decide)
  have value15 : memLoad s15.external (stackPtr s14 + 163) 32 =
      memLoad s0.external (stackPtr s0 + 7) 32 := by
    have h : memLoad s15.external (stackPtr s14 + 163) 32 =
      (s14.regValue .rax).setWidth 32 := e15.writes
    have reg : s14.regValue .rax = s0.regValue .rax :=
      (((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).read (n := 64) (r := 0) (by simp)
    rw [h, reg, ax]
  have w15 : Window s15 (copyLastWindow f) := window_store w14 w0
    (by decide) (by decide) g15 value15
  exact ⟨s15, 15, ((((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15), fr15, e15.rip, w15,
    (g15.read (n := 64) (r := 12) (by simp)).trans r12_14,
    (g15.read (n := 64) (r := 15) (by simp)).trans r15_14⟩

end P256.Proofs.Sec1.Decode.Prepare.Copy
