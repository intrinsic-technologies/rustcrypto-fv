import P256.Proofs.Nonce.Fill.Tail.Decode.Read.State
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Read

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : ScanReady initial s orderAddress state) :
    ∃ t, Advances boundary 8 s t ∧ Prepared initial t orderAddress state := by
  let s0 := s
  have f0 := input.toContext
  have output0 := input.output
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_m32_r32_effect_step 0x1074e8 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 60)) (by decide +kernel) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x74e8 _ (by decide) (by decide +kernel)) ⟨input.rip, stack_writable4 pre f0.toFrame (offset := 60) (by decide) (by decide), Fill.stack_code pre f0.toFrame (offset := 60) (len := 4) (codeOffset := 0x74e8) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74ed (by decide)))
  have g1 : AgreesExcept [.mem (stackPtr s0 + 60) 4, .rip] s0 s1 := by
    simpa [movM32R32Effect, movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := context_after_store pre f0 r1 g1 (by decide) (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have output1 := output_after_store pre f0.toFrame g1 (by decide) output0
  have h1_r12 : s1.regValue .r12 = frameBase initial + 8 := (g1.read (n := 64) (r := 12) (by simp)).trans input.r12
  have h1_r14 : s1.regValue .r14 = 0 := (g1.read (n := 64) (r := 14) (by simp)).trans input.r14
  have h1_rsi : s1.regValue .rsi = 32 := (g1.read (n := 64) (r := 6) (by simp)).trans input.rsi
  have h1_r8 : s1.regValue .r8 = 256 := (g1.read (n := 64) (r := 8) (by simp)).trans input.r8
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_m64_imm32_effect_step 0x1074ed 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl 0).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x74ed _ (by decide) (by decide +kernel)) ⟨e1.rip, Fill.stack_writable8 pre f1.toFrame (offset := 128) (by decide) (by decide), Fill.stack_code pre f1.toFrame (offset := 128) (len := 8) (codeOffset := 0x74ed) (codeLen := 12) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74f9 (by decide)))
  have g2 : AgreesExcept [.mem (stackPtr s1 + 128) 8, .rip] s1 s2 := by
    simpa [movM32R32Effect, movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := context_after_store pre f1 r2 g2 (by decide) (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have output2 := output_after_store pre f1.toFrame g2 (by decide) output1
  have h2_r12 : s2.regValue .r12 = frameBase initial + 8 := (g2.read (n := 64) (r := 12) (by simp)).trans h1_r12
  have h2_r14 : s2.regValue .r14 = 0 := (g2.read (n := 64) (r := 14) (by simp)).trans h1_r14
  have h2_rsi : s2.regValue .rsi = 32 := (g2.read (n := 64) (r := 6) (by simp)).trans h1_rsi
  have h2_r8 : s2.regValue .r8 = 256 := (g2.read (n := 64) (r := 8) (by simp)).trans h1_r8
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_m64_imm32_effect_step 0x1074f9 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl 0).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x74f9 _ (by decide) (by decide +kernel)) ⟨e2.rip, Fill.stack_writable8 pre f2.toFrame (offset := 120) (by decide) (by decide), Fill.stack_code pre f2.toFrame (offset := 120) (len := 8) (codeOffset := 0x74f9) (codeLen := 9) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7502 (by decide)))
  have g3 : AgreesExcept [.mem (stackPtr s2 + 120) 8, .rip] s2 s3 := by
    simpa [movM32R32Effect, movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := context_after_store pre f2 r3 g3 (by decide) (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have output3 := output_after_store pre f2.toFrame g3 (by decide) output2
  have h3_r12 : s3.regValue .r12 = frameBase initial + 8 := (g3.read (n := 64) (r := 12) (by simp)).trans h2_r12
  have h3_r14 : s3.regValue .r14 = 0 := (g3.read (n := 64) (r := 14) (by simp)).trans h2_r14
  have h3_rsi : s3.regValue .rsi = 32 := (g3.read (n := 64) (r := 6) (by simp)).trans h2_rsi
  have h3_r8 : s3.regValue .r8 = 256 := (g3.read (n := 64) (r := 8) (by simp)).trans h2_r8
  obtain ⟨s4, a4, r4, e4⟩ :=
    (mov_m64_imm32_effect_step 0x107502 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl 0).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x7502 _ (by decide) (by decide +kernel)) ⟨e3.rip, Fill.stack_writable8 pre f3.toFrame (offset := 112) (by decide) (by decide), Fill.stack_code pre f3.toFrame (offset := 112) (len := 8) (codeOffset := 0x7502) (codeLen := 9) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x750b (by decide)))
  have g4 : AgreesExcept [.mem (stackPtr s3 + 112) 8, .rip] s3 s4 := by
    simpa [movM32R32Effect, movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := context_after_store pre f3 r4 g4 (by decide) (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have output4 := output_after_store pre f3.toFrame g4 (by decide) output3
  have h4_r12 : s4.regValue .r12 = frameBase initial + 8 := (g4.read (n := 64) (r := 12) (by simp)).trans h3_r12
  have h4_r14 : s4.regValue .r14 = 0 := (g4.read (n := 64) (r := 14) (by simp)).trans h3_r14
  have h4_rsi : s4.regValue .rsi = 32 := (g4.read (n := 64) (r := 6) (by simp)).trans h3_rsi
  have h4_r8 : s4.regValue .r8 = 256 := (g4.read (n := 64) (r := 8) (by simp)).trans h3_r8
  obtain ⟨s5, a5, r5, e5⟩ :=
    (mov_m64_imm32_effect_step 0x10750b 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl 0).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x750b _ (by decide) (by decide +kernel)) ⟨e4.rip, Fill.stack_writable8 pre f4.toFrame (offset := 104) (by decide) (by decide), Fill.stack_code pre f4.toFrame (offset := 104) (len := 8) (codeOffset := 0x750b) (codeLen := 9) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7514 (by decide)))
  have g5 : AgreesExcept [.mem (stackPtr s4 + 104) 8, .rip] s4 s5 := by
    simpa [movM32R32Effect, movM64Imm32Effect, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := context_after_store pre f4 r5 g5 (by decide) (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have output5 := output_after_store pre f4.toFrame g5 (by decide) output4
  have h5_r12 : s5.regValue .r12 = frameBase initial + 8 := (g5.read (n := 64) (r := 12) (by simp)).trans h4_r12
  have h5_r14 : s5.regValue .r14 = 0 := (g5.read (n := 64) (r := 14) (by simp)).trans h4_r14
  have h5_rsi : s5.regValue .rsi = 32 := (g5.read (n := 64) (r := 6) (by simp)).trans h4_rsi
  have h5_r8 : s5.regValue .r8 = 256 := (g5.read (n := 64) (r := 8) (by simp)).trans h4_r8
  obtain ⟨s6, a6, r6, e6⟩ :=
    (mov_r32_imm32_effect_step 0x107514 0xb9 (by decide) 4).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x7514 _ (by decide) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7519 (by decide)))
  have g6 : AgreesExcept [.reg 1, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers r6 g6 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have output6 : (registerRegion initial .rsi 32).HasBytes s6.external (updateValue state).value := by
    simpa only [g6.external (by simp [Component.Covers])] using output5
  have h6_r12 : s6.regValue .r12 = frameBase initial + 8 := (g6.read (n := 64) (r := 12) (by simp)).trans h5_r12
  have h6_r14 : s6.regValue .r14 = 0 := (g6.read (n := 64) (r := 14) (by simp)).trans h5_r14
  have h6_rsi : s6.regValue .rsi = 32 := (g6.read (n := 64) (r := 6) (by simp)).trans h5_rsi
  have h6_r8 : s6.regValue .r8 = 256 := (g6.read (n := 64) (r := 8) (by simp)).trans h5_r8
  have count6 : s6.regValue .rcx = 4 := e6.writes
  obtain ⟨s7, a7, r7, e7⟩ :=
    (mov_r64_m64_effect_step 0x107519 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x7519 _ (by decide) (by decide +kernel)) ⟨e6.rip, Fill.stack_readable pre f6.toFrame (offset := 40) (len := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x751e (by decide)))
  have g7 : AgreesExcept [.reg 7, .rip] s6 s7 := e7.agrees
  have f7 := f6.after_registers r7 g7 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have output7 : (registerRegion initial .rsi 32).HasBytes s7.external (updateValue state).value := by
    simpa only [g7.external (by simp [Component.Covers])] using output6
  have h7_r12 : s7.regValue .r12 = frameBase initial + 8 := (g7.read (n := 64) (r := 12) (by simp)).trans h6_r12
  have h7_r14 : s7.regValue .r14 = 0 := (g7.read (n := 64) (r := 14) (by simp)).trans h6_r14
  have h7_rsi : s7.regValue .rsi = 32 := (g7.read (n := 64) (r := 6) (by simp)).trans h6_rsi
  have h7_r8 : s7.regValue .r8 = 256 := (g7.read (n := 64) (r := 8) (by simp)).trans h6_r8
  have source7 : s7.regValue .rdi = initial.regValue .rsi := by
    have h : s7.regValue .rdi = memLoad s6.external (stackPtr s6 + 40) 64 := e7.writes
    rw [f6.rsp, f6.outputSlot] at h
    exact h
  obtain ⟨s8, a8, r8, e8⟩ :=
    (lea_r64_effect_step 0x10751e 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x751e _ (by decide) (by decide +kernel)) e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7523 (by decide)))
  have g8 : AgreesExcept [.reg 2, .rip] s7 s8 := e8.agrees
  have f8 := f7.after_registers r8 g8 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have output8 : (registerRegion initial .rsi 32).HasBytes s8.external (updateValue state).value := by
    simpa only [g8.external (by simp [Component.Covers])] using output7
  have h8_r12 : s8.regValue .r12 = frameBase initial + 8 := (g8.read (n := 64) (r := 12) (by simp)).trans h7_r12
  have h8_r14 : s8.regValue .r14 = 0 := (g8.read (n := 64) (r := 14) (by simp)).trans h7_r14
  have h8_rsi : s8.regValue .rsi = 32 := (g8.read (n := 64) (r := 6) (by simp)).trans h7_rsi
  have h8_r8 : s8.regValue .r8 = 256 := (g8.read (n := 64) (r := 8) (by simp)).trans h7_r8
  have destination : s8.regValue .rdx = frameBase initial + 104 := by
    have h : s8.regValue .rdx = stackPtr s7 + 104 := e8.writes
    rw [f7.rsp] at h
    exact h
  exact ⟨s8, ((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8,
    f8, e8.rip, h8_r12, h8_r14, h8_rsi,
    ((g7.trans g8).read (n := 64) (r := 1) (by simp)).trans count6, h8_r8,
    (g8.read (n := 64) (r := 7) (by simp)).trans source7, destination, output8⟩

end P256.Proofs.Nonce.Fill.Tail.Decode.Read
