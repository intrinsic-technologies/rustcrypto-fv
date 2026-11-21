import P256.Proofs.Nonce.Initialize.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Buffer

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def storeComponents (s : RamState) : List Component :=
  [.mem (stackPtr s + 156) 4, .mem (stackPtr s + 128) 8,
    .mem (stackPtr s + 120) 8, .mem (stackPtr s + 112) 8,
    .mem (stackPtr s + 104) 8, .rip]

theorem stores_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107916) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x107945 ∧
      AgreesExcept (storeComponents s) s t := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_m32_r32_effect_step 0x107916 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 156)) (by decide +kernel) rfl rfl).advances (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7916 _
        (by decide +kernel) (by decide +kernel))
      ⟨rip, stack_writable4 pre stage (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre stage.toFrameState
          (offset := 156) (len := 4) (codeOffset := 0x7916) (codeLen := 8)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x791e (by decide)))
  have raw1 : AgreesExcept [.mem (stackPtr s + 156) 4, .rip] s s1 := by
    simpa [movM32R32Effect_components, movM64Imm32Effect_components,
      storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_store pre stage a1 r1 raw1 (by decide)
  have sp1 : stackPtr s = stackPtr s := by rfl
  have g1 : AgreesExcept [.mem (stackPtr s + 156) 4, .rip] s s1 := by
    simpa only [sp1] using raw1
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_m64_imm32_effect_step 0x10791e 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl 0).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x791e _
        (by decide +kernel) (by decide +kernel))
      ⟨e1.rip, stack_writable8 pre f1 (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f1.toFrameState
          (offset := 128) (len := 8) (codeOffset := 0x791e) (codeLen := 12)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x792a (by decide)))
  have raw2 : AgreesExcept [.mem (stackPtr s1 + 128) 8, .rip] s1 s2 := by
    simpa [movM32R32Effect_components, movM64Imm32Effect_components,
      storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := after_store pre f1 a2 r2 raw2 (by decide)
  have sp2 : stackPtr s1 = stackPtr s := by rw [f1.rsp, stage.rsp]
  have g2 : AgreesExcept [.mem (stackPtr s + 128) 8, .rip] s1 s2 := by
    simpa only [sp2] using raw2
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_m64_imm32_effect_step 0x10792a 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl 0).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x792a _
        (by decide +kernel) (by decide +kernel))
      ⟨e2.rip, stack_writable8 pre f2 (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f2.toFrameState
          (offset := 120) (len := 8) (codeOffset := 0x792a) (codeLen := 9)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7933 (by decide)))
  have raw3 : AgreesExcept [.mem (stackPtr s2 + 120) 8, .rip] s2 s3 := by
    simpa [movM32R32Effect_components, movM64Imm32Effect_components,
      storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := after_store pre f2 a3 r3 raw3 (by decide)
  have sp3 : stackPtr s2 = stackPtr s := by rw [f2.rsp, stage.rsp]
  have g3 : AgreesExcept [.mem (stackPtr s + 120) 8, .rip] s2 s3 := by
    simpa only [sp3] using raw3
  obtain ⟨s4, a4, r4, e4⟩ :=
    (mov_m64_imm32_effect_step 0x107933 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl 0).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x7933 _
        (by decide +kernel) (by decide +kernel))
      ⟨e3.rip, stack_writable8 pre f3 (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f3.toFrameState
          (offset := 112) (len := 8) (codeOffset := 0x7933) (codeLen := 9)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x793c (by decide)))
  have raw4 : AgreesExcept [.mem (stackPtr s3 + 112) 8, .rip] s3 s4 := by
    simpa [movM32R32Effect_components, movM64Imm32Effect_components,
      storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := after_store pre f3 a4 r4 raw4 (by decide)
  have sp4 : stackPtr s3 = stackPtr s := by rw [f3.rsp, stage.rsp]
  have g4 : AgreesExcept [.mem (stackPtr s + 112) 8, .rip] s3 s4 := by
    simpa only [sp4] using raw4
  obtain ⟨s5, a5, r5, e5⟩ :=
    (mov_m64_imm32_effect_step 0x10793c 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl 0).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x793c _
        (by decide +kernel) (by decide +kernel))
      ⟨e4.rip, stack_writable8 pre f4 (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f4.toFrameState
          (offset := 104) (len := 8) (codeOffset := 0x793c) (codeLen := 9)
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7945 (by decide)))
  have raw5 : AgreesExcept [.mem (stackPtr s4 + 104) 8, .rip] s4 s5 := by
    simpa [movM32R32Effect_components, movM64Imm32Effect_components,
      storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := after_store pre f4 a5 r5 raw5 (by decide)
  have sp5 : stackPtr s4 = stackPtr s := by rw [f4.rsp, stage.rsp]
  have g5 : AgreesExcept [.mem (stackPtr s + 104) 8, .rip] s4 s5 := by
    simpa only [sp5] using raw5
  exact ⟨s5, f5, e5.rip, ((((g1.trans g2).trans g3).trans g4).trans g5).mono (by simp [storeComponents])⟩

end P256.Proofs.Nonce.Initialize.Prepare.Buffer
