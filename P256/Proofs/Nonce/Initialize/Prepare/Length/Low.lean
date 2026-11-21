import P256.Proofs.Nonce.Initialize.Prepare.Length.High
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Length

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Nonce.Initialize.Conversions.Bsr
open P256.Proofs.Nonce.Initialize.Conversions.XorImmediate
open P256.Proofs.Nonce.Initialize.Conversions.Neg32

theorem low_limb [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x1078b7)
    (cx : s.regValue .rcx = 0) (dx : s.regValue .rdx = 0)
    (scratch : memLoad s.external (stackPtr s + 8) 8 = 0) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x1078d2 ∧
      t.regValue .rcx = 256 ∧
      AgreesExcept [.reg 7, .reg 6, .reg 1, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (bsr_r64_r64_effect_step 0x1078b7 0x49 0xff (by simp [RexWPrefix]) rfl).advances (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x78b7 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78bb (by decide)))
  have g1 : AgreesExcept [.reg 7, .flags, .rip] s s1 := e1.agrees
  have f1 := stage.after_registers a1 r1 g1 (by simp [Component.Covers]) (by simp)
  obtain ⟨s2, a2, r2, e2⟩ :=
    (xor_r32_imm8_effect_step 0x1078bb 0xf7 63 rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x78bb _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78be (by decide)))
  have g2 : AgreesExcept [.reg 7, .flags, .rip] s1 s2 := e2.agrees
  have f2 := f1.after_registers a2 r2 g2 (by simp [Component.Covers]) (by simp)
  obtain ⟨s3, a3, r3, e3⟩ :=
    (movzx_r32_m8_effect_step 0x1078be 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x78be _ (by decide +kernel) (by decide +kernel)) ⟨e2.rip, by
        change MemReadable s2 (stackPtr s2 + 8) 1
        exact ScalarFrame.stack_readable pre.toCalleePre f2.toFrameState (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78c3 (by decide)))
  have g3 : AgreesExcept [.reg 6, .rip] s2 s3 := e3.agrees
  have f3 := f2.after_registers a3 r3 g3 (by simp [Component.Covers]) (by simp)
  have v3 : s3.regValue .rsi = 0 := by
    have h : s3.regValue .rsi = (memLoad s2.external (stackPtr s2 + 8) 8).setWidth 64 := e3.writes
    have sp : stackPtr s2 = stackPtr s := (g1.trans g2).read (n := 64) (r := 4) (by simp)
    rw [sp, (g1.trans g2).external (by simp [Component.Covers]), scratch] at h
    exact h
  have in6_4 : s3.regValue .rsi = 0 := v3
  obtain ⟨s4, a4, r4, e4⟩ :=
    (neg_r32_effect_step 0x1078c3 0xde rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x78c3 _ (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78c5 (by decide)))
  have g4 : AgreesExcept [.reg 6, .flags, .rip] s3 s4 := e4.agrees
  have f4 := f3.after_registers a4 r4 g4 (by simp [Component.Covers]) (by simp)
  have v4 : s4.regValue .rsi = 0 := by
    have h : s4.regValue .rsi = (-(s3.regValue .rsi).setWidth 32).setWidth 64 := e4.writes
    simpa [in6_4] using h
  have in6_5 : s4.regValue .rsi = 0 := v4
  obtain ⟨s5, a5, r5, e5⟩ :=
    (and_r32_r32_effect_step 0x1078c5 0xfe rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x78c5 _ (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78c7 (by decide)))
  have g5 : AgreesExcept [.reg 6, .flags, .rip] s4 s5 := e5.agrees
  have f5 := f4.after_registers a5 r5 g5 (by simp [Component.Covers]) (by simp)
  have v5 : s5.regValue .rsi = 0 := by
    have h : s5.regValue .rsi = ((s4.regValue .rsi).setWidth 32 &&& (s4.regValue .rdi).setWidth 32).setWidth 64 := e5.writes
    simpa [in6_5] using h
  have in6_6 : s5.regValue .rsi = 0 := v5
  have in2_6 : s5.regValue .rdx = 0 := (((((g1.trans g2).trans g3).trans g4).trans g5).read (n := 64) (r := 2) (by simp)).trans dx
  obtain ⟨s6, a6, r6, e6⟩ :=
    (add_r32_r32_effect_step 0x1078c7 0xd6 rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x78c7 _ (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78c9 (by decide)))
  have g6 : AgreesExcept [.reg 6, .flags, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers a6 r6 g6 (by simp [Component.Covers]) (by simp)
  have v6 : s6.regValue .rsi = 0 := by
    have h : s6.regValue .rsi = ((s5.regValue .rsi).setWidth 32 + (s5.regValue .rdx).setWidth 32).setWidth 64 := e6.writes
    simpa [in6_6, in2_6] using h
  have in6_7 : s6.regValue .rsi = 0 := v6
  have in1_7 : s6.regValue .rcx = 0 := ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 1) (by simp)).trans cx
  obtain ⟨s7, a7, r7, e7⟩ :=
    (add_r32_r32_effect_step 0x1078c9 0xce rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x78c9 _ (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78cb (by decide)))
  have g7 : AgreesExcept [.reg 6, .flags, .rip] s6 s7 := e7.agrees
  have f7 := f6.after_registers a7 r7 g7 (by simp [Component.Covers]) (by simp)
  have v7 : s7.regValue .rsi = 0 := by
    have h : s7.regValue .rsi = ((s6.regValue .rsi).setWidth 32 + (s6.regValue .rcx).setWidth 32).setWidth 64 := e7.writes
    simpa [in6_7, in1_7] using h
  obtain ⟨s8, a8, r8, e8⟩ :=
    (mov_r32_imm32_effect_step 0x1078cb 0xb9 (by decide) 256).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x78cb _ (by decide +kernel) (by decide +kernel)) e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78d0 (by decide)))
  have g8 : AgreesExcept [.reg 1, .rip] s7 s8 := e8.agrees
  have f8 := f7.after_registers a8 r8 g8 (by simp [Component.Covers]) (by simp)
  have v8 : s8.regValue .rcx = 256 := e8.writes
  have in6_9 : s8.regValue .rsi = 0 := (g8.read (n := 64) (r := 6) (by simp)).trans v7
  have in1_9 : s8.regValue .rcx = 256 := v8
  obtain ⟨s9, a9, r9, e9⟩ :=
    (sub_r32_r32_effect_step 0x1078d0 0xf1 rfl).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x78d0 _ (by decide +kernel) (by decide +kernel)) e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78d2 (by decide)))
  have g9 : AgreesExcept [.reg 1, .flags, .rip] s8 s9 := e9.agrees
  have f9 := f8.after_registers a9 r9 g9 (by simp [Component.Covers]) (by simp)
  have v9 : s9.regValue .rcx = 256 := by
    have h : s9.regValue .rcx = ((s8.regValue .rcx).setWidth 32 - (s8.regValue .rsi).setWidth 32).setWidth 64 := e9.writes
    simpa [in6_9, in1_9] using h
  exact ⟨s9, f9, e9.rip, v9, ((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).mono (by simp)⟩

end P256.Proofs.Nonce.Initialize.Prepare.Length
