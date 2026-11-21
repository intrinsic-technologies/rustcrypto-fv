import P256.Proofs.Nonce.Initialize.Prepare.Scan.Head
import P256.Proofs.Common.Instructions.Cmov32
import P256.Proofs.Common.Encoding.Parser.ByteStore

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Scan

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions

theorem tail [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x10783b)
    (bp : s.regValue .rbp = 0) (ten : s.regValue .r10 = 0) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x107858 ∧
      t.regValue .rdx = 0 ∧ t.regValue .rbp = 0 ∧
      memLoad t.external (stackPtr s + 8) 8 = 0 ∧
      AgreesExcept [.mem (stackPtr s + 8) 1, .reg 5, .reg 2, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (test_r64_r64_effect_step 0x10783b 0x4d 0xed (by simp [RexWPrefix]) rfl).advances (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x783b _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x783e (by decide)))
  have g1 : AgreesExcept [.flags, .rip] s s1 := e1.agrees
  have f1 := stage.after_registers a1 r1 g1 (by simp [Component.Covers]) (by simp)
  have sp1 : stackPtr s1 = stackPtr s := g1.read (n := 64) (r := 4) (by simp)
  have bp1 : s1.regValue .rbp = 0 := (g1.read (n := 64) (r := 5) (by simp)).trans bp
  have ten1 : s1.regValue .r10 = 0 := (g1.read (n := 64) (r := 10) (by simp)).trans ten
  obtain ⟨s2, a2, r2, e2⟩ :=
    (cmovne_r32_r32_rex_effect_step 0x10783e 0x41 0xea (by simp [RexNoWPrefix]) rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x783e _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7842 (by decide)))
  have g2 : AgreesExcept [.reg 5, .rip] s1 s2 := e2.agrees
  have f2 := f1.after_registers a2 r2 g2 (by simp [Component.Covers]) (by simp)
  have sp2 : stackPtr s2 = stackPtr s := (g1.trans g2).read (n := 64) (r := 4) (by simp)
  have bp2 : s2.regValue .rbp = 0 := by
    have h : s2.regValue .rbp = ((if condHolds 5 (StatusFlags.ofRFLAGS s1.RFLAGS) then
      (s1.regValue .r10).setWidth 32 else (s1.regValue .rbp).setWidth 32).setWidth 64) := e2.writes
    simpa [bp1, ten1] using h
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_m8_r8_effect_step 0x107842 0x40 (by simp [RexPrefix]) 5
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x7842 _
        (by decide +kernel) (by decide +kernel)) ⟨e2.rip, by
        change MemWritable s2 (stackPtr s2 + 8) 1
        exact stack_writable1 pre f2 (by decide), by
        change RangeApart (stackPtr s2 + 8) 1 0x107842 5
        exact ScalarFrame.stack_code (offset := 8) (len := 1)
          (codeOffset := 0x7842) (codeLen := 5) pre.toCalleePre f2.toFrameState
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7847 (by decide)))
  have g3 : AgreesExcept [.mem (stackPtr s2 + 8) 1, .rip] s2 s3 := by
    simpa [movM64R64Effect_components, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := after_store pre f2 a3 r3 g3 (by decide)
  have sp3 : stackPtr s3 = stackPtr s := ((g1.trans g2).trans g3).read (n := 64) (r := 4) (by simp)
  have scratch3 : memLoad s3.external (stackPtr s + 8) 8 = 0 := by
    have h : memLoad s3.external (stackPtr s2 + 8) 8 = (s2.regValue .rbp).setWidth 8 := e3.writes
    rwa [sp2, bp2] at h
  obtain ⟨s4, a4, r4, e4⟩ :=
    (movzx_r32_m8_effect_step 0x107847 2
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x7847 _
        (by decide +kernel) (by decide +kernel)) ⟨e3.rip, by
        change MemReadable s3 (stackPtr s3 + 8) 1
        exact ScalarFrame.stack_readable pre.toCalleePre f3.toFrameState
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x784c (by decide)))
  have g4 : AgreesExcept [.reg 2, .rip] s3 s4 := e4.agrees
  have f4 := f3.after_registers a4 r4 g4 (by simp [Component.Covers]) (by simp)
  have sp4 : stackPtr s4 = stackPtr s := (((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 4) (by simp)
  have dx4 : s4.regValue .rdx = 0 := by
    have h : s4.regValue .rdx = (memLoad s3.external (stackPtr s3 + 8) 8).setWidth 64 := e4.writes
    rwa [sp3, scratch3] at h
  obtain ⟨s5, a5, r5, e5⟩ :=
    (test_r64_r64_effect_step 0x10784c 0x4d 0xf6 (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x784c _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x784f (by decide)))
  have g5 : AgreesExcept [.flags, .rip] s4 s5 := e5.agrees
  have f5 := f4.after_registers a5 r5 g5 (by simp [Component.Covers]) (by simp)
  have sp5 : stackPtr s5 = stackPtr s := ((((g1.trans g2).trans g3).trans g4).trans g5).read (n := 64) (r := 4) (by simp)
  have bp5 : s5.regValue .rbp = 0 := (((g3.trans g4).trans g5).read (n := 64) (r := 5) (by simp)).trans bp2
  have ten5 : s5.regValue .r10 = 0 := (((((g1.trans g2).trans g3).trans g4).trans g5).read (n := 64) (r := 10) (by simp)).trans ten
  obtain ⟨s6, a6, r6, e6⟩ :=
    (cmovne_r32_r32_rex_effect_step 0x10784f 0x41 0xea (by simp [RexNoWPrefix]) rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x784f _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7853 (by decide)))
  have g6 : AgreesExcept [.reg 5, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers a6 r6 g6 (by simp [Component.Covers]) (by simp)
  have sp6 : stackPtr s6 = stackPtr s := (((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 4) (by simp)
  have bp6 : s6.regValue .rbp = 0 := by
    have h : s6.regValue .rbp = ((if condHolds 5 (StatusFlags.ofRFLAGS s5.RFLAGS) then
      (s5.regValue .r10).setWidth 32 else (s5.regValue .rbp).setWidth 32).setWidth 64) := e6.writes
    simpa [bp5, ten5] using h
  obtain ⟨s7, a7, r7, e7⟩ :=
    (mov_m8_r8_effect_step 0x107853 0x40 (by simp [RexPrefix]) 5
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x7853 _
        (by decide +kernel) (by decide +kernel)) ⟨e6.rip, by
        change MemWritable s6 (stackPtr s6 + 8) 1
        exact stack_writable1 pre f6 (by decide), by
        change RangeApart (stackPtr s6 + 8) 1 0x107853 5
        exact ScalarFrame.stack_code (offset := 8) (len := 1)
          (codeOffset := 0x7853) (codeLen := 5) pre.toCalleePre f6.toFrameState
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7858 (by decide)))
  have g7 : AgreesExcept [.mem (stackPtr s6 + 8) 1, .rip] s6 s7 := by
    simpa [movM64R64Effect_components, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e7.agrees
  have f7 := after_store pre f6 a7 r7 g7 (by decide)
  have sp7 : stackPtr s7 = stackPtr s := ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 4) (by simp)
  have scratch7 : memLoad s7.external (stackPtr s + 8) 8 = 0 := by
    have h : memLoad s7.external (stackPtr s6 + 8) 8 = (s6.regValue .rbp).setWidth 8 := e7.writes
    rwa [sp6, bp6] at h
  refine ⟨s7, f7, e7.rip, ?_, ?_, scratch7, ?_⟩
  · exact (((g5.trans g6).trans g7).read (n := 64) (r := 2) (by simp)).trans dx4
  · exact (g7.read (n := 64) (r := 5) (by simp)).trans bp6
  · exact ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).mono
      (by simp only [sp2, sp6]; simp)

end P256.Proofs.Nonce.Initialize.Prepare.Scan
