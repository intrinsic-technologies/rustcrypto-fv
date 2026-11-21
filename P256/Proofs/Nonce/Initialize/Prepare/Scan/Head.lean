import P256.Proofs.Nonce.Initialize.Prepare.Scan.Setup
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Common.Instructions.Setb.Memory.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Scan

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions.Setb

theorem head [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107822)
    (high : s.regValue .rcx = 0xffffffff00000000) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x10783b ∧
      t.regValue .rbx = 0xffffffff00000000 ∧ t.regValue .rcx = 0 ∧
      t.regValue .rbp = 0 ∧ t.regValue .r10 = 0 ∧
      memLoad t.external (stackPtr s + 8) 8 = 0 ∧
      AgreesExcept [.mem (stackPtr s + 8) 1, .reg 5, .reg 3, .reg 1,
        .reg 10, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (xor_r32_r32_effect_step 0x107822 0xed rfl).advances (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7822 _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7824 (by decide)))
  have g1 : AgreesExcept [.reg 5, .flags, .rip] s s1 := e1.agrees
  have f1 := stage.after_registers a1 r1 g1 (by simp [Component.Covers]) (by simp)
  have bp1 : s1.regValue .rbp = 0 := by
    have h := e1.writes
    change s1.regValue .rbp = (((s.regValue .rbp).setWidth 32) ^^^
      ((s.regValue .rbp).setWidth 32)).setWidth 64 at h
    simpa using h
  have cx1 : s1.regValue .rcx = 0xffffffff00000000 :=
    (g1.read (n := 64) (r := 1) (by simp)).trans high
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_r64_r64_effect_step 0x107824 0x48 0xcb (by simp [RexWPrefix]) rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x7824 _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7827 (by decide)))
  have g2 : AgreesExcept [.reg 3, .rip] s1 s2 := e2.agrees
  have f2 := f1.after_registers a2 r2 g2 (by simp [Component.Covers]) (by simp)
  have bx2 : s2.regValue .rbx = 0xffffffff00000000 := e2.writes.trans cx1
  have cx2 : s2.regValue .rcx = 0xffffffff00000000 :=
    (g2.read (n := 64) (r := 1) (by simp)).trans cx1
  obtain ⟨s3, a3, r3, e3⟩ :=
    (test_r64_r64_effect_step 0x107827 0x48 0xc9 (by simp [RexWPrefix]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x7827 _
        (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x782a (by decide)))
  have g3 : AgreesExcept [.flags, .rip] s2 s3 := e3.agrees
  have f3 := f2.after_registers a3 r3 g3 (by simp [Component.Covers]) (by simp)
  have zero3 : (StatusFlags.ofRFLAGS s3.RFLAGS).ZF = false := by
    have h := e3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s3.RFLAGS).ZF =
      ((s2.regValue .rcx &&& s2.regValue .rcx) == 0) at h
    rwa [cx2] at h
  have bp3 : s3.regValue .rbp = 0 := ((g2.trans g3).read (n := 64) (r := 5) (by simp)).trans bp1
  obtain ⟨s4, a4, r4, e4⟩ :=
    (setcc_r8_rex_effect_step 0x10782a 0x40 0x94 0xc5 (by simp [RexPrefix])
      (.inr rfl) rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x782a _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x782e (by decide)))
  have g4 : AgreesExcept [.reg 5, .rip] s3 s4 := e4.agrees
  have f4 := f3.after_registers a4 r4 g4 (by simp [Component.Covers]) (by simp)
  have bp4 : s4.regValue .rbp = 0 := by
    have h := e4.writes
    change s4.regValue .rbp = mergeGPR 8
      (if (StatusFlags.ofRFLAGS s3.RFLAGS).ZF then 1 else 0) (s3.regValue .rbp) at h
    rwa [zero3, bp3] at h
  have zero4 : (StatusFlags.ofRFLAGS s4.RFLAGS).ZF = false := by
    rw [g4.rflags (by simp) (by simp)]
    exact zero3
  have sp4 : stackPtr s4 = stackPtr s :=
    (((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 4) (by simp)
  obtain ⟨s5, a5, r5, e5⟩ :=
    (setcc_m8_effect_step 0x10782e 0x94 (.inr rfl) 0 (.sib 4 none 0 (.d8 8))
      (by decide +kernel) rfl rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x782e _
        (by decide +kernel) (by decide +kernel)) ⟨e4.rip, by
        change MemWritable s4 (stackPtr s4 + 8) 1
        exact stack_writable1 pre f4 (by decide), by
        change RangeApart (stackPtr s4 + 8) 1 0x10782e 5
        exact ScalarFrame.stack_code (offset := 8) (len := 1)
          (codeOffset := 0x782e) (codeLen := 5) pre.toCalleePre f4.toFrameState
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7833 (by decide)))
  have g5 : AgreesExcept [.mem (stackPtr s4 + 8) 1, .rip] s4 s5 := by
    simpa [P256.Proofs.Common.Instructions.Setb.setccM8Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e5.agrees
  have f5 := after_store pre f4 a5 r5 g5 (by decide)
  have scratch5 : memLoad s5.external (stackPtr s4 + 8) 8 = 0 := by
    have h : memLoad s5.external (stackPtr s4 + 8) 8 =
      (if (StatusFlags.ofRFLAGS s4.RFLAGS).ZF then 1 else 0) := e5.writes
    rwa [zero4] at h
  have sp5 : stackPtr s5 = stackPtr s4 := g5.read (n := 64) (r := 4) (by simp)
  obtain ⟨s6, a6, r6, e6⟩ :=
    (movzx_r32_m8_effect_step 0x107833 1
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x7833 _
        (by decide +kernel) (by decide +kernel)) ⟨e5.rip, by
        change MemReadable s5 (stackPtr s5 + 8) 1
        exact ScalarFrame.stack_readable pre.toCalleePre f5.toFrameState
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7838 (by decide)))
  have g6 : AgreesExcept [.reg 1, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers a6 r6 g6 (by simp [Component.Covers]) (by simp)
  have cx6 : s6.regValue .rcx = 0 := by
    have h : s6.regValue .rcx = (memLoad s5.external (stackPtr s5 + 8) 8).setWidth 64 := e6.writes
    rwa [sp5, scratch5] at h
  obtain ⟨s7, a7, r7, e7⟩ :=
    (xor_r32_r32_rex_effect_step 0x107838 0x45 0xd2 (by simp [RexNoWPrefix]) rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x7838 _
        (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x783b (by decide)))
  have g7 : AgreesExcept [.reg 10, .flags, .rip] s6 s7 := e7.agrees
  have f7 := f6.after_registers a7 r7 g7 (by simp [Component.Covers]) (by simp)
  have ten7 : s7.regValue .r10 = 0 := by
    have h := e7.writes
    change s7.regValue .r10 = (((s6.regValue .r10).setWidth 32) ^^^
      ((s6.regValue .r10).setWidth 32)).setWidth 64 at h
    simpa using h
  refine ⟨s7, f7, e7.rip, ?_, ?_, ?_, ten7, ?_, ?_⟩
  · exact (((((g3.trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 3) (by simp)).trans bx2
  · exact (g7.read (n := 64) (r := 1) (by simp)).trans cx6
  · exact (((g5.trans g6).trans g7).read (n := 64) (r := 5) (by simp)).trans bp4
  · rw [(g6.trans g7).external (by simp [Component.Covers])]
    simpa only [sp4] using scratch5
  · exact ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).mono
      (by simp only [sp4]; simp)

end P256.Proofs.Nonce.Initialize.Prepare.Scan
