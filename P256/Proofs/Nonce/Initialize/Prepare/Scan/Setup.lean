import P256.Proofs.Nonce.Initialize.Prepare.Guard
import P256.Proofs.Common.Instructions.StoreByte
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Scan

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions

theorem setup [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107808) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x107822 ∧
      t.regValue .rcx = s.regValue .rbp ∧ t.regValue .rsi = 1 ∧
      memLoad t.external (stackPtr s + 184) 64 = s.regValue .rsi ∧
      AgreesExcept [.mem (stackPtr s + 184) 8, .mem (stackPtr s + 8) 1,
        .reg 7, .reg 6, .reg 1, .rip] s t := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_m64_r64_effect_step 0x107808 0x48 (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl).advances (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x7808 _
        (by decide +kernel) (by decide +kernel)) ⟨rip, by
        change MemWritable s (stackPtr s + 184) 8
        exact stack_writable8 pre stage (by decide) (by decide), by
        change RangeApart (stackPtr s + 184) 8 0x107808 8
        exact ScalarFrame.stack_code (offset := 184) (len := 8)
          (codeOffset := 0x7808) (codeLen := 8) pre.toCalleePre stage.toFrameState
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7810 (by decide)))
  have g1 : AgreesExcept [.mem (stackPtr s + 184) 8, .rip] s s1 := by
    simpa [movM64R64Effect_components, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_store pre stage a1 r1 g1 (by decide)
  have secret1 : memLoad s1.external (stackPtr s + 184) 64 = s.regValue .rsi := e1.writes
  have sp1 : stackPtr s1 = stackPtr s := g1.read (n := 64) (r := 4) (by simp)
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_m8_imm8_effect_step 0x107810 (.sib 4 none 0 (.d8 8))
      (by decide +kernel) rfl rfl 1).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x7810 _
        (by decide +kernel) (by decide +kernel)) ⟨e1.rip, by
        change MemWritable s1 (stackPtr s1 + 8) 1
        exact stack_writable1 pre f1 (by decide), by
        change RangeApart (stackPtr s1 + 8) 1 0x107810 5
        exact ScalarFrame.stack_code (offset := 8) (len := 1)
          (codeOffset := 0x7810) (codeLen := 5) pre.toCalleePre f1.toFrameState
          (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7815 (by decide)))
  have g2 : AgreesExcept [.mem (stackPtr s1 + 8) 1, .rip] s1 s2 := by
    simpa [movM8Imm8Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := after_store pre f1 a2 r2 g2 (by decide)
  have scratch2 : memLoad s2.external (stackPtr s1 + 8) 8 = 1 := e2.writes
  have sp2 : stackPtr s2 = stackPtr s1 := g2.read (n := 64) (r := 4) (by simp)
  obtain ⟨s3, a3, r3, e3⟩ :=
    (lea_r64_effect_step 0x107815 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x7815 _
        (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x781a (by decide)))
  have g3 : AgreesExcept [.reg 7, .rip] s2 s3 := e3.agrees
  have f3 := f2.after_registers a3 r3 g3 (by simp [Component.Covers]) (by simp)
  have sp3 : stackPtr s3 = stackPtr s1 := (g3.read (n := 64) (r := 4) (by simp)).trans sp2
  have scratch3 : memLoad s3.external (stackPtr s3 + 8) 8 = 1 := by
    rw [sp3, g3.external (by simp [Component.Covers])]
    exact scratch2
  obtain ⟨s4, a4, r4, e4⟩ :=
    (movzx_r32_m8_effect_step 0x10781a 6
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x781a _
        (by decide +kernel) (by decide +kernel)) ⟨e3.rip, by
        change MemReadable s3 (stackPtr s3 + 8) 1
        exact ScalarFrame.stack_readable pre.toCalleePre f3.toFrameState
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x781f (by decide)))
  have g4 : AgreesExcept [.reg 6, .rip] s3 s4 := e4.agrees
  have f4 := f3.after_registers a4 r4 g4 (by simp [Component.Covers]) (by simp)
  have si4 : s4.regValue .rsi = 1 := by
    have h : s4.regValue .rsi = (memLoad s3.external (stackPtr s3 + 8) 8).setWidth 64 := e4.writes
    rwa [scratch3] at h
  obtain ⟨s5, a5, r5, e5⟩ :=
    (mov_r64_r64_effect_step 0x10781f 0x48 0xe9 (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x781f _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7822 (by decide)))
  have g5 : AgreesExcept [.reg 1, .rip] s4 s5 := e5.agrees
  have f5 := f4.after_registers a5 r5 g5 (by simp [Component.Covers]) (by simp)
  have total := (((g1.trans g2).trans g3).trans g4).trans g5
  refine ⟨s5, f5, e5.rip, ?_, ?_, ?_, ?_⟩
  · exact e5.writes.trans ((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 5) (by simp))
  · exact (g5.read (n := 64) (r := 6) (by simp)).trans si4
  · rw [((g3.trans g4).trans g5).external (by simp [Component.Covers])]
    refine (Program.memLoad_agrees_apart g2 ?_).trans secret1
    intro a n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with he | he
    · cases he
      rw [sp1]
      intro i hi j hj he
      apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj)
        (hl := by decide) (show OffsetsApart 8 1 184 8 by unfold OffsetsApart; decide +kernel) he
    · cases he
  · exact total.mono (by simp only [sp1]; simp)

end P256.Proofs.Nonce.Initialize.Prepare.Scan
