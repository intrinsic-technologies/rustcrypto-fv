import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.State
import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Effect
import P256.Proofs.Nonce.Initialize.Conversions.XorImmediate
import P256.Proofs.Nonce.Initialize.Conversions.Neg32
import P256.Proofs.Common.Instructions.Cmov32
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Common.Instructions.Setb.Memory.Triple
import P256.Proofs.Common.Instructions.Carry.Effect
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.NopMem.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions P256.Proofs.Nonce.Initialize.Conversions.Bsr
open P256.Proofs.Nonce.Initialize.Conversions.XorImmediate P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Nonce.Initialize.Conversions.Neg32

theorem high_scan_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (state : HighLimbState initial s boundary) :
    ∃ t, HighScanState initial t boundary := by
  let s0 := s
  have f0 := state.toStage
  have rip0 := state.rip
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (and_r32_r32_rex_effect_step 0x106f79 0x44 0xca (by simp [RexNoWPrefix]) rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x6f79 _
        (by decide +kernel) (by decide +kernel)) rip0
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f7c (by decide)))
  have g1 : AgreesExcept [.reg 2, .flags, .rip] s0 s1 := e1.agrees
  have f1 := after_registers pre f0 run1 ready1 g1 (by simp [Component.Covers]) (by simp)
  have value1 : s1.regValue .rdx = 0 := by
    have h : s1.regValue .rdx = ((s0.regValue .rdx).setWidth 32 &&& (s0.regValue .r9).setWidth 32).setWidth 64 := e1.writes
    rw [state.rdx, state.r9] at h
    exact h
  have read1_rsi : s1.regValue .rsi = initial.regValue .rsi :=
    (g1.read (n := 64) (r := 6) (by simp)).trans state.rsi
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (mov_r64_m64_effect_step 0x106f7c 0x4c (by simp [RexWPrefix]) 2 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x6f7c _
        (by decide +kernel) (by decide +kernel)) ⟨e1.rip, by
        change MemReadable s1 (s1.regValue .rsi + 16) 8
        rw [read1_rsi]
        exact order_readable pre f1 16 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f80 (by decide)))
  have g2 : AgreesExcept [.reg 10, .rip] s1 s2 := e2.agrees
  have f2 := after_registers pre f1 run2 ready2 g2 (by simp [Component.Covers]) (by simp)
  have value2 : s2.regValue .r10 = 0xffffffffffffffff := by
    have h : s2.regValue .r10 = memLoad s1.external (s1.regValue .rsi + 16) 64 := e2.writes
    rw [read1_rsi] at h
    exact h.trans ((order_preserved pre f1).memLoad_limb 2 (by decide))
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (mov_r32_imm32_rex_effect_step 0x106f80 0x41 0xbb (by simp [RexNoWPrefix]) (by decide) 127).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x6f80 _
        (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f86 (by decide)))
  have g3 : AgreesExcept [.reg 11, .rip] s2 s3 := e3.agrees
  have f3 := after_registers pre f2 run3 ready3 g3 (by simp [Component.Covers]) (by simp)
  have value3 : s3.regValue .r11 = 127 := by
    have h : s3.regValue .r11 = 127 := e3.writes
    exact h
  have read3_r10 : s3.regValue .r10 = 0xffffffffffffffff :=
    (g3.read (n := 64) (r := 10) (by simp)).trans value2
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (bsr_r64_r64_effect_step 0x106f86 0x4d 0xda (by simp [RexWPrefix]) rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x6f86 _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f8a (by decide)))
  have g4 : AgreesExcept [.reg 11, .flags, .rip] s3 s4 := e4.agrees
  have f4 := after_registers pre f3 run4 ready4 g4 (by simp [Component.Covers]) (by simp)
  have value4 : s4.regValue .r11 = 63 := by
    have h : s4.regValue .r11 = (bsrSpec64 (s3.regValue .r11) (s3.regValue .r10)).1 := e4.writes
    rw [value3, read3_r10] at h
    exact h.trans (by decide +kernel)
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (xor_r32_imm8_rex_effect_step 0x106f8a 0x41 0xf3 63 (by simp [RexNoWPrefix]) rfl rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x6f8a _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f8e (by decide)))
  have g5 : AgreesExcept [.reg 11, .flags, .rip] s4 s5 := e5.agrees
  have f5 := after_registers pre f4 run5 ready5 g5 (by simp [Component.Covers]) (by simp)
  have value5 : s5.regValue .r11 = 0 := by
    have h : s5.regValue .r11 = ((s4.regValue .r11).setWidth 32 ^^^ 63).setWidth 64 := e5.writes
    rw [value4] at h
    exact h
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (xor_r32_r32_rex_effect_step 0x106f8e 0x45 0xc9 (by simp [RexNoWPrefix]) rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x6f8e _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f91 (by decide)))
  have g6 : AgreesExcept [.reg 9, .flags, .rip] s5 s6 := e6.agrees
  have f6 := after_registers pre f5 run6 ready6 g6 (by simp [Component.Covers]) (by simp)
  have value6 : s6.regValue .r9 = 0 := by
    have h : s6.regValue .r9 = ((s5.regValue .r9).setWidth 32 ^^^ (s5.regValue .r9).setWidth 32).setWidth 64 := e6.writes
    simpa using h
  have read6_r8 : s6.regValue .r8 = 0xffffffff00000000 :=
    ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 8) (by simp)).trans state.r8
  obtain ⟨s7, run7, ready7, e7⟩ :=
    (test_r64_r64_effect_step 0x106f91 0x4d 0xc0 (by simp [RexWPrefix]) rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x6f91 _
        (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f94 (by decide)))
  have g7 : AgreesExcept [.flags, .rip] s6 s7 := e7.agrees
  have f7 := after_registers pre f6 run7 ready7 g7 (by simp [Component.Covers]) (by simp)
  have zf7 : (StatusFlags.ofRFLAGS s7.RFLAGS).ZF = false := by
    have h := e7.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s7.RFLAGS).ZF = ((s6.regValue .r8 &&& s6.regValue .r8) == 0) at h
    rw [read6_r8] at h
    exact h
  have read7_r9 : s7.regValue .r9 = 0 :=
    (g7.read (n := 64) (r := 9) (by simp)).trans value6
  obtain ⟨s8, run8, ready8, e8⟩ :=
    (setcc_r8_rex_effect_step 0x106f94 0x41 0x94 0xc1 (by simp [RexPrefix]) (.inr rfl) rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x6f94 _
        (by decide +kernel) (by decide +kernel)) e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f98 (by decide)))
  have g8 : AgreesExcept [.reg 9, .rip] s7 s8 := e8.agrees
  have f8 := after_registers pre f7 run8 ready8 g8 (by simp [Component.Covers]) (by simp)
  have value8 : s8.regValue .r9 = 0 := by
    have h : s8.regValue .r9 = mergeGPR 8 (if (StatusFlags.ofRFLAGS s7.RFLAGS).ZF then 1 else 0) (s7.regValue .r9) := e8.writes
    rw [zf7, read7_r9] at h
    exact h
  have zf8 : (StatusFlags.ofRFLAGS s8.RFLAGS).ZF = false := by
    rw [g8.rflags (by simp) (by simp)]
    exact zf7
  obtain ⟨s9, run9, ready9, e9⟩ :=
    (setcc_m8_effect_step 0x106f98 0x94 (.inr rfl) 0 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x6f98 _
        (by decide +kernel) (by decide +kernel)) ⟨e8.rip, by
        change MemWritable s8 (stackPtr s8 + 15) 1
        exact scratch_writable pre f8, by
        change RangeApart (stackPtr s8 + 15) 1 0x106f98 5
        exact scratch_code_apart pre f8 (offset := 0x6f98) (len := 5) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f9d (by decide)))
  have g9 : AgreesExcept [.mem (stackPtr initial - 57) 1, .rip] s8 s9 := by
    have h := e9.agrees
    simp only [setccM8Effect_components] at h
    change AgreesExcept [.mem (stackPtr s8 + 15) 1, .rip] s8 s9 at h
    rwa [scratch_address f8] at h
  have f9 := after_scratch pre f8 run9 ready9 g9
  have scratch9 : memLoad s9.external (stackPtr initial - 57) 8 = 0 := by
    have h : memLoad s9.external (stackPtr s8 + 15) 8 = (if (StatusFlags.ofRFLAGS s8.RFLAGS).ZF then 1 else 0) := e9.writes
    rw [scratch_address f8, zf8] at h
    exact h
  obtain ⟨s10, run10, ready10, e10⟩ :=
    (movzx_r_m8_rex_effect_step 0x106f9d 0x44 (by simp [RexPrefix]) 32 (by simp) (by intro seg; rfl) 0 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x6f9d _
        (by decide +kernel) (by decide +kernel)) ⟨e9.rip, by
        change MemReadable s9 (stackPtr s9 + 15) 1
        exact scratch_readable pre f9⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fa3 (by decide)))
  have g10 : AgreesExcept [.reg 8, .rip] s9 s10 := e10.agrees
  have f10 := after_registers pre f9 run10 ready10 g10 (by simp [Component.Covers]) (by simp)
  have value10 : s10.regValue .r8 = 0 := by
    have h : s10.regValue .r8 = (memLoad s9.external (stackPtr s9 + 15) 8).setWidth 64 := e10.writes
    rw [scratch_address f9, scratch9] at h
    exact h
  obtain ⟨s11, run11, ready11, e11⟩ :=
    (neg_r32_rex_effect_step 0x106fa3 0x41 0xd8 (by simp [RexNoWPrefix]) rfl rfl).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x6fa3 _
        (by decide +kernel) (by decide +kernel)) e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fa6 (by decide)))
  have g11 : AgreesExcept [.reg 8, .flags, .rip] s10 s11 := e11.agrees
  have f11 := after_registers pre f10 run11 ready11 g11 (by simp [Component.Covers]) (by simp)
  have value11 : s11.regValue .r8 = 0 := by
    have h : s11.regValue .r8 = (-(s10.regValue .r8).setWidth 32).setWidth 64 := e11.writes
    rw [value10] at h
    exact h
  have read11_r11 : s11.regValue .r11 = 0 :=
    ((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).read (n := 64) (r := 11) (by simp)).trans value5
  obtain ⟨s12, run12, ready12, e12⟩ :=
    (and_r32_r32_rex_effect_step 0x106fa6 0x45 0xd8 (by simp [RexNoWPrefix]) rfl).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x6fa6 _
        (by decide +kernel) (by decide +kernel)) e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fa9 (by decide)))
  have g12 : AgreesExcept [.reg 8, .flags, .rip] s11 s12 := e12.agrees
  have f12 := after_registers pre f11 run12 ready12 g12 (by simp [Component.Covers]) (by simp)
  have value12 : s12.regValue .r8 = 0 := by
    have h : s12.regValue .r8 = ((s11.regValue .r8).setWidth 32 &&& (s11.regValue .r11).setWidth 32).setWidth 64 := e12.writes
    rw [value11, read11_r11] at h
    exact h
  obtain ⟨s13, run13, ready13, e13⟩ :=
    (xor_r32_r32_rex_effect_step 0x106fa9 0x45 0xdb (by simp [RexNoWPrefix]) rfl).advances (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x6fa9 _
        (by decide +kernel) (by decide +kernel)) e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fac (by decide)))
  have g13 : AgreesExcept [.reg 11, .flags, .rip] s12 s13 := e13.agrees
  have f13 := after_registers pre f12 run13 ready13 g13 (by simp [Component.Covers]) (by simp)
  have value13 : s13.regValue .r11 = 0 := by
    have h : s13.regValue .r11 = ((s12.regValue .r11).setWidth 32 ^^^ (s12.regValue .r11).setWidth 32).setWidth 64 := e13.writes
    simpa using h
  have read13_rdi : s13.regValue .rdi = initial.regValue .rdi :=
    (((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (n := 64) (r := 7) (by simp)).trans state.rdi
  have read13_rsi : s13.regValue .rsi = initial.regValue .rsi :=
    (((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (n := 64) (r := 6) (by simp)).trans state.rsi
  have read13_rcx : s13.regValue .rcx = 32 :=
    (((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (n := 64) (r := 1) (by simp)).trans state.rcx
  have read13_r12 : s13.regValue .r12 = initial.regValue .rdx :=
    (((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (n := 64) (r := 12) (by simp)).trans state.r12
  have read13_rax : s13.regValue .rax = 127 :=
    (((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (n := 64) (r := 0) (by simp)).trans state.rax
  have read13_rdx : s13.regValue .rdx = 0 :=
    ((((((((((((g2.trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (n := 64) (r := 2) (by simp)).trans value1
  have read13_r8 : s13.regValue .r8 = 0 :=
    (g13.read (n := 64) (r := 8) (by simp)).trans value12
  have read13_r9 : s13.regValue .r9 = 0 :=
    (((((g9.trans g10).trans g11).trans g12).trans g13).read (n := 64) (r := 9) (by simp)).trans value8
  have read13_r10 : s13.regValue .r10 = 0xffffffffffffffff :=
    (((((((((((g3.trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).read (n := 64) (r := 10) (by simp)).trans value2
  exact ⟨s13, ⟨f13, e13.rip, read13_rdi, read13_rsi, read13_rcx, read13_r12, read13_rax, read13_rdx, read13_r8, read13_r9, read13_r10, value13⟩⟩

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
