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

theorem middle_scan_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (state : HighScanState initial s boundary) :
    ∃ t, MiddleScanState initial t boundary := by
  let s0 := s
  have f0 := state.toStage
  have rip0 := state.rip
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (test_r64_r64_effect_step 0x106fac 0x4d 0xd2 (by simp [RexWPrefix]) rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x6fac _
        (by decide +kernel) (by decide +kernel)) rip0
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6faf (by decide)))
  have g1 : AgreesExcept [.flags, .rip] s0 s1 := e1.agrees
  have f1 := after_registers pre f0 run1 ready1 g1 (by simp [Component.Covers]) (by simp)
  have zf1 : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = false := by
    have h := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = ((s0.regValue .r10 &&& s0.regValue .r10) == 0) at h
    rw [state.r10] at h
    exact h
  have read1_r9 : s1.regValue .r9 = 0 :=
    (g1.read (n := 64) (r := 9) (by simp)).trans state.r9
  have read1_r11 : s1.regValue .r11 = 0 :=
    (g1.read (n := 64) (r := 11) (by simp)).trans state.r11
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (cmovne_r32_r32_rex_effect_step 0x106faf 0x45 0xcb (by simp [RexNoWPrefix]) rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x6faf _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fb3 (by decide)))
  have g2 : AgreesExcept [.reg 9, .rip] s1 s2 := e2.agrees
  have f2 := after_registers pre f1 run2 ready2 g2 (by simp [Component.Covers]) (by simp)
  have value2 : s2.regValue .r9 = 0 := by
    have h : s2.regValue .r9 = ((if condHolds 5 (StatusFlags.ofRFLAGS s1.RFLAGS) then (s1.regValue .r11).setWidth 32 else (s1.regValue .r9).setWidth 32).setWidth 64) := e2.writes
    simpa [read1_r9, read1_r11] using h
  have read2_rsi : s2.regValue .rsi = initial.regValue .rsi :=
    ((g1.trans g2).read (n := 64) (r := 6) (by simp)).trans state.rsi
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (mov_r64_m64_effect_step 0x106fb3 0x4c (by simp [RexWPrefix]) 2 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x6fb3 _
        (by decide +kernel) (by decide +kernel)) ⟨e2.rip, by
        change MemReadable s2 (s2.regValue .rsi + 8) 8
        rw [read2_rsi]
        exact order_readable pre f2 8 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fb7 (by decide)))
  have g3 : AgreesExcept [.reg 10, .rip] s2 s3 := e3.agrees
  have f3 := after_registers pre f2 run3 ready3 g3 (by simp [Component.Covers]) (by simp)
  have value3 : s3.regValue .r10 = 0xbce6faada7179e84 := by
    have h : s3.regValue .r10 = memLoad s2.external (s2.regValue .rsi + 8) 64 := e3.writes
    rw [read2_rsi] at h
    exact h.trans ((order_preserved pre f2).memLoad_limb 1 (by decide))
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (mov_r32_imm32_effect_step 0x106fb7 0xbb (by decide) 127).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x6fb7 _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fbc (by decide)))
  have g4 : AgreesExcept [.reg 3, .rip] s3 s4 := e4.agrees
  have f4 := after_registers pre f3 run4 ready4 g4 (by simp [Component.Covers]) (by simp)
  have value4 : s4.regValue .rbx = 127 := by
    have h : s4.regValue .rbx = 127 := e4.writes
    exact h
  have read4_r10 : s4.regValue .r10 = 0xbce6faada7179e84 :=
    (g4.read (n := 64) (r := 10) (by simp)).trans value3
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (bsr_r64_r64_effect_step 0x106fbc 0x49 0xda (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x6fbc _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fc0 (by decide)))
  have g5 : AgreesExcept [.reg 3, .flags, .rip] s4 s5 := e5.agrees
  have f5 := after_registers pre f4 run5 ready5 g5 (by simp [Component.Covers]) (by simp)
  have value5 : s5.regValue .rbx = 63 := by
    have h : s5.regValue .rbx = (bsrSpec64 (s4.regValue .rbx) (s4.regValue .r10)).1 := e5.writes
    rw [value4, read4_r10] at h
    exact h.trans (by decide +kernel)
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (xor_r32_imm8_effect_step 0x106fc0 0xf3 63 rfl rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x6fc0 _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fc3 (by decide)))
  have g6 : AgreesExcept [.reg 3, .flags, .rip] s5 s6 := e6.agrees
  have f6 := after_registers pre f5 run6 ready6 g6 (by simp [Component.Covers]) (by simp)
  have value6 : s6.regValue .rbx = 0 := by
    have h : s6.regValue .rbx = ((s5.regValue .rbx).setWidth 32 ^^^ 63).setWidth 64 := e6.writes
    rw [value5] at h
    exact h
  have read6_r9 : s6.regValue .r9 = 0 :=
    ((((g3.trans g4).trans g5).trans g6).read (n := 64) (r := 9) (by simp)).trans value2
  obtain ⟨s7, run7, ready7, e7⟩ :=
    (mov_m8_r8_effect_step 0x106fc3 0x44 (by simp [RexPrefix]) 1 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x6fc3 _
        (by decide +kernel) (by decide +kernel)) ⟨e6.rip, by
        change MemWritable s6 (stackPtr s6 + 15) 1
        exact scratch_writable pre f6, by
        change RangeApart (stackPtr s6 + 15) 1 0x106fc3 5
        exact scratch_code_apart pre f6 (offset := 0x6fc3) (len := 5) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fc8 (by decide)))
  have g7 : AgreesExcept [.mem (stackPtr initial - 57) 1, .rip] s6 s7 := by
    have h := e7.agrees
    simp only [storeEffect_components] at h
    change AgreesExcept [.mem (stackPtr s6 + 15) 1, .rip] s6 s7 at h
    rwa [scratch_address f6] at h
  have f7 := after_scratch pre f6 run7 ready7 g7
  have scratch7 : memLoad s7.external (stackPtr initial - 57) 8 = 0 := by
    have h : memLoad s7.external (stackPtr s6 + 15) 8 = (s6.regValue .r9).setWidth 8 := e7.writes
    rw [scratch_address f6, read6_r9] at h
    exact h
  obtain ⟨s8, run8, ready8, e8⟩ :=
    (movzx_r_m8_rex_effect_step 0x106fc8 0x44 (by simp [RexPrefix]) 32 (by simp) (by intro seg; rfl) 7 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x6fc8 _
        (by decide +kernel) (by decide +kernel)) ⟨e7.rip, by
        change MemReadable s7 (stackPtr s7 + 15) 1
        exact scratch_readable pre f7⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fce (by decide)))
  have g8 : AgreesExcept [.reg 15, .rip] s7 s8 := e8.agrees
  have f8 := after_registers pre f7 run8 ready8 g8 (by simp [Component.Covers]) (by simp)
  have value8 : s8.regValue .r15 = 0 := by
    have h : s8.regValue .r15 = (memLoad s7.external (stackPtr s7 + 15) 8).setWidth 64 := e8.writes
    rw [scratch_address f7, scratch7] at h
    exact h
  obtain ⟨s9, run9, ready9, e9⟩ :=
    (neg_r32_rex_effect_step 0x106fce 0x41 0xdf (by simp [RexNoWPrefix]) rfl rfl).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x6fce _
        (by decide +kernel) (by decide +kernel)) e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fd1 (by decide)))
  have g9 : AgreesExcept [.reg 15, .flags, .rip] s8 s9 := e9.agrees
  have f9 := after_registers pre f8 run9 ready9 g9 (by simp [Component.Covers]) (by simp)
  have value9 : s9.regValue .r15 = 0 := by
    have h : s9.regValue .r15 = (-(s8.regValue .r15).setWidth 32).setWidth 64 := e9.writes
    rw [value8] at h
    exact h
  have read9_rbx : s9.regValue .rbx = 0 :=
    (((g7.trans g8).trans g9).read (n := 64) (r := 3) (by simp)).trans value6
  obtain ⟨s10, run10, ready10, e10⟩ :=
    (and_r32_r32_rex_effect_step 0x106fd1 0x41 0xdf (by simp [RexNoWPrefix]) rfl).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x6fd1 _
        (by decide +kernel) (by decide +kernel)) e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fd4 (by decide)))
  have g10 : AgreesExcept [.reg 15, .flags, .rip] s9 s10 := e10.agrees
  have f10 := after_registers pre f9 run10 ready10 g10 (by simp [Component.Covers]) (by simp)
  have value10 : s10.regValue .r15 = 0 := by
    have h : s10.regValue .r15 = ((s9.regValue .r15).setWidth 32 &&& (s9.regValue .rbx).setWidth 32).setWidth 64 := e10.writes
    rw [value9, read9_rbx] at h
    exact h
  have read10_r10 : s10.regValue .r10 = 0xbce6faada7179e84 :=
    (((((((g4.trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 10) (by simp)).trans value3
  obtain ⟨s11, run11, ready11, e11⟩ :=
    (test_r64_r64_effect_step 0x106fd4 0x4d 0xd2 (by simp [RexWPrefix]) rfl).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x6fd4 _
        (by decide +kernel) (by decide +kernel)) e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fd7 (by decide)))
  have g11 : AgreesExcept [.flags, .rip] s10 s11 := e11.agrees
  have f11 := after_registers pre f10 run11 ready11 g11 (by simp [Component.Covers]) (by simp)
  have zf11 : (StatusFlags.ofRFLAGS s11.RFLAGS).ZF = false := by
    have h := e11.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s11.RFLAGS).ZF = ((s10.regValue .r10 &&& s10.regValue .r10) == 0) at h
    rw [read10_r10] at h
    exact h
  have read11_r9 : s11.regValue .r9 = 0 :=
    (((((((((g3.trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).read (n := 64) (r := 9) (by simp)).trans value2
  have read11_r11 : s11.regValue .r11 = 0 :=
    (((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).read (n := 64) (r := 11) (by simp)).trans state.r11
  obtain ⟨s12, run12, ready12, e12⟩ :=
    (cmovne_r32_r32_rex_effect_step 0x106fd7 0x45 0xcb (by simp [RexNoWPrefix]) rfl).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x6fd7 _
        (by decide +kernel) (by decide +kernel)) e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fdb (by decide)))
  have g12 : AgreesExcept [.reg 9, .rip] s11 s12 := e12.agrees
  have f12 := after_registers pre f11 run12 ready12 g12 (by simp [Component.Covers]) (by simp)
  have value12 : s12.regValue .r9 = 0 := by
    have h : s12.regValue .r9 = ((if condHolds 5 (StatusFlags.ofRFLAGS s11.RFLAGS) then (s11.regValue .r11).setWidth 32 else (s11.regValue .r9).setWidth 32).setWidth 64) := e12.writes
    simpa [read11_r9, read11_r11] using h
  have read12_rdi : s12.regValue .rdi = initial.regValue .rdi :=
    ((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 7) (by simp)).trans state.rdi
  have read12_rsi : s12.regValue .rsi = initial.regValue .rsi :=
    ((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 6) (by simp)).trans state.rsi
  have read12_rcx : s12.regValue .rcx = 32 :=
    ((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 1) (by simp)).trans state.rcx
  have read12_r12 : s12.regValue .r12 = initial.regValue .rdx :=
    ((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 12) (by simp)).trans state.r12
  have read12_rax : s12.regValue .rax = 127 :=
    ((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 0) (by simp)).trans state.rax
  have read12_rdx : s12.regValue .rdx = 0 :=
    ((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 2) (by simp)).trans state.rdx
  have read12_r8 : s12.regValue .r8 = 0 :=
    ((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 8) (by simp)).trans state.r8
  have read12_r15 : s12.regValue .r15 = 0 :=
    ((g11.trans g12).read (n := 64) (r := 15) (by simp)).trans value10
  exact ⟨s12, ⟨f12, e12.rip, read12_rdi, read12_rsi, read12_rcx, read12_r12, read12_rax, read12_rdx, read12_r8, value12, read12_r15⟩⟩

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
