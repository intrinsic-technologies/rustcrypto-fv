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

theorem high_limb_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (registers : EntryRegisters initial s) (rip : s.RIP = 0x106f4e) :
    ∃ t, HighLimbState initial t boundary := by
  let s0 := s
  have f0 := stage
  have rip0 := rip
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (mov_r64_r64_effect_step 0x106f4e 0x49 0xd4 (by simp [RexWPrefix]) rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x6f4e _
        (by decide +kernel) (by decide +kernel)) rip0
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f51 (by decide)))
  have g1 : AgreesExcept [.reg 12, .rip] s0 s1 := e1.agrees
  have f1 := after_registers pre f0 run1 ready1 g1 (by simp [Component.Covers]) (by simp)
  have value1 : s1.regValue .r12 = initial.regValue .rdx := by
    have h : s1.regValue .r12 = s0.regValue .rdx := e1.writes
    rw [registers.output] at h
    exact h
  have read1_rsi : s1.regValue .rsi = initial.regValue .rsi :=
    (g1.read (n := 64) (r := 6) (by simp)).trans registers.order
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (mov_r64_m64_effect_step 0x106f51 0x4c (by simp [RexWPrefix]) 0 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x6f51 _
        (by decide +kernel) (by decide +kernel)) ⟨e1.rip, by
        change MemReadable s1 (s1.regValue .rsi + 24) 8
        rw [read1_rsi]
        exact order_readable pre f1 24 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f55 (by decide)))
  have g2 : AgreesExcept [.reg 8, .rip] s1 s2 := e2.agrees
  have f2 := after_registers pre f1 run2 ready2 g2 (by simp [Component.Covers]) (by simp)
  have value2 : s2.regValue .r8 = 0xffffffff00000000 := by
    have h : s2.regValue .r8 = memLoad s1.external (s1.regValue .rsi + 24) 64 := e2.writes
    rw [read1_rsi] at h
    exact h.trans ((order_preserved pre f1).memLoad_limb 3 (by decide))
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (mov_r32_imm32_effect_step 0x106f55 0xb8 (by decide) 127).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x6f55 _
        (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f5a (by decide)))
  have g3 : AgreesExcept [.reg 0, .rip] s2 s3 := e3.agrees
  have f3 := after_registers pre f2 run3 ready3 g3 (by simp [Component.Covers]) (by simp)
  have value3 : s3.regValue .rax = 127 := by
    have h : s3.regValue .rax = 127 := e3.writes
    exact h
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (mov_r32_imm32_rex_effect_step 0x106f5a 0x41 0xb9 (by simp [RexNoWPrefix]) (by decide) 127).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x6f5a _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f60 (by decide)))
  have g4 : AgreesExcept [.reg 9, .rip] s3 s4 := e4.agrees
  have f4 := after_registers pre f3 run4 ready4 g4 (by simp [Component.Covers]) (by simp)
  have value4 : s4.regValue .r9 = 127 := by
    have h : s4.regValue .r9 = 127 := e4.writes
    exact h
  have read4_r8 : s4.regValue .r8 = 0xffffffff00000000 :=
    ((g3.trans g4).read (n := 64) (r := 8) (by simp)).trans value2
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (bsr_r64_r64_effect_step 0x106f60 0x4d 0xc8 (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x6f60 _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f64 (by decide)))
  have g5 : AgreesExcept [.reg 9, .flags, .rip] s4 s5 := e5.agrees
  have f5 := after_registers pre f4 run5 ready5 g5 (by simp [Component.Covers]) (by simp)
  have value5 : s5.regValue .r9 = 63 := by
    have h : s5.regValue .r9 = (bsrSpec64 (s4.regValue .r9) (s4.regValue .r8)).1 := e5.writes
    rw [value4, read4_r8] at h
    exact h.trans (by decide +kernel)
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (xor_r32_imm8_rex_effect_step 0x106f64 0x41 0xf1 63 (by simp [RexNoWPrefix]) rfl rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x6f64 _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f68 (by decide)))
  have g6 : AgreesExcept [.reg 9, .flags, .rip] s5 s6 := e6.agrees
  have f6 := after_registers pre f5 run6 ready6 g6 (by simp [Component.Covers]) (by simp)
  have value6 : s6.regValue .r9 = 0 := by
    have h : s6.regValue .r9 = ((s5.regValue .r9).setWidth 32 ^^^ 63).setWidth 64 := e6.writes
    rw [value5] at h
    exact h
  obtain ⟨s7, run7, ready7, e7⟩ :=
    (mov_m8_imm8_effect_step 0x106f68 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl 1).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x6f68 _
        (by decide +kernel) (by decide +kernel)) ⟨e6.rip, by
        change MemWritable s6 (stackPtr s6 + 15) 1
        exact scratch_writable pre f6, by
        change RangeApart (stackPtr s6 + 15) 1 0x106f68 5
        exact scratch_code_apart pre f6 (offset := 0x6f68) (len := 5) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f6d (by decide)))
  have g7 : AgreesExcept [.mem (stackPtr initial - 57) 1, .rip] s6 s7 := by
    have h := e7.agrees
    simp only [movM8Imm8Effect_components] at h
    change AgreesExcept [.mem (stackPtr s6 + 15) 1, .rip] s6 s7 at h
    rwa [scratch_address f6] at h
  have f7 := after_scratch pre f6 run7 ready7 g7
  have scratch7 : memLoad s7.external (stackPtr initial - 57) 8 = 1 := by
    have h : memLoad s7.external (stackPtr s6 + 15) 8 = 1 := e7.writes
    rw [scratch_address f6] at h
    exact h
  obtain ⟨s8, run8, ready8, e8⟩ :=
    (lea_r64_effect_step 0x106f6d 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x6f6d _
        (by decide +kernel) (by decide +kernel)) e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f72 (by decide)))
  have g8 : AgreesExcept [.reg 14, .rip] s7 s8 := e8.agrees
  have f8 := after_registers pre f7 run8 ready8 g8 (by simp [Component.Covers]) (by simp)
  have scratch8 : memLoad s8.external (stackPtr initial - 57) 8 = 1 := by
    rw [g8.external (by simp [Component.Covers])]
    exact scratch7
  obtain ⟨s9, run9, ready9, e9⟩ :=
    (movzx_r32_m8_effect_step 0x106f72 2 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x6f72 _
        (by decide +kernel) (by decide +kernel)) ⟨e8.rip, by
        change MemReadable s8 (stackPtr s8 + 15) 1
        exact scratch_readable pre f8⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f77 (by decide)))
  have g9 : AgreesExcept [.reg 2, .rip] s8 s9 := e9.agrees
  have f9 := after_registers pre f8 run9 ready9 g9 (by simp [Component.Covers]) (by simp)
  have value9 : s9.regValue .rdx = 1 := by
    have h : s9.regValue .rdx = (memLoad s8.external (stackPtr s8 + 15) 8).setWidth 64 := e9.writes
    rw [scratch_address f8, scratch8] at h
    exact h
  obtain ⟨s10, run10, ready10, e10⟩ :=
    (neg_r32_effect_step 0x106f77 0xda rfl rfl).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x6f77 _
        (by decide +kernel) (by decide +kernel)) e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f79 (by decide)))
  have g10 : AgreesExcept [.reg 2, .flags, .rip] s9 s10 := e10.agrees
  have f10 := after_registers pre f9 run10 ready10 g10 (by simp [Component.Covers]) (by simp)
  have value10 : s10.regValue .rdx = 4294967295 := by
    have h : s10.regValue .rdx = (-(s9.regValue .rdx).setWidth 32).setWidth 64 := e10.writes
    rw [value9] at h
    exact h
  have read10_rdi : s10.regValue .rdi = initial.regValue .rdi :=
    ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 7) (by simp)).trans registers.input
  have read10_rsi : s10.regValue .rsi = initial.regValue .rsi :=
    ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 6) (by simp)).trans registers.order
  have read10_rcx : s10.regValue .rcx = 32 :=
    ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 1) (by simp)).trans registers.length
  have read10_r12 : s10.regValue .r12 = initial.regValue .rdx :=
    (((((((((g2.trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 12) (by simp)).trans value1
  have read10_rax : s10.regValue .rax = 127 :=
    (((((((g4.trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 0) (by simp)).trans value3
  have read10_r8 : s10.regValue .r8 = 0xffffffff00000000 :=
    ((((((((g3.trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 8) (by simp)).trans value2
  have read10_r9 : s10.regValue .r9 = 0 :=
    ((((g7.trans g8).trans g9).trans g10).read (n := 64) (r := 9) (by simp)).trans value6
  exact ⟨s10, ⟨f10, e10.rip, read10_rdi, read10_rsi, read10_rcx, read10_r12, read10_rax, read10_r8, read10_r9, value10⟩⟩

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
