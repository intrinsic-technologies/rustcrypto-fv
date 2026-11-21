import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix.State
import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Memory
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

theorem low_scan_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (state : MiddleScanState initial s boundary) :
    ∃ t, LowScanState initial t boundary := by
  let s0 := s
  have f0 := state.toStage
  have rip0 := state.rip
  have word0 : memLoad s0.external (s0.regValue .rsi + 0) 64 = 0xf3b9cac2fc632551 := by
    rw [state.rsi]
    exact (order_preserved pre f0).memLoad_limb 0 (by decide)
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (bsr_r64_m64_effect_step 0x106fdb 0x48 (by simp [RexWPrefix]) 0 (.base 6 .none) (by decide +kernel) rfl rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x6fdb _
        (by decide +kernel) (by decide +kernel)) ⟨rip0, by
        change MemReadable s0 (s0.regValue .rsi + 0) 8
        rw [state.rsi]
        exact order_readable pre f0 0 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fdf (by decide)))
  have g1 : AgreesExcept [.reg 0, .flags, .rip] s0 s1 := e1.agrees
  have f1 := after_registers pre f0 run1 ready1 g1 (by simp [Component.Covers]) (by simp)
  have value1 : s1.regValue .rax = 63 := by
    have h : s1.regValue .rax = (bsrSpec64 (s0.regValue .rax) (memLoad s0.external (s0.regValue .rsi + 0) 64)).1 := e1.writes
    rw [state.rax, word0] at h
    exact h.trans (by decide +kernel)
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (xor_r32_imm8_effect_step 0x106fdf 0xf0 63 rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x6fdf _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fe2 (by decide)))
  have g2 : AgreesExcept [.reg 0, .flags, .rip] s1 s2 := e2.agrees
  have f2 := after_registers pre f1 run2 ready2 g2 (by simp [Component.Covers]) (by simp)
  have value2 : s2.regValue .rax = 0 := by
    have h : s2.regValue .rax = ((s1.regValue .rax).setWidth 32 ^^^ 63).setWidth 64 := e2.writes
    rw [value1] at h
    exact h
  have read2_r9 : s2.regValue .r9 = 0 :=
    ((g1.trans g2).read (n := 64) (r := 9) (by simp)).trans state.r9
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (mov_m8_r8_effect_step 0x106fe2 0x44 (by simp [RexPrefix]) 1 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x6fe2 _
        (by decide +kernel) (by decide +kernel)) ⟨e2.rip, by
        change MemWritable s2 (stackPtr s2 + 15) 1
        exact scratch_writable pre f2, by
        change RangeApart (stackPtr s2 + 15) 1 0x106fe2 5
        exact scratch_code_apart pre f2 (offset := 0x6fe2) (len := 5) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fe7 (by decide)))
  have g3 : AgreesExcept [.mem (stackPtr initial - 57) 1, .rip] s2 s3 := by
    have h := e3.agrees
    simp only [storeEffect_components] at h
    change AgreesExcept [.mem (stackPtr s2 + 15) 1, .rip] s2 s3 at h
    rwa [scratch_address f2] at h
  have f3 := after_scratch pre f2 run3 ready3 g3
  have scratch3 : memLoad s3.external (stackPtr initial - 57) 8 = 0 := by
    have h : memLoad s3.external (stackPtr s2 + 15) 8 = (s2.regValue .r9).setWidth 8 := e3.writes
    rw [scratch_address f2, read2_r9] at h
    exact h
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (movzx_r32_m8_effect_step 0x106fe7 6 (.sib 4 none 0 (.d8 15)) (by decide +kernel) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x6fe7 _
        (by decide +kernel) (by decide +kernel)) ⟨e3.rip, by
        change MemReadable s3 (stackPtr s3 + 15) 1
        exact scratch_readable pre f3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fec (by decide)))
  have g4 : AgreesExcept [.reg 6, .rip] s3 s4 := e4.agrees
  have f4 := after_registers pre f3 run4 ready4 g4 (by simp [Component.Covers]) (by simp)
  have value4 : s4.regValue .rsi = 0 := by
    have h : s4.regValue .rsi = (memLoad s3.external (stackPtr s3 + 15) 8).setWidth 64 := e4.writes
    rw [scratch_address f3, scratch3] at h
    exact h
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (neg_r32_effect_step 0x106fec 0xde rfl rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x6fec _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6fee (by decide)))
  have g5 : AgreesExcept [.reg 6, .flags, .rip] s4 s5 := e5.agrees
  have f5 := after_registers pre f4 run5 ready5 g5 (by simp [Component.Covers]) (by simp)
  have value5 : s5.regValue .rsi = 0 := by
    have h : s5.regValue .rsi = (-(s4.regValue .rsi).setWidth 32).setWidth 64 := e5.writes
    rw [value4] at h
    exact h
  have read5_rax : s5.regValue .rax = 0 :=
    (((g3.trans g4).trans g5).read (n := 64) (r := 0) (by simp)).trans value2
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (and_r32_r32_effect_step 0x106fee 0xc6 rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x6fee _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6ff0 (by decide)))
  have g6 : AgreesExcept [.reg 6, .flags, .rip] s5 s6 := e6.agrees
  have f6 := after_registers pre f5 run6 ready6 g6 (by simp [Component.Covers]) (by simp)
  have value6 : s6.regValue .rsi = 0 := by
    have h : s6.regValue .rsi = ((s5.regValue .rsi).setWidth 32 &&& (s5.regValue .rax).setWidth 32).setWidth 64 := e6.writes
    rw [value5, read5_rax] at h
    exact h
  have read6_r8 : s6.regValue .r8 = 0 :=
    ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 8) (by simp)).trans state.r8
  have read6_rdx : s6.regValue .rdx = 0 :=
    ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 2) (by simp)).trans state.rdx
  obtain ⟨s7, run7, ready7, e7⟩ :=
    (add_r64_r64_effect_step 0x106ff0 0x49 0xd0 (by simp [RexWPrefix]) rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x6ff0 _
        (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6ff3 (by decide)))
  have g7 : AgreesExcept [.reg 8, .flags, .rip] s6 s7 := e7.agrees
  have f7 := after_registers pre f6 run7 ready7 g7 (by simp [Component.Covers]) (by simp)
  have value7 : s7.regValue .r8 = 0 := by
    have h : s7.regValue .r8 = s6.regValue .r8 + s6.regValue .rdx := e7.writes
    rw [read6_r8, read6_rdx] at h
    exact h
  have read7_r15 : s7.regValue .r15 = 0 :=
    (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 15) (by simp)).trans state.r15
  obtain ⟨s8, run8, ready8, e8⟩ :=
    (add_r64_r64_effect_step 0x106ff3 0x4d 0xf8 (by simp [RexWPrefix]) rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x6ff3 _
        (by decide +kernel) (by decide +kernel)) e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6ff6 (by decide)))
  have g8 : AgreesExcept [.reg 8, .flags, .rip] s7 s8 := e8.agrees
  have f8 := after_registers pre f7 run8 ready8 g8 (by simp [Component.Covers]) (by simp)
  have value8 : s8.regValue .r8 = 0 := by
    have h : s8.regValue .r8 = s7.regValue .r8 + s7.regValue .r15 := e8.writes
    rw [value7, read7_r15] at h
    exact h
  have read8_rsi : s8.regValue .rsi = 0 :=
    ((g7.trans g8).read (n := 64) (r := 6) (by simp)).trans value6
  obtain ⟨s9, run9, ready9, e9⟩ :=
    (add_r64_r64_effect_step 0x106ff6 0x49 0xf0 (by simp [RexWPrefix]) rfl).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x6ff6 _
        (by decide +kernel) (by decide +kernel)) e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6ff9 (by decide)))
  have g9 : AgreesExcept [.reg 8, .flags, .rip] s8 s9 := e9.agrees
  have f9 := after_registers pre f8 run9 ready9 g9 (by simp [Component.Covers]) (by simp)
  have value9 : s9.regValue .r8 = 0 := by
    have h : s9.regValue .r8 = s8.regValue .r8 + s8.regValue .rsi := e9.writes
    rw [value8, read8_rsi] at h
    exact h
  have read9_rdi : s9.regValue .rdi = initial.regValue .rdi :=
    (((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 7) (by simp)).trans state.rdi
  have read9_rcx : s9.regValue .rcx = 32 :=
    (((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 1) (by simp)).trans state.rcx
  have read9_r12 : s9.regValue .r12 = initial.regValue .rdx :=
    (((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 12) (by simp)).trans state.r12
  exact ⟨s9, ⟨f9, e9.rip, read9_rdi, read9_rcx, read9_r12, value9⟩⟩

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
