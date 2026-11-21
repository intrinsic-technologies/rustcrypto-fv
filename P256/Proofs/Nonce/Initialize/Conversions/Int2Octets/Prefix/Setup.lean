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

theorem setup_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (state : CountState initial s boundary) :
    ∃ t, Stage initial t boundary ∧ LoopRegisters initial t 0 ∧ t.RIP = 0x107050 := by
  let s0 := s
  have f0 := state.toStage
  have rip0 := state.rip
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (mov_r64_r64_effect_step 0x10703b 0x49 0xfd (by simp [RexWPrefix]) rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x703b _
        (by decide +kernel) (by decide +kernel)) rip0
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x703e (by decide)))
  have g1 : AgreesExcept [.reg 13, .rip] s0 s1 := e1.agrees
  have f1 := after_registers pre f0 run1 ready1 g1 (by simp [Component.Covers]) (by simp)
  have value1 : s1.regValue .r13 = initial.regValue .rdi := by
    have h : s1.regValue .r13 = s0.regValue .rdi := e1.writes
    rw [state.rdi] at h
    exact h
  have read1_r12 : s1.regValue .r12 = initial.regValue .rdx :=
    (g1.read (n := 64) (r := 12) (by simp)).trans state.r12
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (mov_r64_r64_effect_step 0x10703e 0x4d 0xe6 (by simp [RexWPrefix]) rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x703e _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7041 (by decide)))
  have g2 : AgreesExcept [.reg 14, .rip] s1 s2 := e2.agrees
  have f2 := after_registers pre f1 run2 ready2 g2 (by simp [Component.Covers]) (by simp)
  have value2 : s2.regValue .r14 = initial.regValue .rdx := by
    have h : s2.regValue .r14 = s1.regValue .r12 := e2.writes
    rw [read1_r12] at h
    exact h
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (xor_r32_r32_rex_effect_step 0x107041 0x45 0xe4 (by simp [RexNoWPrefix]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x7041 _
        (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7044 (by decide)))
  have g3 : AgreesExcept [.reg 12, .flags, .rip] s2 s3 := e3.agrees
  have f3 := after_registers pre f2 run3 ready3 g3 (by simp [Component.Covers]) (by simp)
  have value3 : s3.regValue .r12 = 0 := by
    have h : s3.regValue .r12 = ((s2.regValue .r12).setWidth 32 ^^^ (s2.regValue .r12).setWidth 32).setWidth 64 := e3.writes
    simpa using h
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (xor_r32_r32_effect_step 0x107044 0xed rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x7044 _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7046 (by decide)))
  have g4 : AgreesExcept [.reg 5, .flags, .rip] s3 s4 := e4.agrees
  have f4 := after_registers pre f3 run4 ready4 g4 (by simp [Component.Covers]) (by simp)
  have value4 : s4.regValue .rbp = 0 := by
    have h : s4.regValue .rbp = ((s3.regValue .rbp).setWidth 32 ^^^ (s3.regValue .rbp).setWidth 32).setWidth 64 := e4.writes
    simpa using h
  have read4_rdx : s4.regValue .rdx = 32 :=
    ((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 2) (by simp)).trans state.rdx
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (mov_r64_r64_effect_step 0x107046 0x48 0xd3 (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x7046 _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7049 (by decide)))
  have g5 : AgreesExcept [.reg 3, .rip] s4 s5 := e5.agrees
  have f5 := after_registers pre f4 run5 ready5 g5 (by simp [Component.Covers]) (by simp)
  have value5 : s5.regValue .rbx = 32 := by
    have h : s5.regValue .rbx = s4.regValue .rdx := e5.writes
    rw [read4_rdx] at h
    exact h
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (nop_m_effect_step 0x107049 [] (by simp) (by decide) (.base 0 (.d32 0)) (by decide +kernel) rfl rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x7049 _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7050 (by decide)))
  have g6 : AgreesExcept [.rip] s5 s6 := e6.agrees
  have f6 := after_registers pre f5 run6 ready6 g6 (by simp [Component.Covers]) (by simp)
  have read6_r13 : s6.regValue .r13 = initial.regValue .rdi :=
    (((((g2.trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 13) (by simp)).trans value1
  have read6_r14 : s6.regValue .r14 = initial.regValue .rdx :=
    ((((g3.trans g4).trans g5).trans g6).read (n := 64) (r := 14) (by simp)).trans value2
  have read6_r12 : s6.regValue .r12 = 0 :=
    (((g4.trans g5).trans g6).read (n := 64) (r := 12) (by simp)).trans value3
  have read6_r15 : s6.regValue .r15 = 4 :=
    ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 15) (by simp)).trans state.r15
  have read6_rbp : s6.regValue .rbp = 0 :=
    ((g5.trans g6).read (n := 64) (r := 5) (by simp)).trans value4
  have read6_rbx : s6.regValue .rbx = 32 :=
    (g6.read (n := 64) (r := 3) (by simp)).trans value5
  have read6_rdx : s6.regValue .rdx = 32 :=
    ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 2) (by simp)).trans state.rdx
  exact ⟨s6, f6, ⟨read6_r13, read6_r14, read6_r12, read6_r15, read6_rbp, read6_rbx, read6_rdx⟩, e6.rip⟩

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
