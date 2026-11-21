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

theorem length_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (state : LowScanState initial s boundary) :
    ∃ t, LengthState initial t boundary := by
  let s0 := s
  have f0 := state.toStage
  have rip0 := state.rip
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (mov_r32_imm32_effect_step 0x106ff9 0xb8 (by decide) 263).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x6ff9 _
        (by decide +kernel) (by decide +kernel)) rip0
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6ffe (by decide)))
  have g1 : AgreesExcept [.reg 0, .rip] s0 s1 := e1.agrees
  have f1 := after_registers pre f0 run1 ready1 g1 (by simp [Component.Covers]) (by simp)
  have value1 : s1.regValue .rax = 263 := by
    have h : s1.regValue .rax = 263 := e1.writes
    exact h
  have read1_r8 : s1.regValue .r8 = 0 :=
    (g1.read (n := 64) (r := 8) (by simp)).trans state.r8
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (sub_r64_r64_effect_step 0x106ffe 0x4c 0xc0 (by simp [RexWPrefix]) rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x6ffe _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7001 (by decide)))
  have g2 : AgreesExcept [.reg 0, .flags, .rip] s1 s2 := e2.agrees
  have f2 := after_registers pre f1 run2 ready2 g2 (by simp [Component.Covers]) (by simp)
  have value2 : s2.regValue .rax = 263 := by
    have h : s2.regValue .rax = s1.regValue .rax - s1.regValue .r8 := e2.writes
    rw [value1, read1_r8] at h
    exact h
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (mov_r32_r32_effect_step 0x107001 0xc2 rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x7001 _
        (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7003 (by decide)))
  have g3 : AgreesExcept [.reg 2, .rip] s2 s3 := e3.agrees
  have f3 := after_registers pre f2 run3 ready3 g3 (by simp [Component.Covers]) (by simp)
  have value3 : s3.regValue .rdx = 263 := by
    have h : s3.regValue .rdx = ((s2.regValue .rax).setWidth 32).setWidth 64 := e3.writes
    rw [value2] at h
    exact h
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (shr_r32_imm8_effect_step 0x107003 0xea 3 rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x7003 _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7006 (by decide)))
  have g4 : AgreesExcept [.reg 2, .flags, .rip] s3 s4 := e4.agrees
  have f4 := after_registers pre f3 run4 ready4 g4 (by simp [Component.Covers]) (by simp)
  have value4 : s4.regValue .rdx = 32 := by
    have h : s4.regValue .rdx = ((s3.regValue .rdx).setWidth 32 >>> (3 : Nat)).setWidth 64 := e4.writes
    rw [value3] at h
    exact h
  have read4_rcx : s4.regValue .rcx = 32 :=
    ((((g1.trans g2).trans g3).trans g4).read (n := 64) (r := 1) (by simp)).trans state.rcx
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (cmp_r64_r64_effect_step 0x107006 0x48 0xd1 (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x7006 _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7009 (by decide)))
  have g5 : AgreesExcept [.flags, .rip] s4 s5 := e5.agrees
  have f5 := after_registers pre f4 run5 ready5 g5 (by simp [Component.Covers]) (by simp)
  have cf5 : (StatusFlags.ofRFLAGS s5.RFLAGS).CF = false := by
    have h := e5.flags.1
    change (StatusFlags.ofRFLAGS s5.RFLAGS).CF = (cmpSpec (s4.regValue .rcx) (s4.regValue .rdx)).CF at h
    rw [read4_rcx, value4] at h
    exact h
  obtain ⟨s6, step6, ready6, raw6⟩ :=
    jcc_rel32_effect_step 0x107009 2 0x93 s5 (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x7009 _
        (by decide +kernel) (by decide +kernel)) ⟨e5.rip, fun _ => by decide +kernel⟩
  have e6 := jccEffect_not_taken
    (show condHolds 2 (StatusFlags.ofRFLAGS s5.RFLAGS) = false from cf5) raw6
  have run6 : Advances boundary 1 s5 s6 := Advances.of_step step6 (.inl (by
    rw [e6.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x700f (by decide))))
  have g6 : AgreesExcept [.rip] s5 s6 := e6.agrees
  have f6 := after_registers pre f5 run6 ready6 g6 (by simp [Component.Covers]) (by simp)
  have read6_rdx : s6.regValue .rdx = 32 :=
    ((g5.trans g6).read (n := 64) (r := 2) (by simp)).trans value4
  obtain ⟨s7, run7, ready7, e7⟩ :=
    (test_r64_r64_effect_step 0x10700f 0x48 0xd2 (by simp [RexWPrefix]) rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x700f _
        (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7012 (by decide)))
  have g7 : AgreesExcept [.flags, .rip] s6 s7 := e7.agrees
  have f7 := after_registers pre f6 run7 ready7 g7 (by simp [Component.Covers]) (by simp)
  have zf7 : (StatusFlags.ofRFLAGS s7.RFLAGS).ZF = false := by
    have h := e7.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s7.RFLAGS).ZF = ((s6.regValue .rdx &&& s6.regValue .rdx) == 0) at h
    rw [read6_rdx] at h
    exact h
  obtain ⟨s8, step8, ready8, raw8⟩ :=
    jcc_rel32_effect_step 0x107012 4 0x7b s7 (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x7012 _
        (by decide +kernel) (by decide +kernel)) ⟨e7.rip, fun _ => by decide +kernel⟩
  have e8 := jccEffect_not_taken
    (show condHolds 4 (StatusFlags.ofRFLAGS s7.RFLAGS) = false from zf7) raw8
  have run8 : Advances boundary 1 s7 s8 := Advances.of_step step8 (.inl (by
    rw [e8.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7018 (by decide))))
  have g8 : AgreesExcept [.rip] s7 s8 := e8.agrees
  have f8 := after_registers pre f7 run8 ready8 g8 (by simp [Component.Covers]) (by simp)
  have read8_rdi : s8.regValue .rdi = initial.regValue .rdi :=
    ((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).read (n := 64) (r := 7) (by simp)).trans state.rdi
  have read8_r12 : s8.regValue .r12 = initial.regValue .rdx :=
    ((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).read (n := 64) (r := 12) (by simp)).trans state.r12
  have read8_rax : s8.regValue .rax = 263 :=
    ((((((g3.trans g4).trans g5).trans g6).trans g7).trans g8).read (n := 64) (r := 0) (by simp)).trans value2
  have read8_rdx : s8.regValue .rdx = 32 :=
    ((((g5.trans g6).trans g7).trans g8).read (n := 64) (r := 2) (by simp)).trans value4
  exact ⟨s8, ⟨f8, e8.rip, read8_rdi, read8_r12, read8_rax, read8_rdx⟩⟩

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
