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

theorem count_correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (pre : Pre initial boundary) (state : LengthState initial s boundary) :
    ∃ t, CountState initial t boundary := by
  let s0 := s
  have f0 := state.toStage
  have rip0 := state.rip
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (mov_r32_r32_effect_step 0x107018 0xc1 rfl).advances (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x7018 _
        (by decide +kernel) (by decide +kernel)) rip0
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x701a (by decide)))
  have g1 : AgreesExcept [.reg 1, .rip] s0 s1 := e1.agrees
  have f1 := after_registers pre f0 run1 ready1 g1 (by simp [Component.Covers]) (by simp)
  have value1 : s1.regValue .rcx = 263 := by
    have h : s1.regValue .rcx = ((s0.regValue .rax).setWidth 32).setWidth 64 := e1.writes
    rw [state.rax] at h
    exact h
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (shr_r32_imm8_effect_step 0x10701a 0xe9 6 rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x701a _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x701d (by decide)))
  have g2 : AgreesExcept [.reg 1, .flags, .rip] s1 s2 := e2.agrees
  have f2 := after_registers pre f1 run2 ready2 g2 (by simp [Component.Covers]) (by simp)
  have value2 : s2.regValue .rcx = 4 := by
    have h : s2.regValue .rcx = ((s1.regValue .rcx).setWidth 32 >>> (6 : Nat)).setWidth 64 := e2.writes
    rw [value1] at h
    exact h
  have read2_rax : s2.regValue .rax = 263 :=
    ((g1.trans g2).read (n := 64) (r := 0) (by simp)).trans state.rax
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (and_r32_imm8_effect_step 0x10701d 0xe0 56 rfl rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x701d _
        (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7020 (by decide)))
  have g3 : AgreesExcept [.reg 0, .flags, .rip] s2 s3 := e3.agrees
  have f3 := after_registers pre f2 run3 ready3 g3 (by simp [Component.Covers]) (by simp)
  have value3 : s3.regValue .rax = 0 := by
    have h : s3.regValue .rax = ((s2.regValue .rax).setWidth 32 &&& 56).setWidth 64 := e3.writes
    rw [read2_rax] at h
    exact h
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (cmp_r64_imm8_effect_step 0x107020 0x48 0xf8 1 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x7020 _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7024 (by decide)))
  have g4 : AgreesExcept [.flags, .rip] s3 s4 := e4.agrees
  have f4 := after_registers pre f3 run4 ready4 g4 (by simp [Component.Covers]) (by simp)
  have cf4 : (StatusFlags.ofRFLAGS s4.RFLAGS).CF = true := by
    have h := e4.flags.1
    change (StatusFlags.ofRFLAGS s4.RFLAGS).CF = (cmpSpec (s3.regValue .rax) 1).CF at h
    rw [value3] at h
    exact h
  have read4_rcx : s4.regValue .rcx = 4 :=
    ((g3.trans g4).read (n := 64) (r := 1) (by simp)).trans value2
  have carry4 : s4.RFLAGS.extractLsb' 0 1 = 1 := by
    change s4.RFLAGS.getLsbD 0 = true at cf4
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have he : i = 0 := by omega
    subst i
    simpa using cf4
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (sbb_r64_imm8_effect_step 0x107024 0x48 0xd9 255 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x7024 _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7028 (by decide)))
  have g5 : AgreesExcept [.reg 1, .flags, .rip] s4 s5 := e5.agrees
  have f5 := after_registers pre f4 run5 ready5 g5 (by simp [Component.Covers]) (by simp)
  have value5 : s5.regValue .rcx = 4 := by
    have h : s5.regValue .rcx = (sbbSpec (s4.regValue .rcx) (-1) (s4.RFLAGS.extractLsb' 0 1)).1 := e5.writes
    rw [read4_rcx, carry4] at h
    exact h.trans (by decide +kernel)
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (cmp_r64_imm8_effect_step 0x107028 0x48 0xf9 4 (by simp [RexWPrefix]) rfl rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x7028 _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x702c (by decide)))
  have g6 : AgreesExcept [.flags, .rip] s5 s6 := e6.agrees
  have f6 := after_registers pre f5 run6 ready6 g6 (by simp [Component.Covers]) (by simp)
  have cf6 : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = false := by
    have h := e6.flags.1
    change (StatusFlags.ofRFLAGS s6.RFLAGS).CF = (cmpSpec (s5.regValue .rcx) 4).CF at h
    rw [value5] at h
    exact h
  obtain ⟨s7, run7, ready7, e7⟩ :=
    (mov_r32_imm32_rex_effect_step 0x10702c 0x41 0xbf (by simp [RexNoWPrefix]) (by decide) 4).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x702c _
        (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7032 (by decide)))
  have g7 : AgreesExcept [.reg 15, .rip] s6 s7 := e7.agrees
  have f7 := after_registers pre f6 run7 ready7 g7 (by simp [Component.Covers]) (by simp)
  have value7 : s7.regValue .r15 = 4 := by
    have h : s7.regValue .r15 = 4 := e7.writes
    exact h
  have read7_rcx : s7.regValue .rcx = 4 :=
    ((g6.trans g7).read (n := 64) (r := 1) (by simp)).trans value5
  obtain ⟨s8, run8, ready8, e8⟩ :=
    (cmov_r64_r64_effect_step 0x107032 0x4c 0x42 0xf9 (by simp [RexWPrefix]) (.inl rfl) rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x7032 _
        (by decide +kernel) (by decide +kernel)) e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7036 (by decide)))
  have g8 : AgreesExcept [.reg 15, .rip] s7 s8 := e8.agrees
  have f8 := after_registers pre f7 run8 ready8 g8 (by simp [Component.Covers]) (by simp)
  have value8 : s8.regValue .r15 = 4 := by
    have h : s8.regValue .r15 = (if condHolds 2 (StatusFlags.ofRFLAGS s7.RFLAGS) then s7.regValue .rcx else s7.regValue .r15) := e8.writes
    simpa [value7, read7_rcx] using h
  have read8_rcx : s8.regValue .rcx = 4 :=
    (((g6.trans g7).trans g8).read (n := 64) (r := 1) (by simp)).trans value5
  obtain ⟨s9, run9, ready9, e9⟩ :=
    (test_r64_r64_effect_step 0x107036 0x48 0xc9 (by simp [RexWPrefix]) rfl).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x7036 _
        (by decide +kernel) (by decide +kernel)) e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7039 (by decide)))
  have g9 : AgreesExcept [.flags, .rip] s8 s9 := e9.agrees
  have f9 := after_registers pre f8 run9 ready9 g9 (by simp [Component.Covers]) (by simp)
  have zf9 : (StatusFlags.ofRFLAGS s9.RFLAGS).ZF = false := by
    have h := e9.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s9.RFLAGS).ZF = ((s8.regValue .rcx &&& s8.regValue .rcx) == 0) at h
    rw [read8_rcx] at h
    exact h
  obtain ⟨s10, step10, ready10, raw10⟩ :=
    jcc_rel8_effect_step 0x107039 4 0x58 s9 (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x7039 _
        (by decide +kernel) (by decide +kernel)) ⟨e9.rip, fun _ => by decide +kernel⟩
  have e10 := jccEffect_not_taken
    (show condHolds 4 (StatusFlags.ofRFLAGS s9.RFLAGS) = false from zf9) raw10
  have run10 : Advances boundary 1 s9 s10 := Advances.of_step step10 (.inl (by
    rw [e10.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x703b (by decide))))
  have g10 : AgreesExcept [.rip] s9 s10 := e10.agrees
  have f10 := after_registers pre f9 run10 ready10 g10 (by simp [Component.Covers]) (by simp)
  have read10_rdi : s10.regValue .rdi = initial.regValue .rdi :=
    ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 7) (by simp)).trans state.rdi
  have read10_r12 : s10.regValue .r12 = initial.regValue .rdx :=
    ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 12) (by simp)).trans state.r12
  have read10_rdx : s10.regValue .rdx = 32 :=
    ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 2) (by simp)).trans state.rdx
  have read10_r15 : s10.regValue .r15 = 4 :=
    ((g9.trans g10).read (n := 64) (r := 15) (by simp)).trans value8
  exact ⟨s10, ⟨f10, e10.rip, read10_rdi, read10_r12, read10_rdx, read10_r15⟩⟩

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Prefix
