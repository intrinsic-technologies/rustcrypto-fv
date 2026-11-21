import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Instructions
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Loop
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.SecretKeyFromBytes.Scalar.Equal

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem start_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) : ∃ t, LoopState s t boundary 0 := by
  have st0 : Stage s s boundary := ⟨⟨0, by simp⟩, pre.ready, .refl _ _⟩
  have code0 := programLoaded_codeIn pre.loaded
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (cmp_r64_r64_effect_step 0x119270 0x48 0xce (by simp [RexWPrefix]) rfl).advances
      pre.ready (programText_slice code0 0x19270 [0x48,0x39,0xce] (by decide +kernel) rfl)
      pre.rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19273 (by decide)))
  change (cmpR64R64Effect 0x119270 6 1 s).Holds s s1 at e1
  have st1 := st0.extend run1 ready1 e1 (by simp [clobbers])
  have hz1 : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = true := by
    have h := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = (cmpSpec (s.regValue .rsi) (s.regValue .rcx)).ZF at h
    rw [pre.leftLength, pre.rightLength] at h
    exact h
  have br1 : (jccEffect 0x119273 2 5 ((0x45 : BitVec 8).signExtend 64) s1).rip = 0x119275 := by
    simp [jccEffect, branchEffect, condHolds, hz1]
  obtain ⟨s2, run2, ready2, e2⟩ := (jcc_rel8_effect_step 0x119273 5 0x45).advances ready1
    (programText_slice (programLoaded_codeIn (st1.loaded pre.loaded)) 0x19273 [0x75,0x45]
      (by decide +kernel) rfl) ⟨e1.rip, fun _ => by decide +kernel⟩
    (by rw [br1]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19275 (by decide)))
  have st2 := st1.extend run2 ready2 e2 (by simp [jccEffect, clobbers])
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (test_r64_r64_effect_step 0x119275 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances ready2
    (programText_slice (programLoaded_codeIn (st2.loaded pre.loaded)) 0x19275 [0x48,0x85,0xf6]
      (by decide +kernel) rfl) (e2.rip.trans br1)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19278 (by decide)))
  change (testR64R64Effect 0x119275 6 6 s2).Holds s2 s3 at e3
  have st3 := st2.extend run3 ready3 e3 (by simp [clobbers])
  have length2 : s2.regValue .rsi = 4 :=
    (st2.agrees.read (n := 64) (r := 6) (by simp [clobbers])).trans pre.leftLength
  have hz3 : (StatusFlags.ofRFLAGS s3.RFLAGS).ZF = false := by
    have h := e3.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s3.RFLAGS).ZF = ((s2.regValue .rsi &&& s2.regValue .rsi) == 0) at h
    rw [length2] at h
    exact h
  have br3 : (jccEffect 0x119278 2 4 ((0x4f : BitVec 8).signExtend 64) s3).rip = 0x11927a := by
    simp [jccEffect, branchEffect, condHolds, hz3]
  obtain ⟨s4, run4, ready4, e4⟩ := (jcc_rel8_effect_step 0x119278 4 0x4f).advances ready3
    (programText_slice (programLoaded_codeIn (st3.loaded pre.loaded)) 0x19278 [0x74,0x4f]
      (by decide +kernel) rfl) ⟨e3.rip, fun _ => by decide +kernel⟩
    (by rw [br3]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1927a (by decide)))
  have st4 := st3.extend run4 ready4 e4 (by simp [jccEffect, clobbers])
  obtain ⟨s5, run5, ready5, e5⟩ :=
    (mov_r16_imm16_effect_step 0x11927a 0xb8 (by decide) 1).advances ready4
    (programText_slice (programLoaded_codeIn (st4.loaded pre.loaded)) 0x1927a [0x66,0xb8,1,0]
      (by decide +kernel) rfl) (e4.rip.trans br3)
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1927e (by decide)))
  change (movR16Imm16Effect 0x11927a 0 1 s4).Holds s4 s5 at e5
  have st5 := st4.extend run5 ready5 e5 (by simp [movR16Imm16Effect_components, clobbers])
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (xor_r32_r32_rex_effect_step 0x11927e 0x45 0xc0 (by simp [RexNoWPrefix]) rfl).advances ready5
    (programText_slice (programLoaded_codeIn (st5.loaded pre.loaded)) 0x1927e [0x45,0x31,0xc0]
      (by decide +kernel) rfl) e5.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19281 (by decide)))
  change (xorR32R32Effect 0x11927e 3 8 8 s5).Holds s5 s6 at e6
  have st6 := st5.extend run6 ready6 e6 (by simp [clobbers])
  obtain ⟨s7, run7, ready7, e7⟩ :=
    (xor_r32_r32_effect_step 0x119281 0xc9 rfl).advances ready6
    (programText_slice (programLoaded_codeIn (st6.loaded pre.loaded)) 0x19281 [0x31,0xc9]
      (by decide +kernel) rfl) e6.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19283 (by decide)))
  change (xorR32R32Effect 0x119281 2 1 1 s6).Holds s6 s7 at e7
  have st7 := st6.extend run7 ready7 e7 (by simp [clobbers])
  obtain ⟨s8, run8, ready8, e8⟩ := (equality_nop_effect_step 0x119283).advances ready7
    (programText_slice (programLoaded_codeIn (st7.loaded pre.loaded)) 0x19283
      [0x66,0x66,0x66,0x66,0x2e,0x0f,0x1f,0x84,0,0,0,0,0]
      (by decide +kernel) rfl) e7.rip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x19290 (by decide)))
  have st8 := st7.extend run8 ready8 e8 (by simp [clobbers])
  have hag : AgreesExcept [.reg 0, .reg 1, .reg 8, .flags, .rip] s s8 :=
    (((((((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees).trans
      e6.agrees).trans e7.agrees).trans e8.agrees).mono
      (by simp [jccEffect, movR16Imm16Effect_components])
  have al5 : (s5.regValue .rax).setWidth 8 = 1 := by
    have hw : s5.regValue .rax = mergeGPR 16 1 (s4.regValue .rax) := e5.writes
    rw [hw, mergeGPR16_low (by decide)]
    rfl
  have r86 : s6.regValue .r8 = 0 := by
    have hw : s6.regValue .r8 = (((Operand.reg 8 : Operand 32).read s5) ^^^
      ((Operand.reg 8 : Operand 32).read s5)).setWidth 64 := e6.writes
    simpa using hw
  have rcx7 : s7.regValue .rcx = 0 := by
    have hw : s7.regValue .rcx = (((Operand.reg 1 : Operand 32).read s6) ^^^
      ((Operand.reg 1 : Operand 32).read s6)).setWidth 64 := e7.writes
    simpa using hw
  refine ⟨s8, st8, e8.rip, ?_, ?_, ?_, ?_⟩
  · exact hag.read (n := 64) (r := 2) (by simp)
  · exact (e8.agrees.read (n := 64) (r := 1) (by simp)).trans rcx7
  · exact ((e7.agrees.trans e8.agrees).read (n := 64) (r := 8) (by simp)).trans r86
  · exact (((e6.agrees.trans e7.agrees).trans e8.agrees).read (n := 8) (r := 0)
      (by simp)).trans al5

end P256.Proofs.SecretKeyFromBytes.Scalar.Equal
