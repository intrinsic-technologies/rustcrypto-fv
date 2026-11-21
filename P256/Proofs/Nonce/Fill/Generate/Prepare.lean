import P256.Proofs.Nonce.Fill.Generate.Interface
import P256.Proofs.Common.Memory.Copy.RegisterOps.Cmov
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Generate

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.Common.Instructions

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : State}
    (pre : Pre initial boundary orderAddress original)
    (input : Loop initial s orderAddress state) :
    ∃ t, Advances boundary 7 s t ∧ Ready initial t orderAddress state := by
  obtain ⟨a, ra, readyA, ea⟩ :=
    (mov_r64_m64_effect_step 0x1073a0 0x4c (by simp [RexWPrefix]) 6
      (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl).advances
      (readyToStep input.machine input.bindingsSupported)
      (programText_slice (programLoaded_codeIn input.loaded) 0x73a0 _ (by decide) (by decide +kernel))
      ⟨input.rip, stack_readable pre input.toFrame (offset := 40) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73a5 (by decide)))
  have aa : AgreesExcept [.reg 14, .rip] s a := ea.agrees
  have fa := input.toFrame.after_registers readyA aa (by simp [Component.Covers]) (by simp)
  have r14 : a.regValue .r14 = initial.regValue .rsi := by
    have h := ea.writes
    change a.regValue .r14 = memLoad s.external (stackPtr s + 40) 64 at h
    rw [input.rsp] at h
    exact h.trans input.outputSlot
  obtain ⟨b, rb, readyB, eb⟩ :=
    (mov_r64_m64_effect_step 0x1073a5 0x48 (by simp [RexWPrefix]) 5
      (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn fa.loaded) 0x73a5 _ (by decide) (by decide +kernel))
      ⟨ea.rip, stack_readable pre fa (offset := 48) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73aa (by decide)))
  have ab : AgreesExcept [.reg 5, .rip] a b := eb.agrees
  have fb := fa.after_registers readyB ab (by simp [Component.Covers]) (by simp)
  have rbp : b.regValue .rbp = 32 := by
    have h := eb.writes
    change b.regValue .rbp = memLoad a.external (stackPtr a + 48) 64 at h
    rw [fa.rsp, aa.external (by simp [Component.Covers])] at h
    exact h.trans input.lengthSlot
  obtain ⟨c, rc, readyC, ec⟩ :=
    (nop_m_effect_step 0x1073aa [0x66] (by decide) (by decide)
      (.sib 0 (some 0) 0 (.d8 0)) (by decide) rfl rfl).advances readyB
      (programText_slice (programLoaded_codeIn fb.loaded) 0x73aa _ (by decide) (by decide +kernel)) eb.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73b0 (by decide)))
  have ac : AgreesExcept [.rip] b c := ec.agrees
  have fc := fb.after_registers readyC ac (by simp [Component.Covers]) (by simp)
  obtain ⟨d, rd, readyD, ed⟩ :=
    (cmp_r64_imm8_effect_step 0x1073b0 0x48 0xfd 32
      (by simp [RexWPrefix]) rfl rfl).advances readyC
      (programText_slice (programLoaded_codeIn fc.loaded) 0x73b0 _ (by decide) (by decide +kernel)) ec.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73b4 (by decide)))
  have ad : AgreesExcept [.flags, .rip] c d := ed.agrees
  have fd := fc.after_registers readyD ad (by simp [Component.Covers]) (by simp)
  obtain ⟨e, re, readyE, ee⟩ :=
    (mov_r32_imm32_rex_effect_step 0x1073b4 0x41 0xbf
      (by simp [RexNoWPrefix]) (by decide) 32).advances readyD
      (programText_slice (programLoaded_codeIn fd.loaded) 0x73b4 _ (by decide) (by decide +kernel)) ed.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73ba (by decide)))
  have ae : AgreesExcept [.reg 15, .rip] d e := ee.agrees
  have fe := fd.after_registers readyE ae (by simp [Component.Covers]) (by simp)
  have rbpE : e.regValue .rbp = 32 :=
    ((ac.trans ad).trans ae).read (n := 64) (r := 5) (by simp) |>.trans rbp
  have r15E : e.regValue .r15 = 32 := ee.writes
  obtain ⟨f, rf, readyF, ef⟩ :=
    (cmov_r64_r64_effect_step 0x1073ba 0x4c 0x42 0xfd
      (by simp [RexWPrefix]) (Or.inl rfl) rfl).advances readyE
      (programText_slice (programLoaded_codeIn fe.loaded) 0x73ba _ (by decide) (by decide +kernel)) ee.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73be (by decide)))
  have af : AgreesExcept [.reg 15, .rip] e f := ef.agrees
  have ff := fe.after_registers readyF af (by simp [Component.Covers]) (by simp)
  have r15F : f.regValue .r15 = 32 := by
    have h := ef.writes
    change f.regValue .r15 = (if condHolds 2 (StatusFlags.ofRFLAGS e.RFLAGS) then
      e.regValue .rbp else e.regValue .r15) at h
    simpa only [rbpE, r15E, ite_self] using h
  obtain ⟨t, rt, readyT, et⟩ :=
    (lea_r64_effect_step 0x1073be 0x4f (by simp [RexWPrefix]) 5
      (.sib 14 (some 15) 0 .none) (by decide) rfl rfl).advances readyF
      (programText_slice (programLoaded_codeIn ff.loaded) 0x73be _ (by decide) (by decide +kernel)) ef.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73c2 (by decide)))
  have agT : AgreesExcept [.reg 13, .rip] f t := et.agrees
  have agrees : AgreesExcept [.reg 14, .reg 5, .reg 15, .reg 13, .flags, .rip] s t :=
    (((((aa.trans ab).trans ac).trans ad).trans ae).trans af |>.trans agT).mono (by simp)
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨t, (((((ra.trans rb).trans rc).trans rd).trans re).trans rf).trans rt,
    input.toFrame.after_registers readyT agrees (by simp [Component.Covers]) (by simp),
    input.toSlots.of_memory_eq memory, ?_, et.rip, ?_, ?_⟩
  · exact ⟨(agrees.read (n := 64) (r := 12) (by simp)).trans input.r12,
      (agrees.read (n := 64) (r := 3) (by simp)).trans input.rbx,
      ((af.trans agT).read (n := 64) (r := 5) (by simp)).trans rbpE,
      (((((ab.trans ac).trans ad).trans ae).trans af |>.trans agT).read
        (n := 64) (r := 14) (by simp)).trans r14,
      (agT.read (n := 64) (r := 15) (by simp)).trans r15F⟩
  · exact (agrees.read (n := 64) (r := 7) (by simp)).trans input.rdi
  · simpa only [GeneratorAt, DrbgAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, memory]
      using input.generator

end P256.Proofs.Nonce.Fill.Generate
