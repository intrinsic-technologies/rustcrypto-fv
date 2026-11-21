import P256.Proofs.Nonce.Fill.Generate.Interface
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Generate

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : State}
    (pre : Pre initial boundary orderAddress original)
    (input : Copied initial s orderAddress state) :
    ∃ t, Advances boundary 4 s t ∧ Generated initial t orderAddress state := by
  obtain ⟨a, ra, readyA, ea⟩ :=
    (mov_r64_m64_effect_step 0x1073d2 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl).advances
      (readyToStep input.machine input.bindingsSupported)
      (programText_slice (programLoaded_codeIn input.loaded) 0x73d2 _ (by decide) (by decide +kernel))
      ⟨input.rip, stack_readable pre input.toFrame (offset := 64) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73d7 (by decide)))
  have aa : AgreesExcept [.reg 7, .rip] s a := ea.agrees
  have fa := input.toFrame.after_registers readyA aa (by simp [Component.Covers]) (by simp)
  have rdi : a.regValue .rdi = initial.regValue .rdi + 8 := by
    have h := ea.writes
    change a.regValue .rdi = memLoad s.external (stackPtr s + 64) 64 at h
    rw [input.rsp] at h
    exact h.trans input.statePointerSlot
  obtain ⟨b, rb, readyB, eb⟩ :=
    (mov_r64_r64_effect_step 0x1073d7 0x4d 0xee (by simp [RexWPrefix]) rfl).advances readyA
      (programText_slice (programLoaded_codeIn fa.loaded) 0x73d7 _ (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73da (by decide)))
  have ab : AgreesExcept [.reg 14, .rip] a b := eb.agrees
  have fb := fa.after_registers readyB ab (by simp [Component.Covers]) (by simp)
  obtain ⟨c, rc, readyC, ec⟩ :=
    (sub_r64_r64_effect_step 0x1073da 0x4c 0xfd (by simp [RexWPrefix]) rfl).advances readyB
      (programText_slice (programLoaded_codeIn fb.loaded) 0x73da _ (by decide) (by decide +kernel)) eb.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73dd (by decide)))
  have ac : AgreesExcept [.reg 5, .flags, .rip] b c := ec.agrees
  have fc := fb.after_registers readyC ac (by simp [Component.Covers]) (by simp)
  have bp : b.regValue .rbp = 32 :=
    ((aa.trans ab).read (n := 64) (r := 5) (by simp)).trans input.rbp
  have r15 : b.regValue .r15 = 32 :=
    ((aa.trans ab).read (n := 64) (r := 15) (by simp)).trans input.r15
  have zf : (StatusFlags.ofRFLAGS c.RFLAGS).ZF = true := by
    have h := ec.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS c.RFLAGS).ZF = (subSpec (b.regValue .rbp) (b.regValue .r15)).2.ZF at h
    rw [bp, r15] at h
    exact h
  have next : (jccEffect 0x1073dd 2 5 ((0xd1 : BitVec 8).signExtend 64) c).rip = 0x1073df := by
    simp [jccEffect, branchEffect, condHolds, zf]
  obtain ⟨t, rt, readyT, et⟩ := (jcc_rel8_effect_step 0x1073dd 5 0xd1).advances readyC
    (programText_slice (programLoaded_codeIn fc.loaded) 0x73dd _ (by decide) (by decide +kernel))
    ⟨ec.rip, by intro; decide +kernel⟩
    (by rw [next]; exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73df (by decide)))
  have agT : AgreesExcept [.rip] c t := et.agrees
  have agrees : AgreesExcept [.reg 7, .reg 14, .reg 5, .flags, .rip] s t :=
    (((aa.trans ab).trans ac).trans agT).mono (by simp)
  have memory := agrees.external (by simp [Component.Covers])
  refine ⟨t, ((ra.trans rb).trans rc).trans rt,
    input.toFrame.after_registers readyT agrees (by simp [Component.Covers]) (by simp),
    input.toSlots.of_memory_eq memory, et.rip.trans next,
    (((ab.trans ac).trans agT).read (n := 64) (r := 7) (by simp)).trans rdi, ?_, ?_⟩
  · simpa only [GeneratorAt, DrbgAt, P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At, memory]
      using input.generator
  · simpa only [memory] using input.output

end P256.Proofs.Nonce.Fill.Generate
