import P256.Proofs.Generate.Wrapper.Tail.Output
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem add_length [Bindings] {initial s : RamState} {input : ByteArray}
    (state : OutputState initial s input) (rip : s.RIP = 0x106ec8)
    (outside : ¬ InProgram (returnBoundary initial).rip) (count : s.regValue .r15 = 65) :
    ∃ t, OutputState initial t input ∧ t.RIP = 0x106ecc ∧
      t.regValue .r15 = 97 ∧ AgreesExcept [.reg 15,.flags,.rip] s t := by
  obtain ⟨t,run,ready,effect⟩ := (add_r64_imm8_effect_step 0x106ec8 0x49 0xc7 32
    (by simp [RexWPrefix]) (by decide) (by decide)).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x6ec8 _ (by decide) (by decide +kernel))
    rip (boundary_ne_program outside (inProgram_of_textOffset 0x6ecc (by decide)))
  have g : AgreesExcept [.reg 15,.flags,.rip] s t := effect.agrees
  refine ⟨t,state.after_registers run ready g (by simp [Component.Covers]) (by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp),effect.rip,?_,g⟩
  have h : t.regValue .r15 = s.regValue .r15 + 32 := effect.writes
  rw [h,count]
  rfl

theorem success_branch [Bindings] {initial s : RamState} {input : ByteArray}
    (state : OutputState initial s input) (rip : s.RIP = 0x106ecc)
    (outside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, OutputState initial t input ∧ t.RIP = 0x106ed3 ∧
      AgreesExcept [.reg 1,.flags,.rip] s t := by
  obtain ⟨a,ha,ra,ea⟩ := (xor_r32_r32_effect_step 0x106ecc 0xc9 (by decide)).advances
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x6ecc _ (by decide) (by decide +kernel))
    rip (boundary_ne_program outside (inProgram_of_textOffset 0x6ece (by decide)))
  have fa : AgreesExcept [.reg 1,.flags,.rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have cx : a.regValue .rcx = 0 := by
    have h := ea.writes
    change a.regValue .rcx = (((Operand.reg 1 : Operand 32).read s) ^^^
      ((Operand.reg 1 : Operand 32).read s)).setWidth 64 at h
    simpa only [BitVec.xor_self,BitVec.setWidth_zero,BitVec.ofNat_eq_ofNat] using h
  obtain ⟨b,hb,rb,eb⟩ := (cmp_r32_imm8_effect_step 0x106ece 0xf9 1
    (by decide) (by decide)).advances ra
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma)
      0x6ece _ (by decide) (by decide +kernel)) ea.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x6ed1 (by decide)))
  have fb : AgreesExcept [.flags,.rip] a b := eb.agrees
  have mb := (fb.external (by simp [Component.Covers])).trans ma
  have zf : (StatusFlags.ofRFLAGS b.RFLAGS).ZF = false := by
    have h := eb.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS b.RFLAGS).ZF = (cmpSpec ((a.regValue .rcx).setWidth 32) 1).ZF at h
    rw [h,cx]
    decide +kernel
  obtain ⟨t,step,ready,raw⟩ := jcc_rel8_effect_step 0x106ed1 4 0xb b rb
    (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq mb)
      0x6ed1 _ (by decide) (by decide +kernel)) ⟨eb.rip,by intro; decide⟩
  have effect := jccEffect_not_taken (show condHolds 4 (StatusFlags.ofRFLAGS b.RFLAGS) = false from zf) raw
  have run : Advances (returnBoundary initial) 1 b t := Advances.of_step step (.inl (by
    rw [effect.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6ed3 (by decide))))
  have ag : AgreesExcept [.reg 1,.flags,.rip] s t := ((fa.trans fb).trans effect.agrees).mono (by simp)
  exact ⟨t,state.after_registers ((ha.trans hb).trans run) ready ag
    (by simp [Component.Covers]) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (by simp),effect.rip,ag⟩

end P256.Proofs.Generate.Wrapper.Finish
