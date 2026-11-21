import P256.Proofs.Verifying.Wrapper.Guards

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem message_count_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x1031a0)
    (count : s.regValue .r15 = 3) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1031aa ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (cmp_r64_imm8_effect_step 0x1031a0 0x49 0xff 2 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x31a0 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x31a4 (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have condition : condHolds 6 (StatusFlags.ofRFLAGS a.RFLAGS) = false := by
    have cf := ea.flag .CF
    have zf := ea.flag .ZF
    change (StatusFlags.ofRFLAGS a.RFLAGS).CF = (cmpSpec (s.regValue .r15) 2).CF at cf
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (cmpSpec (s.regValue .r15) 2).ZF at zf
    change ((StatusFlags.ofRFLAGS a.RFLAGS).CF || (StatusFlags.ofRFLAGS a.RFLAGS).ZF) = false
    rw [cf,zf,count]
    rfl
  have next : (jccEffect 0x1031a4 6 6 ((0x87 : BitVec 32).signExtend 64) a).rip = 0x1031aa := by
    simp only [jccEffect, condition]
    rfl
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x1031a4 6 0x87).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x31a4 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [next]; exact boundary_ne_program outside (inProgram_of_textOffset 0x31aa (by decide)))
  exact ⟨t, ha.trans ht, rt, et.rip.trans next,
    (fa.trans et.agrees).mono (by simp [jccEffect])⟩

theorem message_pointer_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x1031b2)
    (hptr : s.regValue .rcx ≠ 0) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x1031b7 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (test_r64_r64_effect_step 0x1031b2 0x48 0xc9 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x31b2 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x31b5 (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have he := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .rcx &&& s.regValue .rcx) == 0) at he
    have hptr' : s.regValue .rcx ≠ 0#64 := hptr
    have hz' : (s.regValue .rcx == 0#64) = false := by
      exact beq_eq_false_iff_ne.mpr hptr'
    simp only [BitVec.and_self] at he
    exact he.trans hz'
  have hn : (jccEffect 0x1031b5 2 4 ((0x69 : BitVec 8).signExtend 64) a).rip = 0x1031b7 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨b, hb, rb, eb⟩ := (jcc_rel8_effect_step 0x1031b5 4 0x69).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x31b5 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x31b7 (by decide)))
  exact ⟨b, ha.trans hb, rb, eb.rip.trans hn,
    (fa.trans eb.agrees).mono (by simp [jccEffect])⟩

end P256.Proofs.Verifying.Wrapper
