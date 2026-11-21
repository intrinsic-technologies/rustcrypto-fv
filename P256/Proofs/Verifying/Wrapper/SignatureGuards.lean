import P256.Proofs.Verifying.Wrapper.Guards

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem signature_count_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x103118)
    (count : s.regValue .r15 = 3) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x103122 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (cmp_r64_imm8_effect_step 0x103118 0x49 0xff 1 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x3118 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x311c (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have condition : condHolds 4 (StatusFlags.ofRFLAGS a.RFLAGS) = false := by
    have zf := ea.flag .ZF
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (cmpSpec (s.regValue .r15) 1).ZF at zf
    rw [count, cmpSpec_ZF] at zf
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false
    rw [zf]
    rfl
  have next : (jccEffect 0x10311c 6 4 ((0x10f : BitVec 32).signExtend 64) a).rip = 0x103122 := by
    simp only [jccEffect, condition]
    rfl
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x10311c 4 0x10f).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x311c _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [next]; exact boundary_ne_program outside (inProgram_of_textOffset 0x3122 (by decide)))
  exact ⟨t, ha.trans ht, rt, et.rip.trans next,
    (fa.trans et.agrees).mono (by simp [jccEffect])⟩

theorem signature_pointer_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x10312a)
    (hptr : s.regValue .rsi ≠ 0) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x103133 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (test_r64_r64_effect_step 0x10312a 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x312a _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x312d (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have he := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .rsi &&& s.regValue .rsi) == 0) at he
    have hptr' : s.regValue .rsi ≠ 0#64 := hptr
    have hz' : (s.regValue .rsi == 0#64) = false := by
      exact beq_eq_false_iff_ne.mpr hptr'
    simp only [BitVec.and_self] at he
    exact he.trans hz'
  have hn : (jccEffect 0x10312d 6 4 ((0xed : BitVec 32).signExtend 64) a).rip = 0x103133 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨b, hb, rb, eb⟩ := (jcc_rel32_effect_step 0x10312d 4 0xed).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x312d _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x3133 (by decide)))
  exact ⟨b, ha.trans hb, rb, eb.rip.trans hn,
    (fa.trans eb.agrees).mono (by simp [jccEffect])⟩

end P256.Proofs.Verifying.Wrapper
