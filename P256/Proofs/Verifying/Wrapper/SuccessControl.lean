import P256.Proofs.Verifying.Wrapper.ReturnState
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem capacity_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x103210)
    (capacity : 8 ≤ (s.regValue .r13).toNat) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x103216 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (cmp_r64_imm8_effect_step 0x103210 0x49 0xfd 7 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x3210 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x3214 (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have condition : condHolds 6 (StatusFlags.ofRFLAGS a.RFLAGS) = false := by
    have cf := ea.flag .CF
    have zf := ea.flag .ZF
    change (StatusFlags.ofRFLAGS a.RFLAGS).CF = (cmpSpec (s.regValue .r13) 7).CF at cf
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (cmpSpec (s.regValue .r13) 7).ZF at zf
    change ((StatusFlags.ofRFLAGS a.RFLAGS).CF || (StatusFlags.ofRFLAGS a.RFLAGS).ZF) = false
    rw [cf, zf, cmpSpec_ZF]
    change (decide ((s.regValue .r13).toNat < 7) || (s.regValue .r13 == 7)) = false
    have hn : ¬ (s.regValue .r13).toNat < 7 := by omega
    have he : s.regValue .r13 ≠ 7 := by intro h; rw [h] at capacity; contradiction
    simp only [hn, decide_false, Bool.false_or, beq_eq_false_iff_ne]
    exact he
  have next : (jccEffect 0x103214 2 6 ((32 : BitVec 8).signExtend 64) a).rip = 0x103216 := by
    simp only [jccEffect, condition]
    rfl
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel8_effect_step 0x103214 6 32).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x3214 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [next]; exact boundary_ne_program outside (inProgram_of_textOffset 0x3216 (by decide)))
  exact ⟨t, ha.trans ht, rt, et.rip.trans next,
    (fa.trans et.agrees).mono (by simp [jccEffect])⟩

end P256.Proofs.Verifying.Wrapper
