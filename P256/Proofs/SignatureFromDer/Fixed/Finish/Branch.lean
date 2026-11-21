import P256.Proofs.SignatureFromDer.Fixed.Interface
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Select.TestAl
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.SignatureFromDer.Fixed.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem zero_branch [Bindings] {t : RamState} {boundary : ReturnBoundary} {zero : Bool}
    (second : Bool) (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (outside : ¬ InProgram boundary.rip)
    (rip : t.RIP = if second then 0x109c53 else 0x109c05)
    (rax : t.regValue .rax = if zero then 1 else 0) :
    ∃ u, Advances boundary 2 t u ∧ ReadyToStep u ∧
      u.RIP = (if zero then 0x109c57 else if second then 0x109c74 else 0x109c09) ∧
      AgreesExcept [.flags, .rip] t u := by
  let offset : Nat := if second then 0x9c53 else 0x9c05
  let p : BitVec 64 := Extracted.textAddress + BitVec.ofNat 64 offset
  let cc : BitVec 4 := if second then 4 else 5
  let disp : BitVec 8 := if second then 0x1d else 0x4e
  have hrip : t.RIP = p := by cases second <;> exact rip
  have code : CodeIn (codeRange p [0x84, 0xc0]) t :=
    programText_slice (programLoaded_codeIn loaded) offset _
      (by cases second <;> decide) (by cases second <;> decide +kernel)
  obtain ⟨a, ha, ra, ea⟩ := (P256.Proofs.Common.Field.test_al_al_effect_step p).advances
    ready code hrip (by
      cases second
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9c07 (by decide))
      · exact boundary_ne_program outside (inProgram_of_textOffset 0x9c55 (by decide)))
  have fa : AgreesExcept [.flags, .rip] t a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have zf : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = !zero := by
    have hz := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((t.regValue .rax).setWidth 8 == 0) at hz
    rw [hz, rax]
    cases zero <;> decide +kernel
  have cond : condHolds cc (StatusFlags.ofRFLAGS a.RFLAGS) = if second then !zero else zero := by
    cases second
    · change (!(StatusFlags.ofRFLAGS a.RFLAGS).ZF) = zero
      rw [zf, Bool.not_not]
    · exact zf
  have next : (jccEffect (p + 2) 2 cc (disp.signExtend 64) a).rip =
      if zero then 0x109c57 else if second then 0x109c74 else 0x109c09 := by
    simp only [jccEffect, cond]
    cases second <;> cases zero <;> rfl
  have code' : CodeIn (codeRange (p + 2) ((jccOpcode8 cc :: immBytes 8 disp))) a := by
    have h := programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      (offset + 2) ((jccOpcode8 cc :: immBytes 8 disp))
      (by cases second <;> decide) (by cases second <;> decide +kernel)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, p] using h
  obtain ⟨u, hu, ru, eu⟩ := (jcc_rel8_effect_step (p + 2) cc disp).advances ra code'
    ⟨ea.rip, by intro; cases second <;> decide⟩
    (by rw [next]; cases zero
        · cases second
          · exact boundary_ne_program outside (inProgram_of_textOffset 0x9c09 (by decide))
          · exact boundary_ne_program outside (inProgram_of_textOffset 0x9c74 (by decide))
        · exact boundary_ne_program outside (inProgram_of_textOffset 0x9c57 (by decide)))
  have fu : AgreesExcept [.rip] a u := eu.agrees
  exact ⟨u, ha.trans hu, ru, eu.rip.trans next, (fa.trans fu).mono (by simp)⟩

end P256.Proofs.SignatureFromDer.Fixed.Finish
