import Md5.Proofs.Buffered.Update.Slices.Entry

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def partialEffect (variant : Bool) (s : RamState) : Effect :=
  { rip := if (.reg 13 : Operand 64).read s = 0 then (pc variant 0x10041d) else (pc variant 0x100377)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem partial_branch {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x10036e))
      Extracted.programImage (partialEffect variant) := by
  cases variant with
  | false =>
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x10036e [0x4d, 0x85, 0xed]) s :=
      program_text_slice hc 0x36e 3 (by decide +kernel)
    have htest : StepEffect (fun s ↦ s.RIP = 0x10036e)
        (codeRange 0x10036e [0x4d, 0x85, 0xed]) (testR64R64Effect 0x10036e 13 13) :=
      test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
    obtain ⟨u, ha, hu, he⟩ := htest.advances hs hbytes hp
      (text_address_ne_return hOutside 0x371 (by decide +kernel))
    have hcu := he.codeIn (testR64R64Effect_avoids _ _ _ _ _) hc
    have hzf : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg 13 : Operand 64).read s == 0) := by
      have hz := he.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        (((.reg 13 : Operand 64).read s &&& (.reg 13 : Operand 64).read s) == 0) at hz
      rw [BitVec.and_self] at hz
      exact hz
    have hnext : (jccEffect 0x100371 6 4 ((0xa6#32).signExtend 64) u).rip =
        (partialEffect false s).rip := by
      simp only [pc, jccEffect, hzf, branchEffect, partialEffect, beq_iff_eq]
      split <;> rfl
    have hne : (partialEffect false s).rip ≠ boundary.rip := by
      unfold partialEffect
      split
      · exact text_address_ne_return hOutside 0x41d (by decide +kernel)
      · exact text_address_ne_return hOutside 0x377 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x100371 [0x0f, 0x84, 0xa6, 0x00, 0x00, 0x00]) u :=
      program_text_slice hcu 0x371 6 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel32_effect_step 0x100371 4 0xa6).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨2, t, ha.trans hb, ht, hag.codeIn (by simp [Component.Covers]) hcu,
      heb.rip.trans hnext, by trivial, by trivial, ?_⟩
    apply (he.agrees.trans hag).mono
    simp [pc, partialEffect, testR64R64Effect, Effect.components]
  | true =>
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x10191e [0x4d, 0x85, 0xed]) s :=
      program_text_slice hc 0x191e 3 (by decide +kernel)
    have htest : StepEffect (fun s ↦ s.RIP = 0x10191e)
        (codeRange 0x10191e [0x4d, 0x85, 0xed]) (testR64R64Effect 0x10191e 13 13) :=
      test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
    obtain ⟨u, ha, hu, he⟩ := htest.advances hs hbytes hp
      (text_address_ne_return hOutside 0x1921 (by decide +kernel))
    have hcu := he.codeIn (testR64R64Effect_avoids _ _ _ _ _) hc
    have hzf : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg 13 : Operand 64).read s == 0) := by
      have hz := he.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        (((.reg 13 : Operand 64).read s &&& (.reg 13 : Operand 64).read s) == 0) at hz
      rw [BitVec.and_self] at hz
      exact hz
    have hnext : (jccEffect 0x101921 6 4 ((0xa6#32).signExtend 64) u).rip =
        (partialEffect true s).rip := by
      simp only [pc, jccEffect, hzf, branchEffect, partialEffect, beq_iff_eq]
      split <;> rfl
    have hne : (partialEffect true s).rip ≠ boundary.rip := by
      unfold partialEffect
      split
      · exact text_address_ne_return hOutside 0x19cd (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1927 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x101921 [0x0f, 0x84, 0xa6, 0x00, 0x00, 0x00]) u :=
      program_text_slice hcu 0x1921 6 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel32_effect_step 0x101921 4 0xa6).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨2, t, ha.trans hb, ht, hag.codeIn (by simp [Component.Covers]) hcu,
      heb.rip.trans hnext, by trivial, by trivial, ?_⟩
    apply (he.agrees.trans hag).mono
    simp [pc, partialEffect, testR64R64Effect, Effect.components]

end Md5.Proofs.Buffered.Update.Slices
