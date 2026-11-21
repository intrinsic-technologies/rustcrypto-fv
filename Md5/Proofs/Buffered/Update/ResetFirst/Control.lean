import Md5.Proofs.Buffered.Update.ResetFirst.Prefix

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def entryEffect (s : RamState) : Effect :=
  { prefixEffect s with
    rip := if ((.reg 14 : Operand 64).read s).toNat < (64 - position s).toNat then
      0x100690 else 0x1006e6
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem entry_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (LoadPre 0x1006d0 (fun s ↦ stackPtr s + 71) 1)
      Extracted.programImage entryEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x1006d0 prefixBytes) s :=
    program_text_slice hc 0x6d0 20 (by decide +kernel)
  obtain ⟨fuel, u, ha, hu, _, he⟩ := entry_prepare boundary hOutside s hs hbytes hp
  have hcu := he.agrees.codeIn (by
    simp [prefixEffect, Effect.components, Component.Covers]) hc
  have hcf : condHolds 2 (StatusFlags.ofRFLAGS u.RFLAGS) =
      decide (((.reg 14 : Operand 64).read s).toNat < (64 - position s).toNat) :=
    he.flags.1
  have hnext : (jccEffect 0x1006e4 2 2 ((0xaa#8).signExtend 64) u).rip =
      (entryEffect s).rip := by
    simp only [jccEffect, hcf, branchEffect, entryEffect, decide_eq_true_eq]
    split <;> rfl
  have hne : (entryEffect s).rip ≠ boundary.rip := by
    unfold entryEffect
    split
    · exact text_address_ne_return hOutside 0x690 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x6e6 (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x1006e4 [0x72, 0xaa]) u :=
    program_text_slice hcu 0x6e4 2 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x1006e4 2 0xaa).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨fuel + 1, t, ha.trans hb, ht,
    hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
  · change (.reg 13 : Operand 64).read t = _ ∧ (.reg 2 : Operand 64).read t = _ ∧
      (.reg 3 : Operand 64).read t = _
    exact ⟨(hag.read (by simp)).trans he.writes.1,
      (hag.read (by simp)).trans he.writes.2.1,
      (hag.read (by simp)).trans he.writes.2.2⟩
  · apply (he.agrees.trans hag).mono
    simp [prefixEffect, entryEffect, Effect.components]

def partialEffect (s : RamState) : Effect :=
  { rip := if (.reg 13 : Operand 64).read s = 0 then 0x100779 else 0x1006ef
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem partial_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1006e6)
      Extracted.programImage partialEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x1006e6 [0x4d, 0x85, 0xed]) s :=
    program_text_slice hc 0x6e6 3 (by decide +kernel)
  have htest : StepEffect (fun s ↦ s.RIP = 0x1006e6)
      (codeRange 0x1006e6 [0x4d, 0x85, 0xed]) (testR64R64Effect 0x1006e6 13 13) :=
    test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨u, ha, hu, he⟩ := htest.advances hs hbytes hp
    (text_address_ne_return hOutside 0x6e9 (by decide +kernel))
  have hcu := he.codeIn (testR64R64Effect_avoids _ _ _ _ _) hc
  have hzf : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      ((.reg 13 : Operand 64).read s == 0) := by
    have hz := he.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((.reg 13 : Operand 64).read s &&& (.reg 13 : Operand 64).read s) == 0) at hz
    rw [BitVec.and_self] at hz
    exact hz
  have hnext : (jccEffect 0x1006e9 6 4 ((0x8a#32).signExtend 64) u).rip =
      (partialEffect s).rip := by
    simp only [jccEffect, hzf, branchEffect, partialEffect, beq_iff_eq]
    split <;> rfl
  have hne : (partialEffect s).rip ≠ boundary.rip := by
    unfold partialEffect
    split
    · exact text_address_ne_return hOutside 0x779 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x6ef (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x1006e9 [0x0f, 0x84, 0x8a, 0x00, 0x00, 0x00]) u :=
    program_text_slice hcu 0x6e9 6 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel32_effect_step 0x1006e9 4 0x8a).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨2, t, ha.trans hb, ht, hag.codeIn (by simp [Component.Covers]) hcu,
    heb.rip.trans hnext, by trivial, by trivial, ?_⟩
  apply (he.agrees.trans hag).mono
  simp [partialEffect, testR64R64Effect, Effect.components]

end Md5.Proofs.Buffered.ResetFirst
