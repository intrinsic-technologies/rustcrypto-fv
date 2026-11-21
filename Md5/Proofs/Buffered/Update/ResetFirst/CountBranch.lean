import Md5.Proofs.Buffered.Update.ResetFirst.Count

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def remainderBranchEffect (s : RamState) : Effect :=
  { remainderCountEffect s with
    rip := if (.reg 3 : Operand 64).read s >>> 6 = 0 then 0x100740 else 0x10072e
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem remainder_count_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100722)
      Extracted.programImage remainderBranchEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x100722 remainderCountBytes) s :=
    program_text_slice hc 0x722 10 (by decide +kernel)
  obtain ⟨fuel, u, ha, hu, _, he⟩ := remainder_count_prepare boundary hOutside s hs hbytes hp
  have hcu := he.agrees.codeIn (by
    simp [remainderCountEffect, Effect.components, Component.Covers]) hc
  have hz : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      ((.reg 3 : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
  have hnext : (jccEffect 0x10072c 2 4 ((0x12#8).signExtend 64) u).rip =
      (remainderBranchEffect s).rip := by
    simp only [jccEffect, hz, branchEffect, remainderBranchEffect, beq_iff_eq]
    split <;> rfl
  have hne : (remainderBranchEffect s).rip ≠ boundary.rip := by
    unfold remainderBranchEffect
    split
    · exact text_address_ne_return hOutside 0x740 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x72e (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x10072c [0x74, 0x12]) u :=
    program_text_slice hcu 0x72c 2 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x10072c 4 0x12).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨fuel + 1, t, ha.trans hb, ht,
    hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
  · exact ⟨(hag.read (by simp)).trans he.writes.1,
      (hag.read (by simp)).trans he.writes.2⟩
  · apply (he.agrees.trans hag).mono
    simp [remainderCountEffect, remainderBranchEffect, Effect.components]

def alignedBranchEffect (s : RamState) : Effect :=
  { alignedCountEffect s with
    rip := 0x10072e
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem aligned_count_nonzero [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x100779 ∧ 64 ≤ ((.reg 14 : Operand 64).read s).toNat)
      Extracted.programImage alignedBranchEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x100779 alignedCountBytes) s :=
    program_text_slice hc 0x779 10 (by decide +kernel)
  obtain ⟨fuel, u, ha, hu, _, he⟩ := aligned_count_prepare boundary hOutside s hs hbytes hp.1
  have hcu := he.agrees.codeIn (by
    simp [alignedCountEffect, Effect.components, Component.Covers]) hc
  have hnonzero : (.reg 14 : Operand 64).read s >>> 6 ≠ 0 := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hn
    change ((.reg 14 : Operand 64).read s).toNat / 64 = 0 at hn
    have := hp.2
    omega
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have hz := he.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      ((.reg 14 : Operand 64).read s >>> 6 == 0) at hz
    exact hz.trans (beq_eq_false_iff_ne.mpr hnonzero)
  have hcond : condHolds 5 (StatusFlags.ofRFLAGS u.RFLAGS) = true := by
    change (!(StatusFlags.ofRFLAGS u.RFLAGS).ZF) = true
    rw [hz]
    rfl
  have hnext : (jccEffect 0x100783 2 5 ((0xa9#8).signExtend 64) u).rip = 0x10072e := by
    rw [jccEffect, hcond]
    rfl
  have hbranch : CodeIn (codeRange 0x100783 [0x75, 0xa9]) u :=
    program_text_slice hcu 0x783 2 (by decide +kernel)
  have hne : (jccEffect 0x100783 2 5 ((0xa9#8).signExtend 64) u).rip ≠ boundary.rip := by
    rw [hnext]
    exact text_address_ne_return hOutside 0x72e (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x100783 5 0xa9).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩
    hne
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨fuel + 1, t, ha.trans hb, ht,
    hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
  · exact ⟨(hag.read (by simp)).trans he.writes.1,
      (hag.read (by simp)).trans he.writes.2⟩
  · apply (he.agrees.trans hag).mono
    simp [alignedCountEffect, alignedBranchEffect, Effect.components]

end Md5.Proofs.Buffered.ResetFirst
