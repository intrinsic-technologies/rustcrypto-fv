import Md5.Proofs.Buffered.Update.Slices.Full.Machine.Count

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def remainderBranchEffect (variant : Bool) (s : RamState) : Effect :=
  { remainderCountEffect variant s with
    rip := if (.reg 5 : Operand 64).read s >>> 6 = 0 then (pc variant 0x1003dd) else (pc variant 0x1003c5)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem remainder_count_branch {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc variant 0x1003b9))
      Extracted.programImage (remainderBranchEffect variant) := by
  cases variant with
  | false =>
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x1003b9 remainderCountBytes) s :=
      program_text_slice hc 0x3b9 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := remainder_count_prepare (variant := false) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [pc, remainderCountEffect, Effect.components, Component.Covers]) hc
    have hz : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg 5 : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
    have hnext : (jccEffect 0x1003c3 2 4 ((0x18#8).signExtend 64) u).rip =
        (remainderBranchEffect false s).rip := by
      simp only [pc, jccEffect, hz, branchEffect, remainderBranchEffect, beq_iff_eq]
      split <;> rfl
    have hne : (remainderBranchEffect false s).rip ≠ boundary.rip := by
      unfold remainderBranchEffect
      split
      · exact text_address_ne_return hOutside 0x3dd (by decide +kernel)
      · exact text_address_ne_return hOutside 0x3c5 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x1003c3 [0x74, 0x18]) u :=
      program_text_slice hcu 0x3c3 2 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x1003c3 4 0x18).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2⟩
    · apply (he.agrees.trans hag).mono
      simp [pc, remainderCountEffect, remainderBranchEffect, Effect.components]
  | true =>
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x101969 remainderCountBytes) s :=
      program_text_slice hc 0x1969 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := remainder_count_prepare (variant := true) boundary hOutside s hs hbytes hp
    have hcu := he.agrees.codeIn (by
      simp [pc, remainderCountEffect, Effect.components, Component.Covers]) hc
    have hz : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
        ((.reg 5 : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
    have hnext : (jccEffect 0x101973 2 4 ((0x18#8).signExtend 64) u).rip =
        (remainderBranchEffect true s).rip := by
      simp only [pc, jccEffect, hz, branchEffect, remainderBranchEffect, beq_iff_eq]
      split <;> rfl
    have hne : (remainderBranchEffect true s).rip ≠ boundary.rip := by
      unfold remainderBranchEffect
      split
      · exact text_address_ne_return hOutside 0x198d (by decide +kernel)
      · exact text_address_ne_return hOutside 0x1975 (by decide +kernel)
    have hbranch : CodeIn (codeRange 0x101973 [0x74, 0x18]) u :=
      program_text_slice hcu 0x1973 2 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x101973 4 0x18).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2⟩
    · apply (he.agrees.trans hag).mono
      simp [pc, remainderCountEffect, remainderBranchEffect, Effect.components]

def alignedBranchEffect (variant : Bool) (s : RamState) : Effect :=
  { alignedCountEffect variant s with
    rip := (pc variant 0x1003c5)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem aligned_count_nonzero {variant : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = (pc variant 0x10041d) ∧ 64 ≤ ((.reg 3 : Operand 64).read s).toNat)
      Extracted.programImage (alignedBranchEffect variant) := by
  cases variant with
  | false =>
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x10041d alignedCountBytes) s :=
      program_text_slice hc 0x41d 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := aligned_count_prepare (variant := false) boundary hOutside s hs hbytes hp.1
    have hcu := he.agrees.codeIn (by
      simp [pc, alignedCountEffect, Effect.components, Component.Covers]) hc
    have hnonzero : (.reg 3 : Operand 64).read s >>> 6 ≠ 0 := by
      intro heq
      have hn := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hn
      change ((.reg 3 : Operand 64).read s).toNat / 64 = 0 at hn
      have := hp.2
      omega
    have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
      have hz := he.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        ((.reg 3 : Operand 64).read s >>> 6 == 0) at hz
      exact hz.trans (beq_eq_false_iff_ne.mpr hnonzero)
    have hcond : condHolds 5 (StatusFlags.ofRFLAGS u.RFLAGS) = true := by
      change (!(StatusFlags.ofRFLAGS u.RFLAGS).ZF) = true
      rw [hz]
      rfl
    have hnext : (jccEffect 0x100427 2 5 ((0x9c#8).signExtend 64) u).rip = 0x1003c5 := by
      rw [jccEffect, hcond]
      rfl
    have hbranch : CodeIn (codeRange 0x100427 [0x75, 0x9c]) u :=
      program_text_slice hcu 0x427 2 (by decide +kernel)
    have hne : (jccEffect 0x100427 2 5 ((0x9c#8).signExtend 64) u).rip ≠ boundary.rip := by
      rw [hnext]
      exact text_address_ne_return hOutside 0x3c5 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x100427 5 0x9c).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩
      hne
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2⟩
    · apply (he.agrees.trans hag).mono
      simp [pc, alignedCountEffect, alignedBranchEffect, Effect.components]
  | true =>
    intro s hs hc hp
    have hbytes : CodeIn (codeRange 0x1019cd alignedCountBytes) s :=
      program_text_slice hc 0x19cd 10 (by decide +kernel)
    obtain ⟨fuel, u, ha, hu, _, he⟩ := aligned_count_prepare (variant := true) boundary hOutside s hs hbytes hp.1
    have hcu := he.agrees.codeIn (by
      simp [pc, alignedCountEffect, Effect.components, Component.Covers]) hc
    have hnonzero : (.reg 3 : Operand 64).read s >>> 6 ≠ 0 := by
      intro heq
      have hn := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hn
      change ((.reg 3 : Operand 64).read s).toNat / 64 = 0 at hn
      have := hp.2
      omega
    have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
      have hz := he.flags.2.2.2.1
      change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
        ((.reg 3 : Operand 64).read s >>> 6 == 0) at hz
      exact hz.trans (beq_eq_false_iff_ne.mpr hnonzero)
    have hcond : condHolds 5 (StatusFlags.ofRFLAGS u.RFLAGS) = true := by
      change (!(StatusFlags.ofRFLAGS u.RFLAGS).ZF) = true
      rw [hz]
      rfl
    have hnext : (jccEffect 0x1019d7 2 5 ((0x9c#8).signExtend 64) u).rip = 0x101975 := by
      rw [jccEffect, hcond]
      rfl
    have hbranch : CodeIn (codeRange 0x1019d7 [0x75, 0x9c]) u :=
      program_text_slice hcu 0x19d7 2 (by decide +kernel)
    have hne : (jccEffect 0x1019d7 2 5 ((0x9c#8).signExtend 64) u).rip ≠ boundary.rip := by
      rw [hnext]
      exact text_address_ne_return hOutside 0x1975 (by decide +kernel)
    obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x1019d7 5 0x9c).advances
      hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩
      hne
    have hag : AgreesExcept [.rip] u t := heb.agrees
    refine ⟨fuel + 1, t, ha.trans hb, ht,
      hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
    · exact ⟨(hag.read (by simp)).trans he.writes.1,
        (hag.read (by simp)).trans he.writes.2⟩
    · apply (he.agrees.trans hag).mono
      simp [pc, alignedCountEffect, alignedBranchEffect, Effect.components]

end Md5.Proofs.Buffered.Update.Slices
