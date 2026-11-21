import Md5.Proofs.Buffered.Update.ResetFirst.Prefix

namespace Md5.Proofs.NewEntries.Reset.FirstUpdate

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def remainderCountBytes : List UInt8 :=
  [0x4c, 0x89, 0xf3, 0x4c, 0x89, 0xea, 0x48, 0xc1, 0xea, 0x6]

def remainderCountEffect (s : RamState) : Effect :=
  { rip := 0x101465
    writes := [⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 13 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 13 : Operand 64).read s)) }

theorem remainder_count_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x10145b)
      (codeRange 0x10145b remainderCountBytes) remainderCountEffect := by
  unfold remainderCountBytes
  md5_run_begin mov_r64_r64_effect_step 0x10145b 0x4c 0xf3
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x145e (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x10145e 0x4c 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10145b) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1461 (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x101461 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10145b) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1465 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [remainderCountEffect, shiftCount]
  · x86_norm [remainderCountEffect, shiftCount]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [remainderCountEffect, shiftCount]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [remainderCountEffect, shiftCount]

def alignedCountBytes : List UInt8 :=
  [0x4d, 0x89, 0xf5, 0x4c, 0x89, 0xea, 0x48, 0xc1, 0xea, 0x6]

def alignedCountEffect (s : RamState) : Effect :=
  { rip := 0x1014be
    writes := [⟨(.reg 13 : Operand 64), (.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 14 : Operand 64).read s)) }

theorem aligned_count_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1014b4)
      (codeRange 0x1014b4 alignedCountBytes) alignedCountEffect := by
  unfold alignedCountBytes
  md5_run_begin mov_r64_r64_effect_step 0x1014b4 0x4d 0xf5
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14b7 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x1014b7 0x4c 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1014b4) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14ba (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x1014ba 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1014b4) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x14be (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [alignedCountEffect, shiftCount]
  · x86_norm [alignedCountEffect, shiftCount]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [alignedCountEffect, shiftCount]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [alignedCountEffect, shiftCount]

def partialCompressBytes : List UInt8 :=
  [0xba, 0x1, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x7c, 0x24, 0x60, 0x48, 0x8d, 0x74, 0x24, 0x20]

def partialCompressEffect (s : RamState) : Effect :=
  { rip := 0x101451
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 96⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 32⟩] }

theorem partial_compress_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x101442)
      (codeRange 0x101442 partialCompressBytes) partialCompressEffect := by
  unfold partialCompressBytes
  md5_run_begin mov_r32_imm32_effect_step 0x101442 0xba (by decide) 1
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1447 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x101447 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101442) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x144c (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x10144c 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 32)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x101442) 10 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1451 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partialCompressEffect]
  · x86_norm [partialCompressEffect, stackPtr]
    simp [Operand.read]
  · intro i; cases i <;> x86_norm [partialCompressEffect]
  · x86_norm [partialCompressEffect]

def fullCompressBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x60, 0x48, 0x89, 0xde]

def fullCompressEffect (s : RamState) : Effect :=
  { rip := 0x101474
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 96⟩,
      ⟨(.reg 6 : Operand 64), (.reg 3 : Operand 64).read s⟩] }

theorem full_compress_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x10146c)
      (codeRange 0x10146c fullCompressBytes) fullCompressEffect := by
  unfold fullCompressBytes
  md5_run_begin lea_r64_effect_step 0x10146c 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 96)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1471 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101471 0x48 0xde
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10146c) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x1474 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [fullCompressEffect]
  · x86_norm [fullCompressEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [fullCompressEffect]
  · x86_norm [fullCompressEffect]

end Md5.Proofs.NewEntries.Reset.FirstUpdate


namespace Md5.Proofs.NewEntries.Reset.FirstUpdate

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def remainderBranchEffect (s : RamState) : Effect :=
  { remainderCountEffect s with
    rip := if (.reg 13 : Operand 64).read s >>> 6 = 0 then 0x101479 else 0x101467
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem remainder_count_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x10145b)
      Extracted.programImage remainderBranchEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x10145b remainderCountBytes) s :=
    program_text_slice hc 0x145b 10 (by decide +kernel)
  obtain ⟨fuel, u, ha, hu, _, he⟩ := remainder_count_prepare boundary hOutside s hs hbytes hp
  have hcu := he.agrees.codeIn (by
    simp [remainderCountEffect, Effect.components, Component.Covers]) hc
  have hz : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      ((.reg 13 : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
  have hnext : (jccEffect 0x101465 2 4 ((0x12#8).signExtend 64) u).rip =
      (remainderBranchEffect s).rip := by
    simp only [jccEffect, hz, branchEffect, remainderBranchEffect, beq_iff_eq]
    split <;> rfl
  have hne : (remainderBranchEffect s).rip ≠ boundary.rip := by
    unfold remainderBranchEffect
    split
    · exact text_address_ne_return hOutside 0x1479 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1467 (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x101465 [0x74, 0x12]) u :=
    program_text_slice hcu 0x1465 2 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x101465 4 0x12).advances
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
    rip := 0x101467
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem aligned_count_nonzero [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x1014b4 ∧ 64 ≤ ((.reg 14 : Operand 64).read s).toNat)
      Extracted.programImage alignedBranchEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x1014b4 alignedCountBytes) s :=
    program_text_slice hc 0x14b4 10 (by decide +kernel)
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
  have hnext : (jccEffect 0x1014be 2 5 ((0xa7#8).signExtend 64) u).rip = 0x101467 := by
    rw [jccEffect, hcond]
    rfl
  have hbranch : CodeIn (codeRange 0x1014be [0x75, 0xa7]) u :=
    program_text_slice hcu 0x14be 2 (by decide +kernel)
  have hne : (jccEffect 0x1014be 2 5 ((0xa7#8).signExtend 64) u).rip ≠ boundary.rip := by
    rw [hnext]
    exact text_address_ne_return hOutside 0x1467 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x1014be 5 0xa7).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩
    hne
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨fuel + 1, t, ha.trans hb, ht,
    hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
  · exact ⟨(hag.read (by simp)).trans he.writes.1,
      (hag.read (by simp)).trans he.writes.2⟩
  · apply (he.agrees.trans hag).mono
    simp [alignedCountEffect, alignedBranchEffect, Effect.components]

end Md5.Proofs.NewEntries.Reset.FirstUpdate
