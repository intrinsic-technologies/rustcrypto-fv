import Md5.Proofs.Buffered.Update.ResetFirst.Layout
import Md5.Proofs.Buffered.Update.ResetFirst.Prefix
import Md5.Proofs.Buffered.Update.ResetFirst.Control
import Md5.Proofs.Buffered.Update.ResetFirst.Preparation
import Md5.Proofs.Buffered.Update.ResetFirst.Count
import Md5.Proofs.Buffered.Update.ResetFirst.CountBranch
import Md5.Proofs.Buffered.Update.ResetFirst.Calls
import Md5.Proofs.Buffered.Update.ResetFirst.ShortFinish
import Md5.Proofs.NewEntries.Reset.FirstUpdate.Prefix
import Md5.Proofs.NewEntries.Reset.FirstUpdate.Preparation
import Md5.Proofs.NewEntries.Reset.FirstUpdate.Count
import Md5.Proofs.NewEntries.Reset.FirstUpdate.Calls
import Md5.Proofs.NewEntries.Reset.FirstUpdate.ShortFinish


namespace Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def prefixBytes : List UInt8 :=
  [0x44, 0x0f, 0xb6, 0x6c, 0x24, 0x47, 0xba, 0x40, 0x00, 0x00, 0x00,
    0x4c, 0x29, 0xea, 0x4c, 0x89, 0xf3, 0x48, 0x29, 0xd3]

def position (s : RamState) : BitVec 64 :=
  ((Operand.mem (stackPtr s + 71) : Operand 8).read s).setWidth 64

def prefixEffect (s : RamState) : Effect :=
  let capacity := 64 - position s
  { rip := 0x100d94
    writes := [⟨(.reg 13 : Operand 64), position s⟩,
      ⟨(.reg 2 : Operand 64), capacity⟩,
      ⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s - capacity⟩]
    flags := some (.ofStatusFlags (subSpec ((.reg 14 : Operand 64).read s) capacity).2) }

theorem entry_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (LoadPre 0x100d80 (fun s ↦ stackPtr s + 71) 1)
      (codeRange 0x100d80 prefixBytes) prefixEffect := by
  unfold prefixBytes
  md5_run_begin (movzx_r_m8_rex_effect_step 0x100d80 0x44
    (by unfold RexPrefix; decide) 32 (.inr rfl)
    (fun seg ↦ (show RexNoWPrefix (0x44 : UInt8).toBitVec by
      unfold RexNoWPrefix; decide).operand_size seg)
    5 (.sib 4 none 0 (.d8 71)) (by decide) (by decide) (by decide))
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xd86 (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x100d86 0xba (by decide) 64
  case sub => exact codeRange_mem_of_drop (p := 0x100d80) 6 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xd8b (by decide +kernel)
  md5_run_then sub_r64_r64_effect_step 0x100d8b 0x4c 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d80) 11 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xd8e (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100d8e 0x4c 0xf3
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d80) 14 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xd91 (by decide +kernel)
  md5_run_then sub_r64_r64_effect_step 0x100d91 0x48 0xd3
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d80) 17 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0xd94 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [prefixEffect]
  · x86_norm [prefixEffect, position, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [prefixEffect, position, stackPtr]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [prefixEffect]

end Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

namespace Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def entryEffect (s : RamState) : Effect :=
  { prefixEffect s with
    rip := if ((.reg 14 : Operand 64).read s).toNat < (64 - position s).toNat then
      0x100d40 else 0x100d96
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem entry_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (LoadPre 0x100d80 (fun s ↦ stackPtr s + 71) 1)
      Extracted.programImage entryEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x100d80 prefixBytes) s :=
    program_text_slice hc 0xd80 20 (by decide +kernel)
  obtain ⟨fuel, u, ha, hu, _, he⟩ := entry_prepare boundary hOutside s hs hbytes hp
  have hcu := he.agrees.codeIn (by
    simp [prefixEffect, Effect.components, Component.Covers]) hc
  have hcf : condHolds 2 (StatusFlags.ofRFLAGS u.RFLAGS) =
      decide (((.reg 14 : Operand 64).read s).toNat < (64 - position s).toNat) :=
    he.flags.1
  have hnext : (jccEffect 0x100d94 2 2 ((0xaa#8).signExtend 64) u).rip =
      (entryEffect s).rip := by
    simp only [jccEffect, hcf, branchEffect, entryEffect, decide_eq_true_eq]
    split <;> rfl
  have hne : (entryEffect s).rip ≠ boundary.rip := by
    unfold entryEffect
    split
    · exact text_address_ne_return hOutside 0xd40 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xd96 (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x100d94 [0x72, 0xaa]) u :=
    program_text_slice hcu 0xd94 2 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x100d94 2 0xaa).advances
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
  { rip := if (.reg 13 : Operand 64).read s = 0 then 0x100e29 else 0x100d9f
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem partial_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100d96)
      Extracted.programImage partialEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x100d96 [0x4d, 0x85, 0xed]) s :=
    program_text_slice hc 0xd96 3 (by decide +kernel)
  have htest : StepEffect (fun s ↦ s.RIP = 0x100d96)
      (codeRange 0x100d96 [0x4d, 0x85, 0xed]) (testR64R64Effect 0x100d96 13 13) :=
    test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨u, ha, hu, he⟩ := htest.advances hs hbytes hp
    (text_address_ne_return hOutside 0xd99 (by decide +kernel))
  have hcu := he.codeIn (testR64R64Effect_avoids _ _ _ _ _) hc
  have hzf : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      ((.reg 13 : Operand 64).read s == 0) := by
    have hz := he.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((.reg 13 : Operand 64).read s &&& (.reg 13 : Operand 64).read s) == 0) at hz
    rw [BitVec.and_self] at hz
    exact hz
  have hnext : (jccEffect 0x100d99 6 4 ((0x8a#32).signExtend 64) u).rip =
      (partialEffect s).rip := by
    simp only [jccEffect, hzf, branchEffect, partialEffect, beq_iff_eq]
    split <;> rfl
  have hne : (partialEffect s).rip ≠ boundary.rip := by
    unfold partialEffect
    split
    · exact text_address_ne_return hOutside 0xe29 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xd9f (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x100d99 [0x0f, 0x84, 0x8a, 0x00, 0x00, 0x00]) u :=
    program_text_slice hcu 0xd99 6 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel32_effect_step 0x100d99 4 0x8a).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨2, t, ha.trans hb, ht, hag.codeIn (by simp [Component.Covers]) hcu,
    heb.rip.trans hnext, by trivial, by trivial, ?_⟩
  apply (he.agrees.trans hag).mono
  simp [partialEffect, testR64R64Effect, Effect.components]

end Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst
namespace Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortCopyBytes : List UInt8 :=
  [0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x08, 0x4c, 0x89, 0xe6,
    0x4c, 0x89, 0xf2]

def shortCopyEffect (s : RamState) : Effect :=
  { rip := 0x100d4e
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + (.reg 13 : Operand 64).read s + 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100d40)
      (codeRange 0x100d40 shortCopyBytes) shortCopyEffect := by
  unfold shortCopyBytes
  md5_run_begin lea_r64_effect_step 0x100d40 0x4a (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd44 (by decide +kernel)
  md5_run_then add_r64_imm8_effect_step 0x100d44 0x48 0xc7 8
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d40) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd48 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100d48 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d40) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd4b (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100d4b 0x4c 0xf2
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d40) 11 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd4e (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [shortCopyEffect]
  · x86_norm [shortCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [shortCopyEffect]
  · x86_norm [shortCopyEffect]

def fillCopyBytes : List UInt8 :=
  [0x4d, 0x8d, 0x34, 0x14, 0x4a, 0x8d, 0x3c, 0x2c, 0x48, 0x83, 0xc7, 0x08,
    0x4c, 0x89, 0xe6]

def fillCopyEffect (s : RamState) : Effect :=
  { rip := 0x100dae
    writes := [⟨(.reg 14 : Operand 64), (.reg 12 : Operand 64).read s +
      (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + (.reg 13 : Operand 64).read s + 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem fill_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100d9f)
      (codeRange 0x100d9f fillCopyBytes) fillCopyEffect := by
  unfold fillCopyBytes
  md5_run_begin lea_r64_effect_step 0x100d9f 0x4d (by unfold RexWPrefix; decide)
    6 (.sib 12 (some 2) 0 .none) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xda3 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x100da3 0x4a (by unfold RexWPrefix; decide)
    7 (.sib 4 (some 13) 0 .none) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d9f) 4 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xda7 (by decide +kernel)
  md5_run_then add_r64_imm8_effect_step 0x100da7 0x48 0xc7 8
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d9f) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdab (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100dab 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d9f) 12 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdae (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [fillCopyEffect]
  · x86_norm [fillCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [fillCopyEffect]
  · x86_norm [fillCopyEffect]

def tailPointerBytes : List UInt8 :=
  [0x48, 0x89, 0xd8, 0x48, 0xb9, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f,
    0x48, 0x21, 0xc8, 0x83, 0xe3, 0x3f, 0x49, 0x01, 0xc4]

def tailPointerEffect (s : RamState) : Effect :=
  let full := (.reg 3 : Operand 64).read s &&& 0x7fffffffffffffc0
  { rip := 0x100e06
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg 3 : Operand 64), (((.reg 3 : Operand 32).read s) &&& 63).setWidth 64⟩,
      ⟨(.reg 12 : Operand 64), (.reg 12 : Operand 64).read s + full⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem tail_pointer_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100df0)
      (codeRange 0x100df0 tailPointerBytes) tailPointerEffect := by
  unfold tailPointerBytes
  md5_run_begin mov_r64_r64_effect_step 0x100df0 0x48 0xd8
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdf3 (by decide +kernel)
  md5_run_then mov_r64_imm64_effect_step 0x100df3 0x48 0xb9
    (by unfold RexWPrefix; decide) (by decide) 0x7fffffffffffffc0
  case sub => exact codeRange_mem_of_drop (p := 0x100df0) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdfd (by decide +kernel)
  md5_run_then and_r64_r64_effect_step 0x100dfd 0x48 0xc8
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100df0) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe00 (by decide +kernel)
  md5_run_then and_r32_imm8_effect_step 0x100e00 0xe3 63 (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100df0) 16 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe03 (by decide +kernel)
  md5_run_then add_r64_r64_effect_step 0x100e03 0x49 0xc4
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100df0) 19 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe06 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [tailPointerEffect]
  · x86_norm [tailPointerEffect]
    simp [Operand.read, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · intro i; cases i <;> x86_norm [tailPointerEffect]
  · x86_norm [tailPointerEffect]

def tailCopyBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x08, 0x4c, 0x89, 0xe6, 0x48, 0x89, 0xda]

def tailCopyEffect (s : RamState) : Effect :=
  { rip := 0x100e15
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s⟩] }

theorem tail_copy_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100e0a)
      (codeRange 0x100e0a tailCopyBytes) tailCopyEffect := by
  unfold tailCopyBytes
  md5_run_begin lea_r64_effect_step 0x100e0a 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe0f (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100e0f 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100e0a) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe12 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100e12 0x48 0xda
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100e0a) 8 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe15 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [tailCopyEffect]
  · x86_norm [tailCopyEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [tailCopyEffect]
  · x86_norm [tailCopyEffect]

end Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

namespace Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def remainderCountBytes : List UInt8 :=
  [0x4d, 0x89, 0xf4, 0x48, 0x89, 0xda, 0x48, 0xc1, 0xea, 0x06]

def remainderCountEffect (s : RamState) : Effect :=
  { rip := 0x100ddc
    writes := [⟨(.reg 12 : Operand 64), (.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 3 : Operand 64).read s)) }

theorem remainder_count_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100dd2)
      (codeRange 0x100dd2 remainderCountBytes) remainderCountEffect := by
  unfold remainderCountBytes
  md5_run_begin mov_r64_r64_effect_step 0x100dd2 0x4d 0xf4
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdd5 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100dd5 0x48 0xda
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100dd2) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdd8 (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x100dd8 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100dd2) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xddc (by decide +kernel)
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
  [0x4c, 0x89, 0xf3, 0x48, 0x89, 0xda, 0x48, 0xc1, 0xea, 0x06]

def alignedCountEffect (s : RamState) : Effect :=
  { rip := 0x100e33
    writes := [⟨(.reg 3 : Operand 64), (.reg 14 : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg 14 : Operand 64).read s)) }

theorem aligned_count_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100e29)
      (codeRange 0x100e29 alignedCountBytes) alignedCountEffect := by
  unfold alignedCountBytes
  md5_run_begin mov_r64_r64_effect_step 0x100e29 0x4c 0xf3
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe2c (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100e2c 0x48 0xda
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100e29) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe2f (by decide +kernel)
  md5_run_then shr_r64_imm8_effect_step 0x100e2f 0x48 0xea 6
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100e29) 6 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe33 (by decide +kernel)
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
  [0xba, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x7c, 0x24, 0x48,
    0x48, 0x8d, 0x74, 0x24, 0x08]

def partialCompressEffect (s : RamState) : Effect :=
  { rip := 0x100dc8
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 8⟩] }

theorem partial_compress_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100db9)
      (codeRange 0x100db9 partialCompressBytes) partialCompressEffect := by
  unfold partialCompressBytes
  md5_run_begin mov_r32_imm32_effect_step 0x100db9 0xba (by decide) 1
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdbe (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x100dbe 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100db9) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdc3 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x100dc3 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d8 8)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100db9) 10 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdc8 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [partialCompressEffect]
  · x86_norm [partialCompressEffect, stackPtr]
    simp [Operand.read]
  · intro i; cases i <;> x86_norm [partialCompressEffect]
  · x86_norm [partialCompressEffect]

def fullCompressBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x48, 0x4c, 0x89, 0xe6]

def fullCompressEffect (s : RamState) : Effect :=
  { rip := 0x100deb
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), (.reg 12 : Operand 64).read s⟩] }

theorem full_compress_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100de3)
      (codeRange 0x100de3 fullCompressBytes) fullCompressEffect := by
  unfold fullCompressBytes
  md5_run_begin lea_r64_effect_step 0x100de3 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 72)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xde8 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x100de8 0x4c 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100de3) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdeb (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [fullCompressEffect]
  · x86_norm [fullCompressEffect, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [fullCompressEffect]
  · x86_norm [fullCompressEffect]

end Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

namespace Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def remainderBranchEffect (s : RamState) : Effect :=
  { remainderCountEffect s with
    rip := if (.reg 3 : Operand 64).read s >>> 6 = 0 then 0x100df0 else 0x100dde
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem remainder_count_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100dd2)
      Extracted.programImage remainderBranchEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x100dd2 remainderCountBytes) s :=
    program_text_slice hc 0xdd2 10 (by decide +kernel)
  obtain ⟨fuel, u, ha, hu, _, he⟩ := remainder_count_prepare boundary hOutside s hs hbytes hp
  have hcu := he.agrees.codeIn (by
    simp [remainderCountEffect, Effect.components, Component.Covers]) hc
  have hz : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      ((.reg 3 : Operand 64).read s >>> 6 == 0) := he.flags.2.2.2.1
  have hnext : (jccEffect 0x100ddc 2 4 ((0x12#8).signExtend 64) u).rip =
      (remainderBranchEffect s).rip := by
    simp only [jccEffect, hz, branchEffect, remainderBranchEffect, beq_iff_eq]
    split <;> rfl
  have hne : (remainderBranchEffect s).rip ≠ boundary.rip := by
    unfold remainderBranchEffect
    split
    · exact text_address_ne_return hOutside 0xdf0 (by decide +kernel)
    · exact text_address_ne_return hOutside 0xdde (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x100ddc [0x74, 0x12]) u :=
    program_text_slice hcu 0xddc 2 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x100ddc 4 0x12).advances
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
    rip := 0x100dde
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem aligned_count_nonzero [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = 0x100e29 ∧ 64 ≤ ((.reg 14 : Operand 64).read s).toNat)
      Extracted.programImage alignedBranchEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x100e29 alignedCountBytes) s :=
    program_text_slice hc 0xe29 10 (by decide +kernel)
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
  have hnext : (jccEffect 0x100e33 2 5 ((0xa9#8).signExtend 64) u).rip = 0x100dde := by
    rw [jccEffect, hcond]
    rfl
  have hbranch : CodeIn (codeRange 0x100e33 [0x75, 0xa9]) u :=
    program_text_slice hcu 0xe33 2 (by decide +kernel)
  have hne : (jccEffect 0x100e33 2 5 ((0xa9#8).signExtend 64) u).rip ≠ boundary.rip := by
    rw [hnext]
    exact text_address_ne_return hOutside 0xdde (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x100e33 5 0xa9).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩
    hne
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨fuel + 1, t, ha.trans hb, ht,
    hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
  · exact ⟨(hag.read (by simp)).trans he.writes.1,
      (hag.read (by simp)).trans he.writes.2⟩
  · apply (he.agrees.trans hag).mono
    simp [alignedCountEffect, alignedBranchEffect, Effect.components]

end Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst



namespace Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

theorem memcpy_rip [bindings : Bindings] (hstride : Prelude.UnitStringStride bindings)
    {boundary : ReturnBoundary} {p : BitVec 64} {s : RamState}
    (hsite : p = 0x100d4e ∨ p = 0x100dae ∨ p = 0x100e15)
    (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hslot : Memory.MemWritable s (pushAddr s) 8)
    (hp : MemcpySitePre (p + 6) s) :
    ∃ t, MemcpySiteResult boundary (p + 6) s t := by
  have hb := outside_text_range_of_not_inProgram hout 0x1024b0 0x1024df
    (by decide) (by decide +kernel)
  rcases hsite with rfl | rfl | rfl
  · have htarget : callMemPtr 0x100d4e (.rip 0xff2ac) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x100d4e [0xff, 0x15, 0xac, 0xf2, 0x0f, 0x00]) s :=
      program_text_slice hcode 0xd4e 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x100d4e 0xff2ac)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0xd54 (by decide +kernel))
  · have htarget : callMemPtr 0x100dae (.rip 0xff24c) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x100dae [0xff, 0x15, 0x4c, 0xf2, 0x0f, 0x00]) s :=
      program_text_slice hcode 0xdae 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x100dae 0xff24c)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0xdb4 (by decide +kernel))
  · have htarget : callMemPtr 0x100e15 (.rip 0xff1e5) s = 0x1024b0 := memcpy_pointer hcode
    have hbytes : CodeIn (codeRange 0x100e15 [0xff, 0x15, 0xe5, 0xf1, 0x0f, 0x00]) s :=
      program_text_slice hcode 0xe15 6 (by decide +kernel)
    exact memcpy_call hstride hb (Stack.call_m64_rip_effect_step 0x100e15 0xff1e5)
      hready hcode hbytes
      ⟨⟨⟨hrip, hslot⟩, by rw [htarget]; decide⟩, memcpy_pointer_readable hcode⟩
      hp htarget (text_address_ne_return hout 0xe1b (by decide +kernel))

theorem compress_call [Bindings] {boundary : ReturnBoundary} {p : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (hsite : p = 0x100dc8 ∨ p = 0x100deb) (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hp : FinalizeReset.CompressCall.Pre buffer input s) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (p + 5) buffer input s t := by
  rcases hsite with rfl | rfl
  · have hbytes : CodeIn (codeRange 0x100dc8 [0xe8, 0xd3, 0x0d, 0x00, 0x00]) s :=
      program_text_slice hcode 0xdc8 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x100dc8 0xdd3 (by decide)) hready hcode hbytes
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0xdcd (by decide +kernel))
  · have hbytes : CodeIn (codeRange 0x100deb [0xe8, 0xb0, 0x0d, 0x00, 0x00]) s :=
      program_text_slice hcode 0xdeb 5 (by decide +kernel)
    exact FinalizeReset.CompressCall.run_of_step
      (Stack.call_rel32_effect_step 0x100deb 0xdb0 (by decide)) hready hcode hbytes
      ⟨hrip, hp.pushWritable⟩ hp rfl (by decide) (by unfold OutsideCompression; decide) hout
      (text_address_ne_return hout 0xdf0 (by decide +kernel))

end Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst


namespace Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortFinishBytes : List UInt8 :=
  [0x45, 0x00, 0xee, 0x44, 0x88, 0x74, 0x24, 0x47]

def shortFinishEffect (s : RamState) : Effect :=
  let value := (.reg 14 : Operand 8).read s + (.reg 13 : Operand 8).read s
  { rip := 0x100d5c
    writes := [⟨(.reg 14 : Operand 64), mergeGPR 8 value ((.reg 14 : Operand 64).read s)⟩,
      ⟨(.mem (stackPtr s + 71) : Operand 8), value⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_finish [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100d54 ∧
      Md5.Proofs.Memory.MemWritable s (stackPtr s + 71) 1 ∧
      RangeApart (stackPtr s + 71) 1 0x100d54 8)
      (codeRange 0x100d54 shortFinishBytes) shortFinishEffect := by
  unfold shortFinishBytes
  md5_run_begin Update.Byte.add_r8_r8_effect_step 0x100d54 0x45 0xee
    (by unfold RexPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd57 (by decide +kernel)
  md5_run_then Update.Byte.mov_m8_r8_rex_effect_step 0x100d57 0x44
    (by unfold RexPrefix; decide) 6 (.sib 4 none 0 (.d8 71))
    (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100d54) 3 (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨Md5.Proofs.Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.2.1
    · x86_norm
      exact MemoryRoutines.rangeApart_slice_right h.2.2 3 5 (by decide)
    · apply Effect.avoids_of_components_mem_rip
        (storeEffect_components 0x100d57 5
          (storeAddrAt 0x100d57 (.sib 4 none 0 (.d8 71)) 5)
          (fun u ↦ (.reg 14 : Operand 8).read u) t)
      change RangeApart (stackPtr t + 71) 1 0x100d54 8
      rw [hsp]
      exact h.2.2
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd5c (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [shortFinishEffect]
  · x86_norm [shortFinishEffect, stackPtr]
    simp [gprNumber, rexB, rexR, modrmReg, modrmRm, Operand.read]
  · intro i; cases i <;> x86_norm [shortFinishEffect]
  · x86_norm [shortFinishEffect, stackPtr]
    rfl

end Md5.Proofs.Buffered.ResetFirst.FinalizeResetFirst

namespace Md5.Proofs.Buffered.ResetFirst

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def position_of_kind (kind : UpdateKind) (s : RamState) : BitVec 64 :=
  ((Operand.mem (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + 63)) : Operand 8).read s).setWidth 64

def prefixEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  let capacity := 64 - position_of_kind kind s
  { rip := pc kind 0x6e4
    writes := [⟨(.reg (reg kind 13) : Operand 64), position_of_kind kind s⟩,
      ⟨(.reg 2 : Operand 64), capacity⟩,
      ⟨(.reg (reg kind 3) : Operand 64),
        (.reg kind.sizeRegister : Operand 64).read s - capacity⟩]
    flags := some (.ofStatusFlags
      (subSpec ((.reg kind.sizeRegister : Operand 64).read s) capacity).2) }

def entryEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { prefixEffect_of_kind kind s with
    rip := if ((.reg kind.sizeRegister : Operand 64).read s).toNat <
      (64 - position_of_kind kind s).toNat then pc kind 0x690 else pc kind 0x6e6
    flags := some ⟨none, none, none, none, none, none⟩ }

def partialEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := if (.reg (reg kind 13) : Operand 64).read s = 0 then
      pc kind 0x779 else pc kind 0x6ef
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem entry_branch_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (LoadPre kind.entry (fun s ↦ stackPtr s + BitVec.ofNat 64 (kind.contextOffset + 63)) 1)
      Extracted.programImage (entryEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact entry_branch boundary hOutside
  · exact FinalizeResetFirst.entry_branch boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.entry_branch boundary hOutside

theorem partial_branch_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x6e6)
      Extracted.programImage (partialEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact partial_branch boundary hOutside
  · exact FinalizeResetFirst.partial_branch boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.partial_branch boundary hOutside

end Md5.Proofs.Buffered.ResetFirst

namespace Md5.Proofs.Buffered.ResetFirst
open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def shortCopyBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then
    Md5.Proofs.NewEntries.Reset.FirstUpdate.shortCopyBytes
  else shortCopyBytes

def shortCopyEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x69e)
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + (.reg (reg kind 13) : Operand 64).read s + stackOffset kind 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def fillCopyBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then
    Md5.Proofs.NewEntries.Reset.FirstUpdate.fillCopyBytes
  else fillCopyBytes

def fillCopyEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x6fe)
    writes := [⟨(.reg kind.sizeRegister : Operand 64), (.reg kind.inputRegister : Operand 64).read s +
      (.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + (.reg (reg kind 13) : Operand 64).read s + stackOffset kind 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def tailPointerBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then
    Md5.Proofs.NewEntries.Reset.FirstUpdate.tailPointerBytes
  else tailPointerBytes

def tailPointerEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  let full := (.reg (reg kind 3) : Operand 64).read s &&& 0x7fffffffffffffc0
  { rip := (pc kind 0x756)
    writes := [⟨(.reg 0 : Operand 64), full⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
      ⟨(.reg (reg kind 3) : Operand 64), (((.reg (reg kind 3) : Operand 32).read s) &&& 63).setWidth 64⟩,
      ⟨(.reg kind.inputRegister : Operand 64), (.reg kind.inputRegister : Operand 64).read s + full⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def tailCopyBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then
    Md5.Proofs.NewEntries.Reset.FirstUpdate.tailCopyBytes
  else tailCopyBytes

def tailCopyEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x765)
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + stackOffset kind 8⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg (reg kind 3) : Operand 64).read s⟩] }

theorem short_copy_prepare_code_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x690))
      (codeRange (pc kind 0x690) (shortCopyBytes_of_kind kind)) (shortCopyEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact short_copy_prepare boundary hOutside
  · exact FinalizeResetFirst.short_copy_prepare boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.short_copy_prepare boundary hOutside

theorem fill_copy_prepare_code_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x6ef))
      (codeRange (pc kind 0x6ef) (fillCopyBytes_of_kind kind)) (fillCopyEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact fill_copy_prepare boundary hOutside
  · exact FinalizeResetFirst.fill_copy_prepare boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.fill_copy_prepare boundary hOutside

theorem tail_pointer_prepare_code_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x740))
      (codeRange (pc kind 0x740) (tailPointerBytes_of_kind kind)) (tailPointerEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact tail_pointer_prepare boundary hOutside
  · exact FinalizeResetFirst.tail_pointer_prepare boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.tail_pointer_prepare boundary hOutside

theorem tail_copy_prepare_code_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x75a))
      (codeRange (pc kind 0x75a) (tailCopyBytes_of_kind kind)) (tailCopyEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact tail_copy_prepare boundary hOutside
  · exact FinalizeResetFirst.tail_copy_prepare boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.tail_copy_prepare boundary hOutside

def remainderCountBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then
    Md5.Proofs.NewEntries.Reset.FirstUpdate.remainderCountBytes
  else remainderCountBytes

def remainderCountEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x72c)
    writes := [⟨(.reg kind.inputRegister : Operand 64), (.reg kind.sizeRegister : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg (reg kind 3) : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg (reg kind 3) : Operand 64).read s)) }

def alignedCountBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then
    Md5.Proofs.NewEntries.Reset.FirstUpdate.alignedCountBytes
  else alignedCountBytes

def alignedCountEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x783)
    writes := [⟨(.reg (reg kind 3) : Operand 64), (.reg kind.sizeRegister : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), (.reg kind.sizeRegister : Operand 64).read s >>> 6⟩]
    flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 ((.reg kind.sizeRegister : Operand 64).read s)) }

def partialCompressBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then
    Md5.Proofs.NewEntries.Reset.FirstUpdate.partialCompressBytes
  else partialCompressBytes

def partialCompressEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x718)
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + stackOffset kind 72⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + stackOffset kind 8⟩] }

def fullCompressBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then
    Md5.Proofs.NewEntries.Reset.FirstUpdate.fullCompressBytes
  else fullCompressBytes

def fullCompressEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { rip := (pc kind 0x73b)
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + stackOffset kind 72⟩,
      ⟨(.reg 6 : Operand 64), (.reg kind.inputRegister : Operand 64).read s⟩] }

theorem remainder_count_prepare_code_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x722))
      (codeRange (pc kind 0x722) (remainderCountBytes_of_kind kind)) (remainderCountEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact remainder_count_prepare boundary hOutside
  · exact FinalizeResetFirst.remainder_count_prepare boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.remainder_count_prepare boundary hOutside

theorem aligned_count_prepare_code_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x779))
      (codeRange (pc kind 0x779) (alignedCountBytes_of_kind kind)) (alignedCountEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact aligned_count_prepare boundary hOutside
  · exact FinalizeResetFirst.aligned_count_prepare boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.aligned_count_prepare boundary hOutside

theorem partial_compress_prepare_code_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x709))
      (codeRange (pc kind 0x709) (partialCompressBytes_of_kind kind)) (partialCompressEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact partial_compress_prepare boundary hOutside
  · exact FinalizeResetFirst.partial_compress_prepare boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.partial_compress_prepare boundary hOutside

theorem full_compress_prepare_code_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x733))
      (codeRange (pc kind 0x733) (fullCompressBytes_of_kind kind)) (fullCompressEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact full_compress_prepare boundary hOutside
  · exact FinalizeResetFirst.full_compress_prepare boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.full_compress_prepare boundary hOutside

def remainderBranchEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { remainderCountEffect_of_kind kind s with
    rip := if (.reg (reg kind 3) : Operand 64).read s >>> 6 = 0 then (pc kind 0x740) else (pc kind 0x72e)
    flags := some ⟨none, none, none, none, none, none⟩ }

def alignedBranchEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  { alignedCountEffect_of_kind kind s with
    rip := (pc kind 0x72e)
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem remainder_count_branch_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (pc kind 0x722))
      Extracted.programImage (remainderBranchEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact remainder_count_branch boundary hOutside
  · exact FinalizeResetFirst.remainder_count_branch boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.remainder_count_branch boundary hOutside

theorem aligned_count_nonzero_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind) (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary
      (fun s ↦ s.RIP = (pc kind 0x779) ∧ 64 ≤ ((.reg kind.sizeRegister : Operand 64).read s).toNat)
      Extracted.programImage (alignedBranchEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact aligned_count_nonzero boundary hOutside
  · exact FinalizeResetFirst.aligned_count_nonzero boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.aligned_count_nonzero boundary hOutside

theorem short_copy_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x690)
      Extracted.programImage (shortCopyEffect_of_kind kind) := by
  intro s hs hc hp
  have hb : CodeIn (codeRange (pc kind 0x690) (shortCopyBytes_of_kind kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x690 14 (by decide +kernel)
    · exact program_text_slice hc 0xd40 14 (by decide +kernel)
    · exact program_text_slice hc 0x13d0 14 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := short_copy_prepare_code_of_kind hk boundary hOutside s hs hb hp
  exact ⟨n, t, ha, ht, he.agrees.codeIn (by
    simp [shortCopyEffect_of_kind, Effect.components, Component.Covers]) hc, he⟩

theorem fill_copy_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x6ef)
      Extracted.programImage (fillCopyEffect_of_kind kind) := by
  intro s hs hc hp
  have hb : CodeIn (codeRange (pc kind 0x6ef) (fillCopyBytes_of_kind kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x6ef 15 (by decide +kernel)
    · exact program_text_slice hc 0xd9f 15 (by decide +kernel)
    · exact program_text_slice hc 0x1428 15 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := fill_copy_prepare_code_of_kind hk boundary hOutside s hs hb hp
  exact ⟨n, t, ha, ht, he.agrees.codeIn (by
    simp [fillCopyEffect_of_kind, Effect.components, Component.Covers]) hc, he⟩

theorem tail_pointer_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x740)
      Extracted.programImage (tailPointerEffect_of_kind kind) := by
  intro s hs hc hp
  have hb : CodeIn (codeRange (pc kind 0x740) (tailPointerBytes_of_kind kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x740 22 (by decide +kernel)
    · exact program_text_slice hc 0xdf0 22 (by decide +kernel)
    · exact program_text_slice hc 0x1479 23 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := tail_pointer_prepare_code_of_kind hk boundary hOutside s hs hb hp
  exact ⟨n, t, ha, ht, he.agrees.codeIn (by
    simp [tailPointerEffect_of_kind, Effect.components, Component.Covers]) hc, he⟩

theorem tail_copy_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x75a)
      Extracted.programImage (tailCopyEffect_of_kind kind) := by
  intro s hs hc hp
  have hb : CodeIn (codeRange (pc kind 0x75a) (tailCopyBytes_of_kind kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x75a 11 (by decide +kernel)
    · exact program_text_slice hc 0xe0a 11 (by decide +kernel)
    · exact program_text_slice hc 0x1495 11 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := tail_copy_prepare_code_of_kind hk boundary hOutside s hs hb hp
  exact ⟨n, t, ha, ht, he.agrees.codeIn (by
    simp [tailCopyEffect_of_kind, Effect.components, Component.Covers]) hc, he⟩

theorem remainder_count_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x722)
      Extracted.programImage (remainderCountEffect_of_kind kind) := by
  intro s hs hc hp
  have hb : CodeIn (codeRange (pc kind 0x722) (remainderCountBytes_of_kind kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x722 10 (by decide +kernel)
    · exact program_text_slice hc 0xdd2 10 (by decide +kernel)
    · exact program_text_slice hc 0x145b 10 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := remainder_count_prepare_code_of_kind hk boundary hOutside s hs hb hp
  exact ⟨n, t, ha, ht, he.agrees.codeIn (by
    simp [remainderCountEffect_of_kind, Effect.components, Component.Covers]) hc, he⟩

theorem aligned_count_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x779)
      Extracted.programImage (alignedCountEffect_of_kind kind) := by
  intro s hs hc hp
  have hb : CodeIn (codeRange (pc kind 0x779) (alignedCountBytes_of_kind kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x779 10 (by decide +kernel)
    · exact program_text_slice hc 0xe29 10 (by decide +kernel)
    · exact program_text_slice hc 0x14b4 10 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := aligned_count_prepare_code_of_kind hk boundary hOutside s hs hb hp
  exact ⟨n, t, ha, ht, he.agrees.codeIn (by
    simp [alignedCountEffect_of_kind, Effect.components, Component.Covers]) hc, he⟩

theorem partial_compress_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x709)
      Extracted.programImage (partialCompressEffect_of_kind kind) := by
  intro s hs hc hp
  have hb : CodeIn (codeRange (pc kind 0x709) (partialCompressBytes_of_kind kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x709 15 (by decide +kernel)
    · exact program_text_slice hc 0xdb9 15 (by decide +kernel)
    · exact program_text_slice hc 0x1442 15 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := partial_compress_prepare_code_of_kind hk boundary hOutside s hs hb hp
  exact ⟨n, t, ha, ht, he.agrees.codeIn (by
    simp [partialCompressEffect_of_kind, Effect.components, Component.Covers]) hc, he⟩

theorem full_compress_prepare_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x733)
      Extracted.programImage (fullCompressEffect_of_kind kind) := by
  intro s hs hc hp
  have hb : CodeIn (codeRange (pc kind 0x733) (fullCompressBytes_of_kind kind)) s := by
    rcases hk with rfl | rfl | rfl
    · exact program_text_slice hc 0x733 8 (by decide +kernel)
    · exact program_text_slice hc 0xde3 8 (by decide +kernel)
    · exact program_text_slice hc 0x146c 8 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := full_compress_prepare_code_of_kind hk boundary hOutside s hs hb hp
  exact ⟨n, t, ha, ht, he.agrees.codeIn (by
    simp [fullCompressEffect_of_kind, Effect.components, Component.Covers]) hc, he⟩

end Md5.Proofs.Buffered.ResetFirst

namespace Md5.Proofs.Buffered.ResetFirst
open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block
theorem memcpy_rip_of_kind [bindings : Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (hstride : Prelude.UnitStringStride bindings)
    {boundary : ReturnBoundary} {p : BitVec 64} {s : RamState}
    (hsite : p = (pc kind 0x69e) ∨ p = (pc kind 0x6fe) ∨ p = (pc kind 0x765))
    (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hslot : Memory.MemWritable s (pushAddr s) 8)
    (hp : MemcpySitePre (p + 6) s) :
    ∃ t, MemcpySiteResult boundary (p + 6) s t := by
  rcases hk with rfl | rfl | rfl
  · exact memcpy_rip hstride hsite hout hready hcode hrip hslot hp
  · exact FinalizeResetFirst.memcpy_rip hstride hsite hout hready hcode hrip hslot hp
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.memcpy_rip hstride hsite hout hready hcode hrip hslot hp

theorem compress_call_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    {boundary : ReturnBoundary} {p : BitVec 64}
    {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray} {s : RamState}
    (hsite : p = (pc kind 0x718) ∨ p = (pc kind 0x73b)) (hout : ¬ InProgram boundary.rip)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hrip : s.RIP = p) (hp : FinalizeReset.CompressCall.Pre buffer input s) :
    ∃ t, FinalizeReset.CompressCall.Post boundary (p + 5) buffer input s t := by
  rcases hk with rfl | rfl | rfl
  · exact compress_call hsite hout hready hcode hrip hp
  · exact FinalizeResetFirst.compress_call hsite hout hready hcode hrip hp
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.compress_call hsite hout hready hcode hrip hp

def shortFinishBytes_of_kind (kind : UpdateKind) : List UInt8 :=
  if kind = .resetDiscardFirst then Md5.Proofs.NewEntries.Reset.FirstUpdate.shortFinishBytes
  else shortFinishBytes

def shortFinishEffect_of_kind (kind : UpdateKind) (s : RamState) : Effect :=
  let value := (.reg kind.sizeRegister : Operand 8).read s + (.reg (reg kind 13) : Operand 8).read s
  { rip := pc kind 0x6ac
    writes := [⟨(.reg kind.sizeRegister : Operand 64), mergeGPR 8 value ((.reg kind.sizeRegister : Operand 64).read s)⟩,
      ⟨(.mem (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + 63)) : Operand 8), value⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem short_finish_of_kind [Bindings] {kind : UpdateKind} (hk : KindSupported kind)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = pc kind 0x6a4 ∧
      Md5.Proofs.Memory.MemWritable s (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + 63)) 1 ∧
      RangeApart (stackPtr s + BitVec.ofNat 64 (kind.contextOffset + 63)) 1 (pc kind 0x6a4) 8)
      (codeRange (pc kind 0x6a4) (shortFinishBytes_of_kind kind)) (shortFinishEffect_of_kind kind) := by
  rcases hk with rfl | rfl | rfl
  · exact short_finish boundary hOutside
  · exact FinalizeResetFirst.short_finish boundary hOutside
  · exact Md5.Proofs.NewEntries.Reset.FirstUpdate.short_finish boundary hOutside

end Md5.Proofs.Buffered.ResetFirst
