import Md5.Proofs.Buffered.Update.ResetFirst.Prefix
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Md5.Proofs.NewEntries.Reset.FirstUpdate

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def prefixBytes : List UInt8 :=
  [0x0f, 0xb6, 0x6c, 0x24, 0x5f, 0xba, 0x40, 0x00, 0x00, 0x00,
    0x48, 0x29, 0xea, 0x4d, 0x89, 0xf5, 0x49, 0x29, 0xd5]

def position (s : RamState) : BitVec 64 :=
  ((Operand.mem (stackPtr s + 95) : Operand 8).read s).setWidth 64

def prefixEffect (s : RamState) : Effect :=
  let capacity := 64 - position s
  { rip := 0x10141d
    writes := [⟨(.reg 5 : Operand 64), position s⟩,
      ⟨(.reg 2 : Operand 64), capacity⟩,
      ⟨(.reg 13 : Operand 64), (.reg 14 : Operand 64).read s - capacity⟩]
    flags := some (.ofStatusFlags (subSpec ((.reg 14 : Operand 64).read s) capacity).2) }

theorem entry_prepare [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ Md5.Spec.Program.InProgram boundary.rip) :
    AdvancesBlock boundary (LoadPre 0x10140a (fun s ↦ stackPtr s + 95) 1)
      (codeRange 0x10140a prefixBytes) prefixEffect := by
  unfold prefixBytes
  md5_run_begin movzx_r32_m8_effect_step 0x10140a
    5 (.sib 4 none 0 (.d8 95)) (by decide) (by decide) (by decide)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x140f (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x10140f 0xba (by decide) 64
  case sub => exact codeRange_mem_of_drop (p := 0x10140a) 5 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1414 (by decide +kernel)
  md5_run_then sub_r64_r64_effect_step 0x101414 0x48 0xea
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10140a) 10 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1417 (by decide +kernel)
  md5_run_then mov_r64_r64_effect_step 0x101417 0x4d 0xf5
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10140a) 13 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x141a (by decide +kernel)
  md5_run_then sub_r64_r64_effect_step 0x10141a 0x49 0xd5
    (by unfold RexWPrefix; decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x10140a) 16 (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x141d (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [prefixEffect]
  · x86_norm [prefixEffect, position, stackPtr]
    simp [Operand.read, gprNumber, rexR, modrmReg]
  · intro i; cases i <;> x86_norm [prefixEffect, position, stackPtr]
    all_goals simp [Operand.read, gprNumber, rexR, modrmReg]
  · x86_norm [prefixEffect]

end Md5.Proofs.NewEntries.Reset.FirstUpdate


namespace Md5.Proofs.NewEntries.Reset.FirstUpdate

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

def entryEffect (s : RamState) : Effect :=
  { prefixEffect s with
    rip := if ((.reg 14 : Operand 64).read s).toNat < (64 - position s).toNat then
      0x1013d0 else 0x10141f
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem entry_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (LoadPre 0x10140a (fun s ↦ stackPtr s + 95) 1)
      Extracted.programImage entryEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x10140a prefixBytes) s :=
    program_text_slice hc 0x140a 19 (by decide +kernel)
  obtain ⟨fuel, u, ha, hu, _, he⟩ := entry_prepare boundary hOutside s hs hbytes hp
  have hcu := he.agrees.codeIn (by
    simp [prefixEffect, Effect.components, Component.Covers]) hc
  have hcf : condHolds 2 (StatusFlags.ofRFLAGS u.RFLAGS) =
      decide (((.reg 14 : Operand 64).read s).toNat < (64 - position s).toNat) :=
    he.flags.1
  have hnext : (jccEffect 0x10141d 2 2 ((0xb1#8).signExtend 64) u).rip =
      (entryEffect s).rip := by
    simp only [jccEffect, hcf, branchEffect, entryEffect, decide_eq_true_eq]
    split <;> rfl
  have hne : (entryEffect s).rip ≠ boundary.rip := by
    unfold entryEffect
    split
    · exact text_address_ne_return hOutside 0x13d0 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x141f (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x10141d [0x72, 0xb1]) u :=
    program_text_slice hcu 0x141d 2 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel8_effect_step 0x10141d 2 0xb1).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨fuel + 1, t, ha.trans hb, ht,
    hag.codeIn (by simp [Component.Covers]) hcu, heb.rip.trans hnext, ?_, by trivial, ?_⟩
  · change (.reg 5 : Operand 64).read t = _ ∧ (.reg 2 : Operand 64).read t = _ ∧
      (.reg 13 : Operand 64).read t = _
    exact ⟨(hag.read (by simp)).trans he.writes.1,
      (hag.read (by simp)).trans he.writes.2.1,
      (hag.read (by simp)).trans he.writes.2.2⟩
  · apply (he.agrees.trans hag).mono
    simp [prefixEffect, entryEffect, Effect.components]

def partialEffect (s : RamState) : Effect :=
  { rip := if (.reg 5 : Operand 64).read s = 0 then 0x1014b4 else 0x101428
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem partial_branch [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x10141f)
      Extracted.programImage partialEffect := by
  intro s hs hc hp
  have hbytes : CodeIn (codeRange 0x10141f [0x48, 0x85, 0xed]) s :=
    program_text_slice hc 0x141f 3 (by decide +kernel)
  have htest : StepEffect (fun s ↦ s.RIP = 0x10141f)
      (codeRange 0x10141f [0x48, 0x85, 0xed]) (testR64R64Effect 0x10141f 5 5) :=
    test_r64_r64_effect_step _ _ _ (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨u, ha, hu, he⟩ := htest.advances hs hbytes hp
    (text_address_ne_return hOutside 0x1422 (by decide +kernel))
  have hcu := he.codeIn (testR64R64Effect_avoids _ _ _ _ _) hc
  have hzf : condHolds 4 (StatusFlags.ofRFLAGS u.RFLAGS) =
      ((.reg 5 : Operand 64).read s == 0) := by
    have hz := he.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF =
      (((.reg 5 : Operand 64).read s &&& (.reg 5 : Operand 64).read s) == 0) at hz
    rw [BitVec.and_self] at hz
    exact hz
  have hnext : (jccEffect 0x101422 6 4 ((0x8c#32).signExtend 64) u).rip =
      (partialEffect s).rip := by
    simp only [jccEffect, hzf, branchEffect, partialEffect, beq_iff_eq]
    split <;> rfl
  have hne : (partialEffect s).rip ≠ boundary.rip := by
    unfold partialEffect
    split
    · exact text_address_ne_return hOutside 0x14b4 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1428 (by decide +kernel)
  have hbranch : CodeIn (codeRange 0x101422 [0x0f, 0x84, 0x8c, 0x00, 0x00, 0x00]) u :=
    program_text_slice hcu 0x1422 6 (by decide +kernel)
  obtain ⟨t, hb, ht, heb⟩ := (jcc_rel32_effect_step 0x101422 4 0x8c).advances
    hu hbranch ⟨he.rip, fun _ ↦ by decide +kernel⟩ (hnext ▸ hne)
  have hag : AgreesExcept [.rip] u t := heb.agrees
  refine ⟨2, t, ha.trans hb, ht, hag.codeIn (by simp [Component.Covers]) hcu,
    heb.rip.trans hnext, by trivial, by trivial, ?_⟩
  apply (he.agrees.trans hag).mono
  simp [partialEffect, testR64R64Effect, Effect.components]

end Md5.Proofs.NewEntries.Reset.FirstUpdate
