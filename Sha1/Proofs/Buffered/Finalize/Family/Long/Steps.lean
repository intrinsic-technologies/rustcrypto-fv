import Sha1.Proofs.Buffered.Finalize.Steps

namespace Sha1.Proofs.Buffered.Finalize.Family.Long

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.Finalize.Steps (PartPre)

def highCopyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x58, 0x48, 0x89, 0x84, 0x24, 0xb8, 0x0, 0x0, 0x0,
    0x48, 0x8b, 0x44, 0x24, 0x50, 0x48, 0x89, 0x84, 0x24, 0xb0, 0x0, 0x0, 0x0,
    0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x89, 0x84, 0x24, 0xa8, 0x0, 0x0, 0x0,
    0x48, 0x8b, 0x44, 0x24, 0x40, 0x48, 0x89, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0]

def highCopyEffect (s : RamState) : Effect :=
  { rip := 0x101e69
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 64) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), (.mem (stackPtr s + 88) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), (.mem (stackPtr s + 80) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 168) : Operand 64), (.mem (stackPtr s + 72) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 160) : Operand 64), (.mem (stackPtr s + 64) : Operand 64).read s⟩] }

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem highCopy_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .updateFinalizeCopy 0x101e35)
      (codeRange 0x101e35 highCopyBytes) highCopyEffect := by
  unfold highCopyBytes
  md5_run_begin (mov_r64_m64_effect_step 0x101e35 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 88)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 88 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1e3a (by decide +kernel)
  storage_copy_store Kind.updateFinalizeCopy, 0x101e3a, 0x101e35, 52, 5,
    0x48, 0, 184, (.sib 4 none 0 (.d32 184)), 8
  storage_copy_load Kind.updateFinalizeCopy, 0x101e42, 0x101e35, 13, 0, 80
  storage_copy_store Kind.updateFinalizeCopy, 0x101e47, 0x101e35, 52, 18,
    0x48, 0, 176, (.sib 4 none 0 (.d32 176)), 8
  storage_copy_load Kind.updateFinalizeCopy, 0x101e4f, 0x101e35, 26, 0, 72
  storage_copy_store Kind.updateFinalizeCopy, 0x101e54, 0x101e35, 52, 31,
    0x48, 0, 168, (.sib 4 none 0 (.d32 168)), 8
  storage_copy_load Kind.updateFinalizeCopy, 0x101e5c, 0x101e35, 39, 0, 64
  storage_copy_store Kind.updateFinalizeCopy, 0x101e61, 0x101e35, 52, 44,
    0x48, 0, 160, (.sib 4 none 0 (.d32 160)), 8
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [highCopyEffect]
  · x86_norm [highCopyEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [highCopyEffect]
  · x86_norm [highCopyEffect, stackPtr]
    all_goals simp [Operand.read]

def lowCopyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x38, 0x48, 0x89, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0,
    0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x84, 0x24, 0x90, 0x0, 0x0, 0x0,
    0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x4c, 0x24, 0x28, 0x48, 0x89, 0x8c,
    0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0]

def lowCopyEffect (s : RamState) : Effect :=
  { rip := 0x101e9d
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 32) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 40) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 152) : Operand 64), (.mem (stackPtr s + 56) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 144) : Operand 64), (.mem (stackPtr s + 48) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 136) : Operand 64), (.mem (stackPtr s + 40) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 128) : Operand 64), (.mem (stackPtr s + 32) : Operand 64).read s⟩] }

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem lowCopy_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .updateFinalizeCopy 0x101e69)
      (codeRange 0x101e69 lowCopyBytes) lowCopyEffect := by
  unfold lowCopyBytes
  md5_run_begin (mov_r64_m64_effect_step 0x101e69 0x48 (by unfold RexWPrefix; decide)
    0 (.sib 4 none 0 (.d8 56)) (by decide) (by decide) (by decide))
  case pre =>
    intro s h
    exact ⟨h.rip, (h.toStorage.stackWritable 56 8 (by decide)).readable⟩
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1e6e (by decide +kernel)
  storage_copy_store Kind.updateFinalizeCopy, 0x101e6e, 0x101e69, 52, 5,
    0x48, 0, 152, (.sib 4 none 0 (.d32 152)), 8
  storage_copy_load Kind.updateFinalizeCopy, 0x101e76, 0x101e69, 13, 0, 48
  storage_copy_store Kind.updateFinalizeCopy, 0x101e7b, 0x101e69, 52, 18,
    0x48, 0, 144, (.sib 4 none 0 (.d32 144)), 8
  storage_copy_load Kind.updateFinalizeCopy, 0x101e83, 0x101e69, 26, 0, 32
  storage_copy_load Kind.updateFinalizeCopy, 0x101e88, 0x101e69, 31, 1, 40
  storage_copy_store Kind.updateFinalizeCopy, 0x101e8d, 0x101e69, 52, 36,
    0x48, 1, 136, (.sib 4 none 0 (.d32 136)), 8
  storage_copy_store Kind.updateFinalizeCopy, 0x101e95, 0x101e69, 52, 44,
    0x48, 0, 128, (.sib 4 none 0 (.d32 128)), 8
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [lowCopyEffect]
  · x86_norm [lowCopyEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [lowCopyEffect]
  · x86_norm [lowCopyEffect, stackPtr]
    all_goals simp [Operand.read]

def clearBytes : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24,
    0x28, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x30, 0x0, 0x0, 0x0,
    0x0, 0x48, 0xc7, 0x44, 0x24, 0x38, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44,
    0x24, 0x40, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x48, 0x0, 0x0,
    0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x50, 0x0, 0x0, 0x0, 0x0]

def clearEffect (s : RamState) : Effect :=
  { rip := 0x101ef3
    writes := [
      ⟨(.mem (stackPtr s + 32) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 48) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 80) : Operand 64), 0⟩] }

macro "family_clear_store " pc:num ", " off:term ", " dst:term : tactic => do
  let pcOffset := Lean.quote (pc.getNat - 0x100000)
  let nextOffset := Lean.quote (pc.getNat + 9 - 0x100000)
  `(tactic| (
  md5_run_then (Common.Instructions.MovStore.mov_m64_imm32_effect_step $pc 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 $dst)) (by decide) (by decide)
    (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x101eb4) $off (by decide +kernel)
  case mid =>
    intro s t h hE hO
    have hsp : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
    refine ⟨storePre_of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable $dst 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := $pcOffset) (by decide) (by decide +kernel)
    · apply Effect.avoids_of_components_mem_rip (movM64Imm32Effect_components _ _ _ _)
      x86_norm
      change RangeApart (stackPtr t + $dst) 8 0x101eb4 63
      rw [hsp]
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := 0x1eb4) (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem clear_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre .updateFinalizeCopy 0x101eb4) (codeRange 0x101eb4 clearBytes) clearEffect := by
  unfold clearBytes
  md5_run_begin (Common.Instructions.MovStore.mov_m64_imm32_effect_step 0x101eb4 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 32)) (by decide) (by decide)
    (by decide) 0)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 32 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 32) (len := 8)
        (codeOffset := 0x1eb4) (by decide) (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_of_components_mem_rip (movM64Imm32Effect_components _ _ _ _)
    x86_norm
    change RangeApart (stackPtr s + 32) 8 0x101eb4 63
    exact h.toStorage.stackApart (offset := 32) (len := 8)
      (codeOffset := 0x1eb4) (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1ebd (by decide +kernel)
  family_clear_store 0x101ebd, 9, 40
  family_clear_store 0x101ec6, 18, 48
  family_clear_store 0x101ecf, 27, 56
  family_clear_store 0x101ed8, 36, 64
  family_clear_store 0x101ee1, 45, 72
  family_clear_store 0x101eea, 54, 80
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [clearEffect]
  · x86_norm [clearEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [clearEffect]
  · x86_norm [clearEffect, stackPtr]
    all_goals simp [Operand.read]

end Sha1.Proofs.Buffered.Finalize.Family.Long
