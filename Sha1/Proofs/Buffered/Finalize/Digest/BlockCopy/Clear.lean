import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Tactics

namespace Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

def clearBytes : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0,
    0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x28, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x30,
    0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x38, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44,
    0x24, 0x40, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x48, 0x0, 0x0, 0x0, 0x0]

def clearEffect (s : RamState) : Effect :=
  { rip := 0x1001f2
    writes := [
      ⟨(.mem (stackPtr s + 24) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 32) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 40) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 48) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 56) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 64) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 72) : Operand 64), 0⟩] }

macro "digest_clear_store " pc:num ", " off:term ", " dst:term : tactic => do
  let pcOffset := Lean.quote (pc.getNat - 0x100000)
  let nextOffset := Lean.quote (pc.getNat + 9 - 0x100000)
  `(tactic| (
  md5_run_then (Common.Instructions.MovStore.mov_m64_imm32_effect_step $pc 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 $dst)) (by decide) (by decide)
    (by decide) 0)
  case sub => exact codeRange_mem_of_drop (p := 0x1001b3) $off (by decide +kernel)
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
      change RangeApart (stackPtr t + $dst) 8 0x1001b3 63
      rw [hsp]
      exact h.toStorage.stackApart (offset := $dst) (len := 8)
        (codeOffset := 0x1b3) (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return (by assumption) $nextOffset (by decide +kernel)))

set_option maxRecDepth 1024 in
set_option maxHeartbeats 1000000 in
theorem clear_execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (PartPre 0x1001b3) (codeRange 0x1001b3 clearBytes) clearEffect := by
  unfold clearBytes
  md5_run_begin (Common.Instructions.MovStore.mov_m64_imm32_effect_step 0x1001b3 0x48
    (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 24)) (by decide) (by decide)
    (by decide) 0)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · x86_norm
      exact h.toStorage.stackWritable 24 8 (by decide)
    · x86_norm
      exact h.toStorage.stackApart (offset := 24) (len := 8)
        (codeOffset := 0x1b3) (by decide) (by decide +kernel)
  case av =>
    intro s h
    apply Effect.avoids_of_components_mem_rip (movM64Imm32Effect_components _ _ _ _)
    x86_norm
    change RangeApart (stackPtr s + 24) 8 0x1001b3 63
    exact h.toStorage.stackApart (offset := 24) (len := 8)
      (codeOffset := 0x1b3) (by decide) (by decide +kernel)
  case boundary =>
    intro _ _
    exact text_address_ne_return hOutside 0x1bc (by decide +kernel)
  digest_clear_store 0x1001bc, 9, 32
  digest_clear_store 0x1001c5, 18, 40
  digest_clear_store 0x1001ce, 27, 48
  digest_clear_store 0x1001d7, 36, 56
  digest_clear_store 0x1001e0, 45, 64
  digest_clear_store 0x1001e9, 54, 72
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [clearEffect]
  · x86_norm [clearEffect, stackPtr]
    all_goals simp [Operand.read]
  · intro i; cases i <;> x86_norm [clearEffect]
  · x86_norm [clearEffect, stackPtr]
    all_goals simp [Operand.read]

end Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy
