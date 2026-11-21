import Sha2.Proofs.Common.Instructions.ForgetFlags
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.SHA256.Absorb.Direct
import Sha2.Proofs.Common.Instructions.CrossPageStore.Mov
import Sha2.Proofs.Common.Instructions.ByteStore
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.SHA256.Absorb.Direct (Stage)

def bytes : Stage → List UInt8
  | .select => [0x49,0x83,0xfe,0x3f,0x77,0x1b]
  | .smallSetup => [0x48,0x8d,0xbc,0x24,0xa8,0,0,0,0x4c,0x89,0xf2]
  | .smallStore => [0x44,0x88,0xb4,0x24,0xe7,0,0,0,0xeb,0x4c]
  | .bulkSetup => [0x48,0x8d,0xbc,0x24,0xe8,0,0,0,0x4c,0x89,0xf2,0x48,0xc1,0xea,6,
      0x49,0xbf,0xc0,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x4d,0x21,0xf7,
      0x41,0x83,0xe6,0x3f,0x49,1,0xf7,0x48,0x89,0x94,0x24,8,1,0,0]
  | .bulkTail => [0x44,0x88,0xb4,0x24,0xe7,0,0,0]
  | .tailSetup => [0x48,0x8d,0xbc,0x24,0xa8,0,0,0,0x4c,0x89,0xfe,0x4c,0x89,0xf2]

def effect (p : BitVec 64) (stage : Stage) (s : RamState) : Effect :=
  match stage with
  | .select =>
      { rip := if (s.regValue .r14).toNat ≤ 63 then p + 6 else p + 33,
        flags := some ⟨none,none,none,none,none,none⟩ }
  | .smallSetup =>
      { rip := p + 11, writes := [
      ⟨(.reg 7 : Operand 64), rspOf s + 168⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r14⟩] }
  | .smallStore =>
      { rip := p + 86, writes := [
      ⟨(.mem (rspOf s + 231) : Operand 8), (s.regValue .r14).setWidth 8⟩] }
  | .bulkSetup =>
      { rip := p + 43, writes := [
      ⟨(.reg 7 : Operand 64), rspOf s + 232⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r14 >>> 6⟩,
      ⟨(.reg 15 : Operand 64), s.regValue .rsi + (s.regValue .r14 &&& 0x7fffffffffffffc0)⟩,
      ⟨(.reg 14 : Operand 64), ((s.regValue .r14).setWidth 32 &&& 63).setWidth 64⟩,
      ⟨(.mem (rspOf s + 264) : Operand 64), s.regValue .r14 >>> 6⟩],
        flags := some ⟨none,none,none,none,none,none⟩ }
  | .bulkTail =>
      { rip := p + 8, writes := [
      ⟨(.mem (rspOf s + 231) : Operand 8), (s.regValue .r14).setWidth 8⟩] }
  | .tailSetup =>
      { rip := p + 14, writes := [
      ⟨(.reg 7 : Operand 64), rspOf s + 168⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r15⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .r14⟩] }

structure Pre (p : BitVec 64) (stage : Stage) (s : RamState) : Prop where
  rip : s.RIP = p
  tailWritable : MemWritable s (rspOf s + 231) 1
  counterWritable : CrossPageStore.Writable s (rspOf s + 264) 8
  tailApart : RangeApart (rspOf s + 231) 1 p (bytes stage).length
  counterApart : RangeApart (rspOf s + 264) 8 p (bytes stage).length

theorem smallSetup_run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes .smallSetup).length) :
    AdvanceTriple boundary (Pre p .smallSetup) (codeRange p (bytes .smallSetup))
      (Effect.post (effect p .smallSetup)) := by
  advance_reloc_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 11 (by decide)))
  advance_finish [effect]

theorem tailSetup_run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes .tailSetup).length) :
    AdvanceTriple boundary (Pre p .tailSetup) (codeRange p (bytes .tailSetup))
      (Effect.post (effect p .tailSetup)) := by
  advance_reloc_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xfe (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 11 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 11) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 14 (by decide)))
  advance_finish [effect]

theorem bulkTail_run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes .bulkTail).length) :
    AdvanceTriple boundary (Pre p .bulkTail) (codeRange p (bytes .bulkTail))
      (Effect.post (effect p .bulkTail)) := by
  advance_reloc_begin (mov_m8_r8_effect_step p 0x44 (by simp [RexPrefix]) 6
    (.sib 4 none 0 (.d32 231)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_finish [effect]

set_option maxHeartbeats 600000 in
theorem bulkSetup_run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes .bulkSetup).length) :
    AdvanceTriple boundary (Pre p .bulkSetup) (codeRange p (bytes .bulkSetup))
      (Effect.post (effect p .bulkSetup)) := by
  advance_reloc_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_reloc_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xf2 (by simp [RexWPrefix]) rfl)
    next (boundary_ne_program outside (inside 11 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := shr_r64_imm8_effect_step
    (p + 11) 0x48 0xea 6 (by simp [RexWPrefix]) rfl rfl))
    next (boundary_ne_program outside (inside 15 (by decide)))
  advance_reloc_then (mov_r64_imm64_effect_step (p + 15) 0x49 0xbf
    (by simp [RexWPrefix]) (by decide) 0x7fffffffffffffc0)
    next (boundary_ne_program outside (inside 25 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := and_r64_r64_effect_step
    (p + 25) 0x4d 0xf7 (by simp [RexWPrefix]) rfl))
    next (boundary_ne_program outside (inside 28 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := and_r32_imm8_rex_effect_step
    (p + 28) 0x41 0xe6 63 (by simp [RexNoWPrefix]) rfl rfl))
    next (boundary_ne_program outside (inside 32 (by decide)))
  advance_reloc_then (StepEffect.forgetFlags (h := add_r64_r64_effect_step
    (p + 32) 0x49 0xf7 (by simp [RexWPrefix]) rfl))
    next (boundary_ne_program outside (inside 35 (by decide)))
  advance_reloc_then (CrossPageStore.mov_m64_r64_effect_step_any (p + 35) 0x48
    (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 264)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 43 (by decide)))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    refine ⟨rfl, ?_, rfl, rfl⟩
    exact (BitVec.add_comm _ _).trans (congrArg (· + _) (BitVec.and_comm _ _))
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

theorem smallStore_run [Bindings] (p : BitVec 64) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes .smallStore).length)
    (target : InProgram (p + 86)) :
    AdvanceTriple boundary (Pre p .smallStore) (codeRange p (bytes .smallStore))
      (Effect.post (effect p .smallStore)) := by
  have low : (branchTarget (p + 8) 2 ((76 : BitVec 8).signExtend 64)).toNat < 2^32 := by
    obtain ⟨byte, mem⟩ := target
    have bound := programSections_low.codeLow (_, byte) mem
    simpa [branchTarget, BitVec.add_assoc, Prelude.userAddressLimit] using bound
  advance_reloc_begin (mov_m8_r8_effect_step p 0x44 (by simp [RexPrefix]) 6
    (.sib 4 none 0 (.d32 231)) (by decide) rfl rfl)
    next (boundary_ne_program outside (inside 8 (by decide)))
  advance_reloc_then (jmp_rel8_effect_step (p + 8) 76 low)
    next (boundary_ne_program outside target)
  advance_finish [effect]

end Sha2.Proofs.Common.SHA256.Blocks.Digest.Absorb
