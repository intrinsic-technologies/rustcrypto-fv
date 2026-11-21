import P256.Proofs.Signing.Core.Initialize.Memory
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

attribute [local x86_compose] jmpEffect branchEffect branchTarget

structure LoopSetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x10ca7b
  writable : MemWritable s (stackPtr s + 96) 8
  codeApart : ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + 96) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def loopSetupBytes : List UInt8 :=
  [76, 137, 100, 36, 96, 72, 141, 92, 36, 40, 76, 141, 172, 36, 176, 1, 0, 0, 76, 141, 188, 36, 48, 5, 0, 0, 235, 14]

def loopSetupEffect (s : RamState) : Effect :=
  { rip := 0x10caa5
    writes := [⟨(.mem (stackPtr s + 96) : Operand 64), s.regValue .r12⟩,
      ⟨(.reg 3 : Operand 64), stackPtr s + 40⟩,
      ⟨(.reg 13 : Operand 64), stackPtr s + 432⟩,
      ⟨(.reg 15 : Operand 64), stackPtr s + 1328⟩] }

theorem loop_setup_correct [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoopSetupPre (codeRange 0x10ca7b loopSetupBytes)
      (Effect.post loopSetupEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x10ca7b 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.codeApart 0xca7b 5 (by decide)⟩
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    exact h.codeApart 0xca7b 28 (by decide)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0xca80 (by decide))
  advance_then (lea_r64_effect_step 0x10ca80 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ca7b loopSetupBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xca85 (by decide))
  advance_then (lea_r64_effect_step 0x10ca85 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d32 432)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ca7b loopSetupBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xca8d (by decide))
  advance_then (lea_r64_effect_step 0x10ca8d 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 1328)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10ca7b loopSetupBytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xca95 (by decide))
  advance_then (jmp_rel8_effect_step 0x10ca95 0x0e (by decide))
  case sub => exact codeRange_slice_subset 0x10ca7b loopSetupBytes 26 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    exact boundary_ne_program outside (inProgram_of_textOffset 0xcaa5 (by decide))
  advance_finish [loopSetupEffect, jmpEffect, stackPtr, Operand.read_reg64, gprNumber,
    rexR, rexB, modrmReg, modrmRm, UInt8.toBitVec]

end P256.Proofs.Signing.Core.Initialize
