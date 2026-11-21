import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash

open P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field P256.Proofs.Common.Instructions

attribute [local x86_compose] jmpEffect branchEffect

def setupBytes : List UInt8 :=
  [0x49,0x89,0xcc,0x49,0x89,0xd5,0x49,0xc1,0xe4,0x4,0x49,0x1,0xd4,0xeb,0x32]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10d63f
    writes := [⟨(.reg 12 : Operand 64), (s.regValue .rcx <<< 4) + s.regValue .rdx⟩,
      ⟨(.reg 13 : Operand 64), s.regValue .rdx⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem setup_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d5fe)
      (codeRange 0x10d5fe setupBytes) (Effect.post setupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10d5fe 0x49 0xcc (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xd601 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10d601 0x49 0xd5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d5fe setupBytes 3 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd604 (by decide))⟩
  advance_then (StepEffect.forgetFlags (h := shl_r64_imm8_effect_step 0x10d604 0x49 0xe4 4 (by simp [RexWPrefix]) rfl rfl))
  case sub => exact codeRange_slice_subset 0x10d5fe setupBytes 6 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers, Effect.forgetFlags, shlR64Effect, Effect.components, Write.component, Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd608 (by decide))⟩
  advance_then (StepEffect.forgetFlags (h := add_r64_r64_effect_step 0x10d608 0x49 0xd4 (by simp [RexWPrefix]) rfl))
  case sub => exact codeRange_slice_subset 0x10d5fe setupBytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers, Effect.forgetFlags, addR64R64Effect, Effect.components, Write.component, Operand.component]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd60b (by decide))⟩
  advance_then (jmp_rel8_effect_step 0x10d60b 0x32 (by decide))
  case sub => exact codeRange_slice_subset 0x10d5fe setupBytes 13 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem
      (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd63f (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [setupEffect, State.regValue, Operand.read_reg64]
  · x86_norm [setupEffect, State.regValue, Operand.read_reg64]
    exact ⟨rfl, rfl⟩
  · intro flag; cases flag <;> x86_norm [setupEffect]
  · x86_norm [setupEffect]

end P256.Proofs.Verifying.Message.Hash
