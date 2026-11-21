import P256.Proofs.Verifying.Core.Digest.Finish.Arguments
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open P256.Proofs.Common.Field (AdvanceTriple)

def reduceArgumentBytes : List UInt8 :=
  [0x48,0x89,0xe3,0x48,0x8d,0xb4,0x24,0x80,0x0,0x0,0x0,0x48,0x89,0xdf]

def reduceArgumentEffect (s : RamState) : Effect :=
  { rip := 0x10e157
    writes := [⟨(.reg 3 : Operand 64),rspOf s⟩,
      ⟨(.reg 6 : Operand 64),rspOf s+128⟩,⟨(.reg 7 : Operand 64),rspOf s⟩] }

theorem reduce_arguments_block [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e149)
      (codeRange 0x10e149 reduceArgumentBytes) (Effect.post reduceArgumentEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10e149 0x48 0xe3 (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xe14c (by decide))
  advance_then (lea_r64_effect_step 0x10e14c 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10e149 reduceArgumentBytes 3 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),?_,?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe154 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e154 0x48 0xdf (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e149 reduceArgumentBytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),?_,?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe157 (by decide))
  advance_finish [reduceArgumentEffect]

def equalArgumentBytes : List UInt8 := [0x48,0x8d,0xbc,0x24,0xc0,0x2,0x0,0x0,0x48,0x89,0xde]

def equalArgumentEffect (s : RamState) : Effect :=
  { rip := 0x10e167
    writes := [⟨(.reg 7 : Operand 64),rspOf s+704⟩,
      ⟨(.reg 6 : Operand 64),s.regValue .rbx⟩] }

theorem equal_arguments_block [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10e15c)
      (codeRange 0x10e15c equalArgumentBytes) (Effect.post equalArgumentEffect) := by
  advance_begin (lea_r64_effect_step 0x10e15c 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 704)) (by decide) rfl rfl)
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xe164 (by decide))
  advance_then (mov_r64_r64_effect_step 0x10e164 0x48 0xde (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10e15c equalArgumentBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm),?_,?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xe167 (by decide))
  advance_finish [equalArgumentEffect]

end P256.Proofs.Verifying.Core.Finish.Tail
