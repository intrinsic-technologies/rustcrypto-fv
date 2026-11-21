import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple

open P256.Proofs.Common.Field (AdvanceTriple)

set_option autoImplicit false

open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.SquareRoot.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def parameterSetupBytes : List UInt8 :=
  [0x4c,0x8d,0x84,0x24,0xe0,0x0,0x0,0x0,0xb9,0xe,0x0,0x0,0x0,0x4c,0x89,0xc7,0x48,0xc7,0xc6,0x28,0x2f,0x20,0x0]

def parameterSetupEffect (s : RamState) : Effect :=
  { rip := 0x114468
    writes := [⟨(Operand.reg 8 : Operand 64), (Operand.reg 4 : Operand 64).read s + 224⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 224⟩,
      ⟨(Operand.reg 1 : Operand 64), 14⟩,
      ⟨(Operand.reg 6 : Operand 64), 0x202f28⟩] }

theorem parameter_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x114451)
      (codeRange 0x114451 parameterSetupBytes) (Effect.post parameterSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x114451 0x4c (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d32 224)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x14459 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x114459 0xb9 (by decide +kernel) 14)
  case sub => exact codeRange_slice_subset 0x114451 parameterSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1445e (by decide))
  advance_then (mov_r64_r64_effect_step 0x11445e 0x4c 0xc7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x114451 parameterSetupBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14461 (by decide))
  advance_then (mov_r64_imm32_effect_step 0x114461 0x48 0xc6
    (by simp [RexWPrefix]) rfl rfl 0x202f28)
  case sub => exact codeRange_slice_subset 0x114451 parameterSetupBytes 16 7
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14468 (by decide))
  advance_finish [parameterSetupEffect]

def exponentSetupBytes : List UInt8 :=
  [0x4c,0x8d,0xb4,0x24,0x50,0x1,0x0,0x0,0x48,0x8d,0xb4,0x24,0xc0,0x0,0x0,0x0,0x4c,0x89,0xf7,0x48,0xc7,0xc2,0xb8,0x2f,0x20,0x0,0xb9,0xfe,0x0,0x0,0x0]

def exponentSetupEffect (s : RamState) : Effect :=
  { rip := 0x11448a
    writes := [⟨(Operand.reg 14 : Operand 64), (Operand.reg 4 : Operand 64).read s + 336⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 192⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 336⟩,
      ⟨(Operand.reg 2 : Operand 64), 0x202fb8⟩,
      ⟨(Operand.reg 1 : Operand 64), 254⟩] }

theorem exponent_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x11446b)
      (codeRange 0x11446b exponentSetupBytes) (Effect.post exponentSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x11446b 0x4c (by simp [RexWPrefix])
    6 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x14473 (by decide))
  advance_then (lea_r64_effect_step 0x114473 0x48 (by simp [RexWPrefix])
    6 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11446b exponentSetupBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1447b (by decide))
  advance_then (mov_r64_r64_effect_step 0x11447b 0x4c 0xf7 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11446b exponentSetupBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1447e (by decide))
  advance_then (mov_r64_imm32_effect_step 0x11447e 0x48 0xc2
    (by simp [RexWPrefix]) rfl rfl 0x202fb8)
  case sub => exact codeRange_slice_subset 0x11446b exponentSetupBytes 19 7
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14485 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x114485 0xb9 (by decide +kernel) 254)
  case sub => exact codeRange_slice_subset 0x11446b exponentSetupBytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1448a (by decide))
  advance_finish [exponentSetupEffect]

end P256.Proofs.Sec1.SquareRoot.Prepare
