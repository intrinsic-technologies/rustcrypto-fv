import X86Proofs.Instructions.Lea.Triple
import P256.Proofs.Projective.Add.CrossTerms.Memory
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def yyPlusXYSetupBytes : List UInt8 :=
  [0x48, 0x8d, 0xac, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x48, 0x89, 0xef]

def yyPlusXYSetupEffect (s : RamState) : Effect :=
  { rip := 0x105b6d
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩, ⟨(.reg 5 : Operand 64), (Operand.reg 4 : Operand 64).read s + 552⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 552⟩] }

theorem yyPlusXY_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105b58)
      (codeRange 0x105b58 yyPlusXYSetupBytes) (Effect.post yyPlusXYSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105b58 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 552)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5b60 (by decide))
  advance_then (lea_r64_effect_step 0x105b60 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105b58 yyPlusXYSetupBytes 8 5
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5b65 (by decide))
  advance_then (lea_r64_effect_step 0x105b65 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105b58 yyPlusXYSetupBytes 13 5
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5b6a (by decide))
  advance_then (mov_r64_r64_effect_step 0x105b6a 0x48 0xef (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105b58 yyPlusXYSetupBytes 18 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5b6d (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [yyPlusXYSetupEffect]
  · x86_norm [yyPlusXYSetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [yyPlusXYSetupEffect]
  · x86_norm [yyPlusXYSetupEffect]

def yzBXZ3SetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x28, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xf7]

def yzBXZ3SetupEffect (s : RamState) : Effect :=
  { rip := 0x105bef
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩, ⟨(.reg 14 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩] }

theorem yzBXZ3_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105bda)
      (codeRange 0x105bda yzBXZ3SetupBytes) (Effect.post yzBXZ3SetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105bda 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5be2 (by decide))
  advance_then (lea_r64_effect_step 0x105be2 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105bda yzBXZ3SetupBytes 8 5
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5be7 (by decide))
  advance_then (lea_r64_effect_step 0x105be7 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105bda yzBXZ3SetupBytes 13 5
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5bec (by decide))
  advance_then (mov_r64_r64_effect_step 0x105bec 0x4c 0xf7 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105bda yzBXZ3SetupBytes 18 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5bef (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [yzBXZ3SetupEffect]
  · x86_norm [yzBXZ3SetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [yzBXZ3SetupEffect]
  · x86_norm [yzBXZ3SetupEffect]

def xSetupBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x8, 0x48, 0x89, 0xee, 0x4c, 0x89, 0xf2]

def xSetupEffect (s : RamState) : Effect :=
  { rip := 0x105bff
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩] }

theorem x_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105bf4)
      (codeRange 0x105bf4 xSetupBytes) (Effect.post xSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105bf4 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5bf9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105bf9 0x48 0xee (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105bf4 xSetupBytes 5 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5bfc (by decide))
  advance_then (mov_r64_r64_effect_step 0x105bfc 0x4c 0xf2 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105bf4 xSetupBytes 8 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5bff (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [xSetupEffect]
  · x86_norm [xSetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [xSetupEffect]
  · x86_norm [xSetupEffect]

def yyPlusMinusSetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0xb4, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xf7, 0x48, 0x8d, 0xb4, 0x24, 0x68, 0x1, 0x0, 0x0]

def yyPlusMinusSetupEffect (s : RamState) : Effect :=
  { rip := 0x105c73
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 360⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩, ⟨(.reg 14 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩] }

theorem yyPlusMinus_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105c5b)
      (codeRange 0x105c5b yyPlusMinusSetupBytes) (Effect.post yyPlusMinusSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105c5b 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5c63 (by decide))
  advance_then (lea_r64_effect_step 0x105c63 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c5b yyPlusMinusSetupBytes 8 5
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c68 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105c68 0x4c 0xf7 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105c5b yyPlusMinusSetupBytes 13 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c6b (by decide))
  advance_then (lea_r64_effect_step 0x105c6b 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 360)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c5b yyPlusMinusSetupBytes 16 8
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c73 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [yyPlusMinusSetupEffect]
  · x86_norm [yyPlusMinusSetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [yyPlusMinusSetupEffect]
  · x86_norm [yyPlusMinusSetupEffect]

def xxMinusBXZ3SetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0x7c, 0x24, 0x28, 0x48, 0x8d, 0x74, 0x24, 0x8, 0x4c, 0x89, 0xff, 0x4c, 0x89, 0xe2]

def xxMinusBXZ3SetupEffect (s : RamState) : Effect :=
  { rip := 0x105cbc
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 12 : Operand 64).read s⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩, ⟨(.reg 15 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩] }

theorem xxMinusBXZ3_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105cac)
      (codeRange 0x105cac xxMinusBXZ3SetupBytes) (Effect.post xxMinusBXZ3SetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105cac 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5cb1 (by decide))
  advance_then (lea_r64_effect_step 0x105cb1 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cac xxMinusBXZ3SetupBytes 5 5
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cb6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105cb6 0x4c 0xff (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105cac xxMinusBXZ3SetupBytes 10 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cb9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105cb9 0x4c 0xe2 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105cac xxMinusBXZ3SetupBytes 13 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cbc (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [xxMinusBXZ3SetupEffect]
  · x86_norm [xxMinusBXZ3SetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [xxMinusBXZ3SetupEffect]
  · x86_norm [xxMinusBXZ3SetupEffect]

def ySetupBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x8, 0x4c, 0x89, 0xf6, 0x4c, 0x89, 0xfa]

def ySetupEffect (s : RamState) : Effect :=
  { rip := 0x105ccc
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩] }

theorem y_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105cc1)
      (codeRange 0x105cc1 ySetupBytes) (Effect.post ySetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105cc1 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5cc6 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105cc6 0x4c 0xf6 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105cc1 ySetupBytes 5 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cc9 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105cc9 0x4c 0xfa (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105cc1 ySetupBytes 8 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ccc (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [ySetupEffect]
  · x86_norm [ySetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [ySetupEffect]
  · x86_norm [ySetupEffect]

def yyMinusYZSetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0x74, 0x24, 0x28, 0x4c, 0x89, 0xf7, 0x48, 0x8d, 0xb4, 0x24, 0x48, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x94, 0x24, 0x8, 0x1, 0x0, 0x0]

def yyMinusYZSetupEffect (s : RamState) : Effect :=
  { rip := 0x105d0d
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 264⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 328⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩, ⟨(.reg 14 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩] }

theorem yyMinusYZ_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105cf5)
      (codeRange 0x105cf5 yyMinusYZSetupBytes) (Effect.post yyMinusYZSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105cf5 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5cfa (by decide))
  advance_then (mov_r64_r64_effect_step 0x105cfa 0x4c 0xf7 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105cf5 yyMinusYZSetupBytes 5 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cfd (by decide))
  advance_then (lea_r64_effect_step 0x105cfd 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cf5 yyMinusYZSetupBytes 8 8
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d05 (by decide))
  advance_then (lea_r64_effect_step 0x105d05 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cf5 yyMinusYZSetupBytes 16 8
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d0d (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [yyMinusYZSetupEffect]
  · x86_norm [yyMinusYZSetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [yyMinusYZSetupEffect]
  · x86_norm [yyMinusYZSetupEffect]

def xyXXMinusSetupBytes : List UInt8 :=
  [0x4c, 0x8d, 0x7c, 0x24, 0x8, 0x4c, 0x89, 0xff, 0x48, 0x8d, 0xb4, 0x24, 0xe8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xea]

def xyXXMinusSetupEffect (s : RamState) : Effect :=
  { rip := 0x105d25
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 232⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩, ⟨(.reg 15 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩] }

theorem xyXXMinus_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105d12)
      (codeRange 0x105d12 xyXXMinusSetupBytes) (Effect.post xyXXMinusSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105d12 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5d17 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105d17 0x4c 0xff (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105d12 xyXXMinusSetupBytes 5 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d1a (by decide))
  advance_then (lea_r64_effect_step 0x105d1a 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105d12 xyXXMinusSetupBytes 8 8
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d22 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105d22 0x4c 0xea (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105d12 xyXXMinusSetupBytes 16 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d25 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [xyXXMinusSetupEffect]
  · x86_norm [xyXXMinusSetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [xyXXMinusSetupEffect]
  · x86_norm [xyXXMinusSetupEffect]

def zSetupBytes : List UInt8 :=
  [0x48, 0x8d, 0xbc, 0x24, 0x88, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xf6, 0x4c, 0x89, 0xfa]

def zSetupEffect (s : RamState) : Effect :=
  { rip := 0x105d38
    writes := [⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩, ⟨(.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩, ⟨(.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩] }

theorem z_setup_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x105d2a)
      (codeRange 0x105d2a zSetupBytes) (Effect.post zSetupEffect) := by
  advance_begin (lea_r64_effect_step 0x105d2a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5d32 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105d32 0x4c 0xf6 (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105d2a zSetupBytes 8 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d35 (by decide))
  advance_then (mov_r64_r64_effect_step 0x105d35 0x4c 0xfa (by simp [RexWPrefix]) (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x105d2a zSetupBytes 11 3
  case mid =>
    intro s t _ hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d38 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [zSetupEffect]
  · x86_norm [zSetupEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [zSetupEffect]
  · x86_norm [zSetupEffect]

theorem execute_registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {bytes : List UInt8} {E : RamState → Effect}
    (state : FrameState s t 96 920 632)
    (block : AdvanceTriple boundary
      (fun t => t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post E))
    (bound : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (noMem : ∀ c ∈ (E t).components, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ (E t).components)
    (hdf : Component.df ∉ (E t).components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ (E t).components := by component_not_mem)
    (hfcw : Component.fcw ∉ (E t).components := by component_not_mem) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      (E t).Holds t u ∧ u.external = t.external := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bound code) rip
  exact ⟨fuel, u, run, state.after_registers ready effect.agrees noMem sp,
    effect, effect.agrees.external noMem⟩

end P256.Proofs.Projective.Add.Output
