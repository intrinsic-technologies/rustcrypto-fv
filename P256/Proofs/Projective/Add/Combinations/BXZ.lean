import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def BXZBytes : List UInt8 :=
  [0x48, 0xb8, 0x34, 0x48, 0x87, 0x4, 0x1d, 0x6, 0x30, 0xdc, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0xb8, 0xd6, 0x2e, 0x21, 0xf7, 0xab, 0x20, 0xa2, 0xe5, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0xb8, 0x90, 0x30, 0x84, 0x78, 0xcd, 0x5, 0xf0, 0xac, 0x48, 0x89, 0x44, 0x24, 0x10, 0x4c, 0x89, 0x64, 0x24, 0x8, 0x4c, 0x8d, 0xac, 0x24, 0x28, 0x2, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x8, 0x4c, 0x89, 0xef, 0x48, 0x8d, 0x94, 0x24, 0x28, 0x1, 0x0, 0x0]

def BXZEffect (s : RamState) : Effect :=
  { rip := 0x10599b
    writes := [
      ⟨(Operand.reg 0 : Operand 64), 0xacf005cd78843090⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 296⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 552⟩,
      ⟨(Operand.reg 13 : Operand 64), (Operand.reg 4 : Operand 64).read s + 552⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), 0xacf005cd78843090⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), 0xe5a220abf7212ed6⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), 0xdc30061d04874834⟩] }

theorem BXZ_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x105951) (codeRange 0x105951 BXZBytes) (Effect.post BXZEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x105951 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xdc30061d04874834)
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x595b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10595b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.apart 32 (by decide) 0x595b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 (by decide) 0x5951 74 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5960 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x105960 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xe5a220abf7212ed6)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 15 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x596a (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10596a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x596a 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x5951 74 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x596f (by decide))
  advance_then (mov_r64_imm64_effect_step 0x10596f 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xacf005cd78843090)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 30 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5979 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105979 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 40 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x5979 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x5951 74 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x597e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10597e 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 45 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x597e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x5951 74 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5983 (by decide))
  advance_then (lea_r64_effect_step 0x105983 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 552)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 50 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x598b (by decide))⟩
  advance_then (lea_r64_effect_step 0x10598b 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 58 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5990 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105990 0x4c 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 63 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5993 (by decide))⟩
  advance_then (lea_r64_effect_step 0x105993 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105951 BXZBytes 66 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x599b (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [BXZEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [BXZEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [BXZEffect]
  · x86_norm [BXZEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
