import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def BZZBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x8b, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x4c, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0xb8, 0x34, 0x48, 0x87, 0x4, 0x1d, 0x6, 0x30, 0xdc, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0xb8, 0xd6, 0x2e, 0x21, 0xf7, 0xab, 0x20, 0xa2, 0xe5, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0xb8, 0x90, 0x30, 0x84, 0x78, 0xcd, 0x5, 0xf0, 0xac, 0x48, 0x89, 0x44, 0x24, 0x10, 0x49, 0xbc, 0xdf, 0xbd, 0xc4, 0x29, 0x62, 0xdf, 0x9c, 0xd8, 0x4c, 0x89, 0x64, 0x24, 0x8, 0x4c, 0x8d, 0xb4, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x8, 0x48, 0x8d, 0x54, 0x24, 0x28, 0x4c, 0x89, 0xf7]

def BZZEffect (s : RamState) : Effect :=
  { rip := 0x1057ba
    writes := [
      ⟨(Operand.reg 0 : Operand 64), 0xacf005cd78843090⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 112) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 40⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩,
      ⟨(Operand.reg 12 : Operand 64), 0xd89cdf6229c4bddf⟩,
      ⟨(Operand.reg 14 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), 0xd89cdf6229c4bddf⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), 0xacf005cd78843090⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), 0xe5a220abf7212ed6⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), 0xdc30061d04874834⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 40) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 104) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 48) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 112) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 56) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 120) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 64) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 128) : Operand 64).read s⟩] }

theorem BZZ_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x10573e) (codeRange 0x10573e BZZBytes) (Effect.post BZZEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10573e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 128 (by decide)⟩
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5746 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105746 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by decide)
    · x86_norm
      exact hP.apart 64 (by decide) 0x5746 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 64 (by decide) 0x573e 124 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x574b (by decide))
  advance_then (mov_r64_m64_effect_step 0x10574b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 120 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5750 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105750 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by decide)
    · x86_norm
      exact hP.apart 56 (by decide) 0x5750 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 56 (by decide) 0x573e 124 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5755 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105755 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 104 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x575a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10575a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 112 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x575f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10575f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 33 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by decide)
    · x86_norm
      exact hP.apart 48 (by decide) 0x575f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 48 (by decide) 0x573e 124 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5764 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105764 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 38 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by decide)
    · x86_norm
      exact hP.apart 40 (by decide) 0x5764 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 40 (by decide) 0x573e 124 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5769 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x105769 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xdc30061d04874834)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 43 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5773 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105773 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 53 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.apart 32 (by decide) 0x5773 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 (by decide) 0x573e 124 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5778 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x105778 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xe5a220abf7212ed6)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 58 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5782 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105782 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 68 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x5782 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x573e 124 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5787 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x105787 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0xacf005cd78843090)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 73 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5791 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105791 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 83 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x5791 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x573e 124 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5796 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x105796 0x49 0xbc (by simp [RexWPrefix]) (by decide) 0xd89cdf6229c4bddf)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 88 10
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x57a0 (by decide))⟩
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1057a0 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 98 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x57a0 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x573e 124 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x57a5 (by decide))
  advance_then (lea_r64_effect_step 0x1057a5 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 103 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x57ad (by decide))⟩
  advance_then (lea_r64_effect_step 0x1057ad 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 111 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x57b2 (by decide))⟩
  advance_then (lea_r64_effect_step 0x1057b2 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 116 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x57b7 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1057b7 0x4c 0xf7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10573e BZZBytes 121 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x57ba (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [BZZEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [BZZEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [BZZEffect]
  · x86_norm [BZZEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
