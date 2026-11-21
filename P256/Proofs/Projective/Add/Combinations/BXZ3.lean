import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def BXZ3Bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x0, 0x2, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x84, 0x24, 0xf8, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x84, 0x24, 0xe8, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0xf0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8, 0x4c, 0x8d, 0xa4, 0x24, 0x8, 0x2, 0x0, 0x0, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xe7, 0x4c, 0x89, 0xee]

def BXZ3Effect (s : RamState) : Effect :=
  { rip := 0x105a83
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 488) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 496) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 520⟩,
      ⟨(Operand.reg 12 : Operand 64), (Operand.reg 4 : Operand 64).read s + 520⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 488) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 496) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 504) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 512) : Operand 64).read s⟩] }

theorem BXZ3_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x105a3c) (codeRange 0x105a3c BXZ3Bytes) (Effect.post BXZ3Effect) := by
  advance_begin (mov_r64_m64_effect_step 0x105a3c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 512)) (by decide) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 512 (by decide)⟩
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5a44 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105a44 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.apart 32 (by decide) 0x5a44 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 (by decide) 0x5a3c 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5a49 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105a49 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 504)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 504 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5a51 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105a51 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x5a51 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x5a3c 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5a56 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105a56 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 488)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 488 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5a5e (by decide))
  advance_then (mov_r64_m64_effect_step 0x105a5e 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 496)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 496 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5a66 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105a66 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x5a66 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x5a3c 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5a6b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105a6b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x5a6b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x5a3c 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5a70 (by decide))
  advance_then (lea_r64_effect_step 0x105a70 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 520)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 52 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a78 (by decide))⟩
  advance_then (lea_r64_effect_step 0x105a78 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 60 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a7d (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105a7d 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 65 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a80 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105a80 0x4c 0xee (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a3c BXZ3Bytes 68 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5a83 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [BXZ3Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [BXZ3Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [BXZ3Effect]
  · x86_norm [BXZ3Effect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
