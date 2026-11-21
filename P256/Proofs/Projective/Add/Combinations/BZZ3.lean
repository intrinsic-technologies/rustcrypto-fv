import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def BZZ3Bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xa0, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x84, 0x24, 0x98, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x84, 0x24, 0x88, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0x90, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8, 0x4c, 0x8d, 0xac, 0x24, 0xa8, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xef, 0x4c, 0x89, 0xf6]

def BZZ3Effect (s : RamState) : Effect :=
  { rip := 0x105862
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 392) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 400) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 424⟩,
      ⟨(Operand.reg 13 : Operand 64), (Operand.reg 4 : Operand 64).read s + 424⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 392) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 400) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 408) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 416) : Operand 64).read s⟩] }

theorem BZZ3_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x10581b) (codeRange 0x10581b BZZ3Bytes) (Effect.post BZZ3Effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10581b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 416)) (by decide) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 416 (by decide)⟩
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5823 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105823 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.apart 32 (by decide) 0x5823 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 (by decide) 0x581b 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5828 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105828 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 408)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 408 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5830 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105830 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x5830 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x581b 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5835 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105835 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 392)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 392 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x583d (by decide))
  advance_then (mov_r64_m64_effect_step 0x10583d 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 400)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 400 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5845 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105845 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x5845 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x581b 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x584a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10584a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x584a 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x581b 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x584f (by decide))
  advance_then (lea_r64_effect_step 0x10584f 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 424)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 52 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5857 (by decide))⟩
  advance_then (lea_r64_effect_step 0x105857 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 60 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x585c (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10585c 0x4c 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 65 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x585f (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x10585f 0x4c 0xf6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10581b BZZ3Bytes 68 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5862 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [BZZ3Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [BZZ3Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [BZZ3Effect]
  · x86_norm [BZZ3Effect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
