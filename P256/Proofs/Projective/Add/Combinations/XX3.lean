import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def XX3Bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x60, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x44, 0x24, 0x58, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x48, 0x48, 0x8b, 0x4c, 0x24, 0x50, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8, 0x4c, 0x8d, 0xbc, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x4c, 0x89, 0xff, 0x4c, 0x89, 0xf6]

def XX3Effect (s : RamState) : Effect :=
  { rip := 0x105ad5
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 72) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 80) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩,
      ⟨(Operand.reg 15 : Operand 64), (Operand.reg 4 : Operand 64).read s + 136⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 72) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 80) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 88) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 96) : Operand 64).read s⟩] }

theorem XX3_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x105a9a) (codeRange 0x105a9a XX3Bytes) (Effect.post XX3Effect) := by
  advance_begin (mov_r64_m64_effect_step 0x105a9a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 96 (by decide)⟩
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5a9f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105a9f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.apart 32 (by decide) 0x5a9f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 (by decide) 0x5a9a 59 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5aa4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105aa4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 88 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5aa9 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105aa9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x5aa9 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x5a9a 59 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5aae (by decide))
  advance_then (mov_r64_m64_effect_step 0x105aae 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 72 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ab3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105ab3 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 80 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ab8 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105ab8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x5ab8 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x5a9a 59 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5abd (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105abd 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 35 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x5abd 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x5a9a 59 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ac2 (by decide))
  advance_then (lea_r64_effect_step 0x105ac2 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 40 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5aca (by decide))⟩
  advance_then (lea_r64_effect_step 0x105aca 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 48 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5acf (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105acf 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 53 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5ad2 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105ad2 0x4c 0xf6 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105a9a XX3Bytes 56 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5ad5 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [XX3Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [XX3Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [XX3Effect]
  · x86_norm [XX3Effect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
