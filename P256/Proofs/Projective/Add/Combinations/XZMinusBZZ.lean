import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def XZMinusBZZBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x40, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x84, 0x24, 0x38, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x84, 0x24, 0x28, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0x30, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8, 0x4c, 0x8d, 0xbc, 0x24, 0x88, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x8, 0x4c, 0x89, 0xff, 0x4c, 0x89, 0xf2]

def XZMinusBZZEffect (s : RamState) : Effect :=
  { rip := 0x105806
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 296) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 304) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 14 : Operand 64).read s⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 392⟩,
      ⟨(Operand.reg 15 : Operand 64), (Operand.reg 4 : Operand 64).read s + 392⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 296) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 304) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 312) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 320) : Operand 64).read s⟩] }

theorem XZMinusBZZ_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x1057bf) (codeRange 0x1057bf XZMinusBZZBytes) (Effect.post XZMinusBZZEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1057bf 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by decide) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 320 (by decide)⟩
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x57c7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1057c7 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.apart 32 (by decide) 0x57c7 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 (by decide) 0x57bf 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x57cc (by decide))
  advance_then (mov_r64_m64_effect_step 0x1057cc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 312)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 312 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x57d4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1057d4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x57d4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x57bf 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x57d9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1057d9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 296 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x57e1 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1057e1 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 304)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 304 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x57e9 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1057e9 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x57e9 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x57bf 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x57ee (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1057ee 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x57ee 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x57bf 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x57f3 (by decide))
  advance_then (lea_r64_effect_step 0x1057f3 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 392)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 52 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x57fb (by decide))⟩
  advance_then (lea_r64_effect_step 0x1057fb 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 60 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5800 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105800 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 65 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5803 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105803 0x4c 0xf2 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x1057bf XZMinusBZZBytes 68 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5806 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [XZMinusBZZEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [XZMinusBZZEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [XZMinusBZZEffect]
  · x86_norm [XZMinusBZZEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
