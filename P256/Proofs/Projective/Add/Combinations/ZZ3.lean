import P256.Proofs.Projective.Add.Combinations.Setup

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def ZZ3Bytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x44, 0x24, 0x78, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x68, 0x48, 0x8b, 0x4c, 0x24, 0x70, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8, 0x48, 0x8d, 0xac, 0x24, 0xc8, 0x1, 0x0, 0x0, 0x48, 0x8d, 0x54, 0x24, 0x8, 0x48, 0x89, 0xef, 0x4c, 0x89, 0xee]

def ZZ3Effect (s : RamState) : Effect :=
  { rip := 0x10594c
    writes := [
      ⟨(Operand.reg 0 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 104) : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 112) : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s + 8⟩,
      ⟨(Operand.reg 5 : Operand 64), (Operand.reg 4 : Operand 64).read s + 456⟩,
      ⟨(Operand.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s + 456⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 104) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 112) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 120) : Operand 64).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (Operand.mem ((Operand.reg 4 : Operand 64).read s + 128) : Operand 64).read s⟩] }

theorem ZZ3_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (SetupPre 0x10590e) (codeRange 0x10590e ZZ3Bytes) (Effect.post ZZ3Effect) := by
  advance_begin (mov_r64_m64_effect_step 0x10590e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl)
  case pre => intro s hP; exact ⟨hP.rip, hP.readable 128 (by decide)⟩
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x5916 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105916 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.apart 32 (by decide) 0x5916 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 32 (by decide) 0x590e 62 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x591b (by decide))
  advance_then (mov_r64_m64_effect_step 0x10591b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 120 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5920 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105920 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.apart 24 (by decide) 0x5920 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 (by decide) 0x590e 62 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5925 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105925 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 104 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x592a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10592a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 28 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 112 (by decide)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x592f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10592f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 33 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.apart 16 (by decide) 0x592f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 (by decide) 0x590e 62 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5934 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105934 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 38 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.apart 8 (by decide) 0x5934 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 (by decide) 0x590e 62 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5939 (by decide))
  advance_then (lea_r64_effect_step 0x105939 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 456)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 43 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5941 (by decide))⟩
  advance_then (lea_r64_effect_step 0x105941 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 51 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5946 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105946 0x48 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 56 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x5949 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x105949 0x4c 0xee (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10590e ZZ3Bytes 59 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x594c (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [ZZ3Effect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [ZZ3Effect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [ZZ3Effect]
  · x86_norm [ZZ3Effect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Add.Combinations
