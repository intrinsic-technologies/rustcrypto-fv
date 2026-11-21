import P256.Proofs.Projective.Double.Products.Pre
import P256.Proofs.Projective.Double.Values
import P256.Proofs.Program.FieldCall.Binary
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Projective.Double

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall
open P256.Proofs.Field X86 X86.Machine X86.UserProcess X86Proofs

namespace Products

def subtractionBytes : List UInt8 :=
  [72, 139, 132, 36, 160, 0, 0, 0, 72, 137, 68, 36, 64, 72, 139, 132, 36, 152, 0, 0, 0, 72, 137, 68, 36, 56, 72, 139, 132, 36, 136, 0, 0, 0, 72, 139, 140, 36, 144, 0, 0, 0, 72, 137, 76, 36, 48, 72, 137, 68, 36, 40, 72, 139, 132, 36, 64, 1, 0, 0, 72, 137, 68, 36, 32, 72, 139, 132, 36, 56, 1, 0, 0, 72, 137, 68, 36, 24, 72, 139, 132, 36, 40, 1, 0, 0, 72, 139, 140, 36, 48, 1, 0, 0, 72, 137, 76, 36, 16, 72, 137, 68, 36, 8, 76, 141, 164, 36, 72, 1, 0, 0, 72, 141, 116, 36, 40, 72, 141, 84, 36, 8, 76, 137, 231]

def subtractionEffect (s : RamState) : Effect :=
  { rip := 0x10604e
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 296) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 304) : Operand 64).read s⟩,
      ⟨(.reg 12 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 328)⟩,
      ⟨(.reg 6 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 40)⟩,
      ⟨(.reg 2 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 8)⟩,
      ⟨(.reg 7 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 328)⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 296) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 304) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 312) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 320) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 40) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 136) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 48) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 144) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 56) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 152) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 64) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 160) : Operand 64).read s⟩] }

theorem subtraction_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    P256.Proofs.Common.Field.AdvanceTriple boundary (MovePre 0x105fd1 [136, 144, 152, 160, 296, 304, 312, 320] [8, 16, 24, 32, 40, 48, 56, 64])
      (codeRange 0x105fd1 subtractionBytes) (Effect.post subtractionEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x105fd1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 160 (by decide)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5fd9 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105fd9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by decide)
    · x86_norm
      exact hP.codeApart 64 (by decide) 0x5fd9 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 (by decide) 0x5fd1 125 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5fde (by decide))
  advance_then (mov_r64_m64_effect_step 0x105fde 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 152 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5fe6 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105fe6 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by decide)
    · x86_norm
      exact hP.codeApart 56 (by decide) 0x5fe6 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by decide) 0x5fd1 125 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5feb (by decide))
  advance_then (mov_r64_m64_effect_step 0x105feb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ff3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105ff3 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ffb (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105ffb 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by decide)
    · x86_norm
      exact hP.codeApart 48 (by decide) 0x5ffb 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by decide) 0x5fd1 125 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6000 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106000 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by decide)
    · x86_norm
      exact hP.codeApart 40 (by decide) 0x6000 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by decide) 0x5fd1 125 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6005 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106005 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 320)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 320 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x600d (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10600d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 60 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.codeApart 32 (by decide) 0x600d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by decide) 0x5fd1 125 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6012 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106012 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 312)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 65 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 312 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x601a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10601a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 73 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.codeApart 24 (by decide) 0x601a 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by decide) 0x5fd1 125 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x601f (by decide))
  advance_then (mov_r64_m64_effect_step 0x10601f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 296)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 78 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 296 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6027 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106027 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 304)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 86 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 304 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x602f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10602f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 94 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.codeApart 16 (by decide) 0x602f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by decide) 0x5fd1 125 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6034 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106034 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 99 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.codeApart 8 (by decide) 0x6034 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by decide) 0x5fd1 125 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6039 (by decide))
  advance_then (lea_r64_effect_step 0x106039 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 328)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 104 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6041 (by decide))
  advance_then (lea_r64_effect_step 0x106041 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 112 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6046 (by decide))
  advance_then (lea_r64_effect_step 0x106046 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 117 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x604b (by decide))
  advance_then (mov_r64_r64_effect_step 0x10604b 0x4c 0xe7 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x105fd1 subtractionBytes 122 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x604e (by decide))
  advance_finish [subtractionEffect]


end Products
end P256.Proofs.Projective.Double
