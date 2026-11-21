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

def y_productBytes : List UInt8 :=
  [72, 139, 132, 36, 96, 1, 0, 0, 72, 137, 68, 36, 32, 72, 139, 132, 36, 88, 1, 0, 0, 72, 137, 68, 36, 24, 72, 139, 132, 36, 72, 1, 0, 0, 72, 139, 140, 36, 80, 1, 0, 0, 72, 137, 76, 36, 16, 72, 137, 68, 36, 8, 76, 141, 188, 36, 104, 2, 0, 0, 72, 141, 84, 36, 8, 76, 137, 255, 76, 137, 238]

def y_productEffect (s : RamState) : Effect :=
  { rip := 0x1060e6
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 328) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 336) : Operand 64).read s⟩,
      ⟨(.reg 15 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 616)⟩,
      ⟨(.reg 2 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 8)⟩,
      ⟨(.reg 7 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 616)⟩,
      ⟨(.reg 6 : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 328) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 336) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 344) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 352) : Operand 64).read s⟩] }

theorem y_product_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    P256.Proofs.Common.Field.AdvanceTriple boundary (MovePre 0x10609f [328, 336, 344, 352] [8, 16, 24, 32])
      (codeRange 0x10609f y_productBytes) (Effect.post y_productEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x10609f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 352)) (by decide) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 352 (by decide)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x60a7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1060a7 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.codeApart 32 (by decide) 0x60a7 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by decide) 0x609f 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60ac (by decide))
  advance_then (mov_r64_m64_effect_step 0x1060ac 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 344)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 344 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60b4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1060b4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.codeApart 24 (by decide) 0x60b4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by decide) 0x609f 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60b9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1060b9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 328)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 328 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60c1 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1060c1 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 336)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 336 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60c9 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1060c9 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.codeApart 16 (by decide) 0x60c9 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by decide) 0x609f 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60ce (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1060ce 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.codeApart 8 (by decide) 0x60ce 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by decide) 0x609f 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60d3 (by decide))
  advance_then (lea_r64_effect_step 0x1060d3 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 616)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60db (by decide))
  advance_then (lea_r64_effect_step 0x1060db 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 60 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60e0 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1060e0 0x4c 0xff (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 65 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60e3 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1060e3 0x4c 0xee (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x10609f y_productBytes 68 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x60e6 (by decide))
  advance_finish [y_productEffect]


end Products
end P256.Proofs.Projective.Double
