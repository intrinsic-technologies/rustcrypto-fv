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

def additionBytes : List UInt8 :=
  [72, 139, 132, 36, 160, 0, 0, 0, 72, 137, 68, 36, 32, 72, 139, 132, 36, 152, 0, 0, 0, 72, 137, 68, 36, 24, 72, 139, 132, 36, 136, 0, 0, 0, 72, 139, 140, 36, 144, 0, 0, 0, 72, 137, 76, 36, 16, 72, 137, 68, 36, 8, 76, 141, 172, 36, 72, 2, 0, 0, 72, 141, 116, 36, 8, 76, 137, 239, 76, 137, 250]

def additionEffect (s : RamState) : Effect :=
  { rip := 0x10609a
    writes := [
      ⟨(.reg 0 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 136) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 144) : Operand 64).read s⟩,
      ⟨(.reg 13 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 584)⟩,
      ⟨(.reg 6 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 8)⟩,
      ⟨(.reg 7 : Operand 64), ((Operand.reg 4 : Operand 64).read s + 584)⟩,
      ⟨(.reg 2 : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 136) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 144) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 152) : Operand 64).read s⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), (.mem ((Operand.reg 4 : Operand 64).read s + 160) : Operand 64).read s⟩] }

theorem addition_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    P256.Proofs.Common.Field.AdvanceTriple boundary (MovePre 0x106053 [136, 144, 152, 160] [8, 16, 24, 32])
      (codeRange 0x106053 additionBytes) (Effect.post additionEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x106053 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.readable 160 (by decide)⟩
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x605b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10605b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 32 (by decide)
    · x86_norm
      exact hP.codeApart 32 (by decide) 0x605b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 32 (by decide) 0x6053 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6060 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106060 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 152 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6068 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106068 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by decide)
    · x86_norm
      exact hP.codeApart 24 (by decide) 0x6068 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by decide) 0x6053 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x606d (by decide))
  advance_then (mov_r64_m64_effect_step 0x10606d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 136 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6075 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106075 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 144 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x607d (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10607d 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by decide)
    · x86_norm
      exact hP.codeApart 16 (by decide) 0x607d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by decide) 0x6053 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6082 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x106082 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by decide)
    · x86_norm
      exact hP.codeApart 8 (by decide) 0x6082 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by decide) 0x6053 71 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6087 (by decide))
  advance_then (lea_r64_effect_step 0x106087 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 584)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 52 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x608f (by decide))
  advance_then (lea_r64_effect_step 0x10608f 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 60 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6094 (by decide))
  advance_then (mov_r64_r64_effect_step 0x106094 0x4c 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 65 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6097 (by decide))
  advance_then (mov_r64_r64_effect_step 0x106097 0x4c 0xfa (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x106053 additionBytes 68 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x609a (by decide))
  advance_finish [additionEffect]


end Products
end P256.Proofs.Projective.Double
