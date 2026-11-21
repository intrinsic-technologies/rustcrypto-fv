import P256.Proofs.HMAC.Finalize.Length

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Length.Outer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Field.FieldNeg.Instructions (orR64R64Effect or_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft
open P256.Proofs.Common.Field.SquareRoot.ExponentMultiply (shlR32Effect)

attribute [local x86_compose] shlR32Effect shlR64Effect encodeBswapR64
attribute [local x86_local] Length.shift64_local Length.shift32_local

def bytes : List UInt8 := [0x49,0xc1,0xe5,9,0x41,0xc1,0xe4,3,0x4d,9,0xec,0x49,0x0f,0xcc]

def effect (s : RamState) : Effect :=
  { rip := 0x10134a
    writes := [⟨(.reg 13 : Operand 64), (.reg 13 : Operand 64).read s <<< 9⟩,
      ⟨(.reg 12 : Operand 64), bswap64
        (((.reg 12 : Operand 32).read s <<< 3).setWidth 64 |||
          ((.reg 13 : Operand 64).read s <<< 9))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10133c bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x133c bytes
    (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10133c)
      (codeRange 0x10133c bytes) (Effect.post effect) := by
  advance_begin (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (shlR64Effect 0x10133c 4 13 9) from
      shl_r64_imm8_effect_step 0x10133c 0x49 0xe5 9 (by simp [RexWPrefix]) rfl rfl)))
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x1340 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (shlR32Effect 0x101340 4 12 3) from
      shl_r32_imm8_rex_effect_step 0x101340 0x41 0xe4 3 (by simp [RexNoWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10133c bytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, shlR32Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1344 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (orR64R64Effect 0x101344 12 13) from
      or_r64_r64_effect_step 0x101344 0x4d 0xec (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10133c bytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, orR64R64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1347 (by decide))
  advance_then (bswap_r64_effect_step 0x101347 12)
  case sub => exact codeRange_slice_subset 0x10133c bytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x134a (by decide))
  advance_finish [effect]

end P256.Proofs.HMAC.Finalize.Length.Outer
