import P256.Proofs.Common.Instructions.ShiftLeft.Register32
import P256.Proofs.Common.Instructions.Bswap
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.LengthMachine

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Field.FieldNeg.Instructions (orR64R64Effect or_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft

attribute [local x86_compose] P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shlR32Effect P256.Proofs.Common.Instructions.ShiftLeft.shlR64Effect encodeBswapR64

@[local x86_local] theorem shift32_local (p : BitVec 64) (n : Nat) (r : BitVec 5) (c : Nat) :
    Effect.Local (fun s => Common.Instructions.Effect.forgetFlags (P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shlR32Effect p n r c s)) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Common.Instructions.Effect.forgetFlags, P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shlR32Effect, h.read_reg]
  · intro s
    simp [Common.Instructions.Effect.forgetFlags, P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shlR32Effect, Write.Full, Operand.Full]

def bytes : List UInt8 := [0x49,0xc1,0xe4,0x9,0x41,0xc1,0xe7,0x3,0x4d,0x9,0xe7,0x49,0xf,0xcf]

def effect (s : RamState) : Effect :=
  { rip := 0x10d857
    writes := [⟨(.reg 12 : Operand 64), (.reg 12 : Operand 64).read s <<< 9⟩,
      ⟨(.reg 15 : Operand 64), bswap64
        (((.reg 15 : Operand 32).read s <<< 3).setWidth 64 |||
          ((.reg 12 : Operand 64).read s <<< 9))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d849 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd849 bytes
    (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10d849)
      (codeRange 0x10d849 bytes) (Effect.post effect) := by
  advance_begin (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (P256.Proofs.Common.Instructions.ShiftLeft.shlR64Effect 0x10d849 4 12 9) from
      P256.Proofs.Common.Instructions.ShiftLeft.shl_r64_imm8_effect_step 0x10d849 0x49 0xe4 9 (by simp [RexWPrefix]) rfl rfl)))
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd84d (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shlR32Effect 0x10d84d 4 15 3) from
      P256.Proofs.Common.Instructions.ShiftLeft.shl_r32_imm8_rex_effect_step 0x10d84d 0x41 0xe7 3 (by simp [RexNoWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10d849 bytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shlR32Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd851 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (orR64R64Effect 0x10d851 15 12) from
      or_r64_r64_effect_step 0x10d851 0x4d 0xe7 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10d849 bytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, orR64R64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd854 (by decide))
  advance_then (bswap_r64_effect_step 0x10d854 15)
  case sub => exact codeRange_slice_subset 0x10d849 bytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd857 (by decide))
  advance_finish [effect]

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.LengthMachine
