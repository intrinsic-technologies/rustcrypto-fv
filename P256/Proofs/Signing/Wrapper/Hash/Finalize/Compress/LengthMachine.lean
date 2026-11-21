import P256.Proofs.Common.Field.SquareRoot.Exponent.Multiply.Shift
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

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.LengthMachine

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

def bytes : List UInt8 := [0x49,0xc1,0xe6,0x9,0xc1,0xe3,0x3,0x4c,0x9,0xf3,0x48,0xf,0xcb]

def effect (s : RamState) : Effect :=
  { rip := 0x10294a
    writes := [⟨(.reg 14 : Operand 64), (.reg 14 : Operand 64).read s <<< 9⟩,
      ⟨(.reg 3 : Operand 64), bswap64
        (((.reg 3 : Operand 32).read s <<< 3).setWidth 64 |||
          ((.reg 14 : Operand 64).read s <<< 9))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10293d bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x293d bytes
    (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10293d)
      (codeRange 0x10293d bytes) (Effect.post effect) := by
  advance_begin (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (P256.Proofs.Common.Instructions.ShiftLeft.shlR64Effect 0x10293d 4 14 9) from
      P256.Proofs.Common.Instructions.ShiftLeft.shl_r64_imm8_effect_step 0x10293d 0x49 0xe6 9 (by simp [RexWPrefix]) rfl rfl)))
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x2941 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shlR32Effect 0x102941 3 3 3) from
      P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shl_r32_imm8_effect_step 0x102941 0xe3 3 rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10293d bytes 4 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, P256.Proofs.Common.Field.SquareRoot.ExponentMultiply.shlR32Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2944 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (orR64R64Effect 0x102944 3 14) from
      or_r64_r64_effect_step 0x102944 0x4c 0xf3 (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10293d bytes 7 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, orR64R64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2947 (by decide))
  advance_then (bswap_r64_effect_step 0x102947 3)
  case sub => exact codeRange_slice_subset 0x10293d bytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x294a (by decide))
  advance_finish [effect]

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.LengthMachine
