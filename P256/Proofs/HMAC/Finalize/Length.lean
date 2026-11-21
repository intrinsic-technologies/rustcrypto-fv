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

namespace P256.Proofs.HMAC.Finalize.Length

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program
open P256.Proofs.Common
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Field.FieldNeg.Instructions (orR64R64Effect or_r64_r64_effect_step)
open P256.Proofs.Common.Instructions.ShiftLeft
open P256.Proofs.Common.Field.SquareRoot.ExponentMultiply (shlR32Effect)

attribute [local x86_compose] shlR32Effect shlR64Effect encodeBswapR64

@[local x86_local] theorem shift64_local (p : BitVec 64) (n : Nat) (r : BitVec 5) (c : Nat) :
    Effect.Local (fun s => Common.Instructions.Effect.forgetFlags (shlR64Effect p n r c s)) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Common.Instructions.Effect.forgetFlags, shlR64Effect, h.read_reg]
  · intro s
    simp [Common.Instructions.Effect.forgetFlags, shlR64Effect, Write.Full, Operand.Full]

@[local x86_local] theorem shift32_local (p : BitVec 64) (n : Nat) (r : BitVec 5) (c : Nat) :
    Effect.Local (fun s => Common.Instructions.Effect.forgetFlags (shlR32Effect p n r c s)) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Common.Instructions.Effect.forgetFlags, shlR32Effect, h.read_reg]
  · intro s
    simp [Common.Instructions.Effect.forgetFlags, shlR32Effect, Write.Full, Operand.Full]

def bytes : List UInt8 := [0x48,0xc1,0xe5,9,0x41,0xc1,0xe5,3,0x49,9,0xed,0x49,0x0f,0xcd]

def effect (s : RamState) : Effect :=
  { rip := 0x1010ac
    writes := [⟨(.reg 5 : Operand 64), (.reg 5 : Operand 64).read s <<< 9⟩,
      ⟨(.reg 13 : Operand 64), bswap64
        (((.reg 13 : Operand 32).read s <<< 3).setWidth 64 |||
          ((.reg 5 : Operand 64).read s <<< 9))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

 theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10109e bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x109e bytes
    (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10109e)
      (codeRange 0x10109e bytes) (Effect.post effect) := by
  advance_begin (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (shlR64Effect 0x10109e 4 5 9) from
      shl_r64_imm8_effect_step 0x10109e 0x48 0xe5 9 (by simp [RexWPrefix]) rfl rfl)))
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x10a2 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (shlR32Effect 0x1010a2 4 13 3) from
      shl_r32_imm8_rex_effect_step 0x1010a2 0x41 0xe5 3 (by simp [RexNoWPrefix]) rfl rfl)))
  case sub => exact codeRange_slice_subset 0x10109e bytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, shlR32Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a6 (by decide))
  advance_then (StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (orR64R64Effect 0x1010a6 13 5) from
      or_r64_r64_effect_step 0x1010a6 0x49 0xed (by simp [RexWPrefix]) rfl)))
  case sub => exact codeRange_slice_subset 0x10109e bytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Common.Instructions.Effect.forgetFlags, orR64R64Effect, Effect.components,
        Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10a9 (by decide))
  advance_then (bswap_r64_effect_step 0x1010a9 13)
  case sub => exact codeRange_slice_subset 0x10109e bytes 11 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [bswapR64Effect, Effect.components, Write.component, Operand.component, Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x10ac (by decide))
  advance_finish [effect]

end P256.Proofs.HMAC.Finalize.Length
