import P256.Proofs.Field.Inverse.Tail.Support
import P256.Proofs.Common.Instructions.MovzxByte
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

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Field.Inverse.SecondArguments

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def selectSetupBytes : List UInt8 :=
  [0x48,0x89,0xe7,0x48,0x8d,0x54,0x24,0x28,0xbe,0x4,0x0,0x0,0x0,0xb9,0x4,0x0,0x0,0x0,0x41,0x89,0xe8]

def selectSetupEffect (s : RamState) : Effect :=
  { rip := 0x1141ff
    writes := [⟨(Operand.reg 7 : Operand 64), (Operand.reg 4 : Operand 64).read s⟩,
      ⟨(Operand.reg 2 : Operand 64), (Operand.reg 4 : Operand 64).read s+40⟩,
      ⟨(Operand.reg 6 : Operand 64),4⟩,⟨(Operand.reg 1 : Operand 64),4⟩,
      ⟨(Operand.reg 8 : Operand 64), ((Operand.reg 5 : Operand 64).read s).setWidth 32 |>.setWidth 64⟩] }

theorem select_setup_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1141ea selectSetupBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x141ea selectSetupBytes
    (by decide +kernel) (by decide +kernel)

theorem select_setup [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP=0x1141ea) (codeRange 0x1141ea selectSetupBytes)
      (Effect.post selectSetupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1141ea 0x48 0xe7 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x141ed (by decide))
  advance_then (lea_r64_effect_step 0x1141ed 0x48 (by simp [RexWPrefix])
    2 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1141ea selectSetupBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141f2 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1141f2 0xbe (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x1141ea selectSetupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141f7 (by decide))
  advance_then (mov_r32_imm32_effect_step 0x1141f7 0xb9 (by decide +kernel) 4)
  case sub => exact codeRange_slice_subset 0x1141ea selectSetupBytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141fc (by decide))
  advance_then (mov_r32_r32_rex_effect_step 0x1141fc 0x41 0xe8 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1141ea selectSetupBytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem; simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x141ff (by decide))
  advance_finish [selectSetupEffect]

end P256.Proofs.Field.Inverse.SecondArguments
