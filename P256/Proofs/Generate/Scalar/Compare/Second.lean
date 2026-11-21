import P256.Proofs.Generate.Scalar.Compare.Common
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
  X86Proofs

def secondWordBytes : List UInt8 :=
  [0x48, 0xbe, 0x7c, 0x61, 0xe8, 0x58, 0x52, 0x5, 0x19, 0x43, 0x4c, 0x1, 0xe6, 0x48, 0x1, 0xd6,
    0x4c, 0x89, 0xe2, 0x48, 0xf7, 0xd2, 0x48, 0x9, 0xf2, 0x48, 0xc1, 0xea, 0x3f]

def secondWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 12 : Operand 64).read s
  let r := 0x4319055258e8617c + x + (Operand.reg 2 : Operand 64).read s
  { rip := 0x112f49
    writes := [⟨(Operand.reg 6 : Operand 64), r⟩,
      ⟨(Operand.reg 2 : Operand 64), (~~~x ||| r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem second_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x112f2c)
      (codeRange 0x112f2c secondWordBytes) (Effect.post secondWordEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x112f2c 0x48 0xbe (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel) 0x4319055258e8617c)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12f36 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x112f36 0x4c 0xe6 (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f2c secondWordBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f39 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x112f39 0x48 0xd6 (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f2c secondWordBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f3c (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x112f3c 0x4c 0xe2 (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f2c secondWordBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f3f (by decide +kernel))
  advance_then (not_r64_effect_step 0x112f3f 0x48 0xd2 (by unfold RexWPrefix; decide +kernel) rfl
    rfl)
  case sub => exact codeRange_slice_subset 0x112f2c secondWordBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f42 (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x112f42 0x48 0xf2 (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f2c secondWordBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f45 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x112f45 0x48 0xea 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f2c secondWordBytes 25 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f49 (by decide +kernel))
  advance_finish [secondWordEffect, stackPtr, BitVec.add_zero]

end P256.Proofs.Generate.Scalar
