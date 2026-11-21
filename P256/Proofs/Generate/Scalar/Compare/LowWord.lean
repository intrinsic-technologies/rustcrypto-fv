import P256.Proofs.Generate.Scalar.Compare.Common

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
  X86Proofs

def lowWordBytes : List UInt8 :=
  [0x48, 0xb8, 0xaf, 0xda, 0x9c, 0x3, 0x3d, 0x35, 0x46, 0xc, 0x4c, 0x1, 0xe8, 0x4c, 0x89, 0xe9,
    0x48, 0xf7, 0xd1, 0x48, 0x9, 0xc1, 0x48, 0xc1, 0xe9, 0x3f]

def lowWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 13 : Operand 64).read s
  { rip := 0x112f15
    writes := [⟨(Operand.reg 0 : Operand 64), 0x0c46353d039cdaaf + x⟩,
      ⟨(Operand.reg 1 : Operand 64), (~~~x ||| (0x0c46353d039cdaaf + x)) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem low_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x112efb)
      (codeRange 0x112efb lowWordBytes) (Effect.post lowWordEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x112efb 0x48 0xb8
    (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0x0c46353d039cdaaf)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12f05 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x112f05 0x4c 0xe8
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x112efb lowWordBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f08 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x112f08 0x4c 0xe9
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x112efb lowWordBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f0b (by decide +kernel))
  advance_then (not_r64_effect_step 0x112f0b 0x48 0xd1
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112efb lowWordBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f0e (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x112f0e 0x48 0xc1
    (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x112efb lowWordBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f11 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x112f11 0x48 0xe9 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112efb lowWordBytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f15 (by decide +kernel))
  advance_finish [lowWordEffect]

end P256.Proofs.Generate.Scalar
