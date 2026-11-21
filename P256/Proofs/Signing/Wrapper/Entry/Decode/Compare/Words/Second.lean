import P256.Proofs.Signing.Wrapper.Entry.Decode.Compare.Borrow
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Signing.Wrapper.Entry.Decode.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def secondWordBytes : List UInt8 :=
  [72, 190, 124, 97, 232, 88, 82, 5, 25, 67, 76, 1, 246, 72, 1, 214, 76, 137, 242, 72, 247, 210, 72, 9, 242, 72, 193, 234, 63]

def secondWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 14 : Operand 64).read s
  let r := 0x4319055258e8617c + x + (Operand.reg 2 : Operand 64).read s
  { rip := 0x1024f0
    writes := [⟨(Operand.reg 6 : Operand 64), r⟩,
      ⟨(Operand.reg 2 : Operand 64), (~~~x ||| r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem second_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1024d3)
      (codeRange 0x1024d3 secondWordBytes) (Effect.post secondWordEffect) := by
  advance_begin (mov_r64_imm64_effect_step 0x1024d3 0x48 0xbe (by unfold RexWPrefix; decide +kernel) (by decide +kernel) 0x4319055258e8617c)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x24dd (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x1024dd 0x4c 0xf6 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x1024d3 secondWordBytes 10 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24e0 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x1024e0 0x48 0xd6 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x1024d3 secondWordBytes 13 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24e3 (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x1024e3 0x4c 0xf2 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x1024d3 secondWordBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24e6 (by decide +kernel))
  advance_then (not_r64_effect_step 0x1024e6 0x48 0xd2 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024d3 secondWordBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24e9 (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x1024e9 0x48 0xf2 (by unfold RexWPrefix; decide +kernel) rfl)
  case sub => exact codeRange_slice_subset 0x1024d3 secondWordBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24ec (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x1024ec 0x48 0xea 63 (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1024d3 secondWordBytes 25 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x24f0 (by decide +kernel))
  advance_finish [secondWordEffect, stackPtr, BitVec.add_zero]

end P256.Proofs.Signing.Wrapper.Entry.Decode.Compare
