import P256.Proofs.Generate.Scalar.Compare.Common
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sarR64Effect_components sar_r64_imm8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
  X86Proofs

def highWordBytes : List UInt8 :=
  [0x48, 0x89, 0x74, 0x24, 0x8, 0x48, 0x2b, 0x4c, 0x24, 0x8, 0x48, 0xc1, 0xf9, 0x3f, 0x4c, 0x89,
    0xf2, 0x48, 0xf7, 0xd2, 0x48, 0xbe, 0x0, 0x0, 0x0, 0x0, 0x1, 0x0, 0x0, 0x0, 0x4c, 0x1, 0xf6,
    0x48, 0x1, 0xce, 0x48, 0x9, 0xd6, 0x48, 0xc1, 0xee, 0x3f]

def highWordEffect (s : RamState) : Effect :=
  let x := (Operand.reg 14 : Operand 64).read s
  let c := ((Operand.reg 1 : Operand 64).read s - (Operand.reg 6 : Operand 64).read s).sshiftRight
    63
  { rip := 0x112f97
    writes := [⟨(Operand.mem (stackPtr s + 8) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(Operand.reg 1 : Operand 64), c⟩,
      ⟨(Operand.reg 2 : Operand 64), ~~~x⟩,
      ⟨(Operand.reg 6 : Operand 64), (0x100000000 + x + c ||| ~~~x) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem high_word_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ComparePre 0x112f6c)
      (codeRange 0x112f6c highWordBytes) (Effect.post highWordEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x112f6c 0x48 (by unfold RexWPrefix; decide +kernel) 6
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · change MemWritable s (stackPtr s + 8#64) 8
      exact h.writable
    · change RangeApart (stackPtr s + 8#64) 8 0x112f6c 5
      have ha := h.apart 0x12f6c 5 (by decide +kernel)
      change RangeApart (stackPtr s + 8) 8 (0x112f6c : BitVec 64) 5 at ha
      exact ha
  case av =>
    intro s h
    apply h.avoids_code 0x12f6c highWordBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12f71 (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x112f71 0x48 (by unfold RexWPrefix; decide +kernel) 1 (.sib
    4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm [BitVec.add_zero]
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f76 (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x112f76 0x48 0xf9 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 10 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components , Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f7a (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x112f7a 0x4c 0xf2 (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 14 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f7d (by decide +kernel))
  advance_then (not_r64_effect_step 0x112f7d 0x48 0xd2 (by unfold RexWPrefix; decide +kernel) rfl
    rfl)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 17 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f80 (by decide +kernel))
  advance_then (mov_r64_imm64_effect_step 0x112f80 0x48 0xbe (by unfold RexWPrefix; decide +kernel)
    (by decide +kernel) 0x100000000)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 20 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f8a (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x112f8a 0x4c 0xf6 (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 30 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f8d (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x112f8d 0x48 0xce (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 33 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f90 (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x112f90 0x48 0xd6 (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 36 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f93 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x112f93 0x48 0xee 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f6c highWordBytes 39 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f97 (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [highWordEffect, stackPtr, BitVec.add_zero]
    repeat' constructor
  · intro i
    cases i <;> x86_norm [highWordEffect]
  · x86_norm [highWordEffect, stackPtr, BitVec.add_zero]
    rfl

end P256.Proofs.Generate.Scalar
