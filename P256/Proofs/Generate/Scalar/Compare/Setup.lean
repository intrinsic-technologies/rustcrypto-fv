import P256.Proofs.Generate.Scalar.Compare.Common
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

def setupBytes : List UInt8 :=
  [0x48, 0x89, 0x4c, 0x24, 0x8, 0x48, 0x8d, 0x44, 0x24, 0x8, 0x31, 0xd2, 0x48, 0x2b, 0x54, 0x24,
    0x8, 0x31, 0xc9, 0x48, 0xc1, 0xfa, 0x3f]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x112f2c
    writes := [⟨(Operand.mem (stackPtr s + 8) : Operand 64), (Operand.reg 1 : Operand 64).read s⟩,
      ⟨(Operand.reg 0 : Operand 64), stackPtr s + 8⟩,
      ⟨(Operand.reg 1 : Operand 64), 0⟩,
      ⟨(Operand.reg 2 : Operand 64), (-((Operand.reg 1 : Operand 64).read s)).sshiftRight 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem setup_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ComparePre 0x112f15)
      (codeRange 0x112f15 setupBytes) (Effect.post setupEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x112f15 0x48 (by unfold RexWPrefix; decide +kernel) 1
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.apart 0x12f15 5 (by decide +kernel)⟩
  case av =>
    intro s h
    apply h.avoids_code 0x12f15 setupBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12f1a (by decide +kernel))
  advance_then (lea_r64_effect_step 0x112f1a 0x48 (by unfold RexWPrefix; decide +kernel) 0 (.sib 4
    none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f15 setupBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f1f (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x112f1f 0xd2 rfl)
  case sub => exact codeRange_slice_subset 0x112f15 setupBytes 10 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f21 (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x112f21 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib
    4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f15 setupBytes 12 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f26 (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x112f26 0xc9 rfl)
  case sub => exact codeRange_slice_subset 0x112f15 setupBytes 17 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f28 (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x112f28 0x48 0xfa 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f15 setupBytes 19 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f2c (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [setupEffect, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub]
    simp [gprNumber, modrmRm, modrmReg, rexR, shiftCount, BitVec.xor_self, BitVec.zero_sub]
  · intro i
    cases i <;> x86_norm [setupEffect]
  · x86_norm [setupEffect, stackPtr]
    rfl

end P256.Proofs.Generate.Scalar
