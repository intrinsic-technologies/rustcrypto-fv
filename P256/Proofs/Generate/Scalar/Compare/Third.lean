import P256.Proofs.Generate.Scalar.Compare.Common
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Inc.Generated.R.Triple
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Common.Field
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (subR64M64Effect_components sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
  X86Proofs

private theorem compareIncLocal (p : BitVec 64) (r : BitVec 5) :
    Effect.Local (fun s => P256.Proofs.Common.Instructions.Effect.forgetFlags (incR64Effect p r s))
      := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [P256.Proofs.Common.Instructions.Effect.forgetFlags, incR64Effect, h.read_reg]
  · intro s
    simp [P256.Proofs.Common.Instructions.Effect.forgetFlags, incR64Effect, Write.Full,
      Operand.Full]

attribute [local x86_compose] incR64Effect
attribute [local x86_local] compareIncLocal

def thirdBytes : List UInt8 :=
  [0x48, 0x89, 0x54, 0x24, 0x8, 0x31, 0xd2, 0x48, 0x2b, 0x54, 0x24, 0x8, 0x48, 0xc1, 0xfa, 0x3f,
    0x4c, 0x1, 0xfa, 0x48, 0xff, 0xc2, 0x4c, 0x89, 0xfe, 0x48, 0xf7, 0xd6, 0x48, 0x9, 0xd6, 0x48,
    0xc1, 0xee, 0x3f]

def thirdEffect (s : RamState) : Effect :=
  let x := (Operand.reg 15 : Operand 64).read s
  let b := (Operand.reg 2 : Operand 64).read s
  let r := (-b).sshiftRight 63 + x + 1
  { rip := 0x112f6c
    writes := [⟨(Operand.mem (stackPtr s + 8) : Operand 64), b⟩,
      ⟨(Operand.reg 2 : Operand 64), r⟩,
      ⟨(Operand.reg 6 : Operand 64), (~~~x ||| r) >>> 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem third_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (ComparePre 0x112f49)
      (codeRange 0x112f49 thirdBytes) (Effect.post thirdEffect) := by
  advance_begin (mov_m64_r64_effect_step 0x112f49 0x48 (by unfold RexWPrefix; decide +kernel) 2
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.writable, h.apart 0x12f49 5 (by decide +kernel)⟩
  case av =>
    intro s h
    apply h.avoids_code 0x12f49 thirdBytes (by decide +kernel)
    intro c hc a len he
    simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he
      exact ⟨rfl, rfl⟩
    · cases he
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x12f4e (by decide +kernel))
  advance_then (xor_r32_r32_effect_step 0x112f4e 0xd2 rfl)
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 5 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f50 (by decide +kernel))
  advance_then (sub_r64_m64_effect_step 0x112f50 0x48 (by unfold RexWPrefix; decide +kernel) 2 (.sib
    4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 7 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable.readable
    · apply Effect.Avoids.of_noMem
      simp [subR64M64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f55 (by decide +kernel))
  advance_then (sar_r64_imm8_effect_step 0x112f55 0x48 0xfa 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [sarR64Effect_components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f59 (by decide +kernel))
  advance_then (add_r64_r64_effect_step 0x112f59 0x4c 0xfa (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 16 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f5c (by decide +kernel))
  advance_then (P256.Proofs.Common.Instructions.StepEffect.forgetFlags (h := inc_r64_effect_step
    0x112f5c 0x48 0xc2 (by unfold RexWPrefix; decide +kernel) rfl rfl))
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [P256.Proofs.Common.Instructions.Effect.forgetFlags, incR64Effect,
        Effect.components, Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f5f (by decide +kernel))
  advance_then (mov_r64_r64_effect_step 0x112f5f 0x4c 0xfe (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f62 (by decide +kernel))
  advance_then (not_r64_effect_step 0x112f62 0x48 0xd6 (by unfold RexWPrefix; decide +kernel) rfl
    rfl)
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 25 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f65 (by decide +kernel))
  advance_then (or_r64_r64_effect_step 0x112f65 0x48 0xd6 (by unfold RexWPrefix; decide +kernel)
    rfl)
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 28 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f68 (by decide +kernel))
  advance_then (shr_r64_imm8_effect_step 0x112f68 0x48 0xee 63
    (by unfold RexWPrefix; decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x112f49 thirdBytes 31 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x12f6c (by decide +kernel))
  apply AdvanceTriple.block_end
  intro s t _ he
  apply he.weaken
  · rfl
  · x86_norm [thirdEffect, stackPtr, Operand.read_reg64, BitVec.xor_self, BitVec.zero_sub]
    simp [gprNumber, modrmRm, modrmReg, rexR, shiftCount, BitVec.xor_self, BitVec.zero_sub]
  · intro i
    cases i <;> x86_norm [thirdEffect]
  · x86_norm [thirdEffect, stackPtr]
    rfl

end P256.Proofs.Generate.Scalar
