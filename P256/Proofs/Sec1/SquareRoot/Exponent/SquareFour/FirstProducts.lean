import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Frame
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Multiply
import P256.Proofs.Common.EffectCompose.Carry
import P256.Proofs.Common.Instructions.Imul.Triple
import P256.Proofs.Common.Instructions.Neg64
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

open P256.Proofs.Common.Instructions (imul_r64_m64_effect_step mulFlags64 mulHigh64 mulR64Effect mul_m64_effect_step mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Neg64 (negR64Effect neg_r64_effect_step)
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem negR64Effect_local (pc : BitVec 64) (r : BitVec 5) :
    Effect.Local (negR64Effect pc r) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [negR64Effect, h.read_reg]
  · intro s
    simp [negR64Effect, Write.Full, Operand.Full]

attribute [local x86_local] negR64Effect_local
attribute [local x86_compose] negR64Effect

def firstProductsBytes : List UInt8 :=
  [0x48, 0xf7, 0x64, 0x24, 0x68, 0x49, 0x89, 0xd2, 0x49, 0x89, 0xc1, 0x48, 0x8d, 0x3c, 0x8, 0x49, 0xf, 0xaf, 0xfc, 0x48, 0xf7, 0xdf, 0x48, 0x89, 0xf8, 0x48, 0xf7, 0xe3, 0x48, 0x89, 0xc3, 0x49, 0x89, 0xd0]

def firstProductsEffect (s : RamState) : Effect :=
  let a := (Operand.reg 0#5 : Operand 64).read s
  let b := (Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x68#64) : Operand 64).read s
  let c := (Operand.reg 1#5 : Operand 64).read s
  let n := (Operand.reg 12#5 : Operand 64).read s
  let p1 := (Operand.reg 3#5 : Operand 64).read s
  let q := -((a*b+c)*n)
  { rip := 0x115587
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), q*p1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), mulHigh64 q p1⟩,
      ⟨(Operand.reg 10#5 : Operand 64), mulHigh64 a b⟩,
      ⟨(Operand.reg 9#5 : Operand 64), a*b⟩,
      ⟨(Operand.reg 7#5 : Operand 64), q⟩,
      ⟨(Operand.reg 3#5 : Operand 64), q*p1⟩,
      ⟨(Operand.reg 8#5 : Operand 64), mulHigh64 q p1⟩]
    flags := some (mulFlags64 q p1) }

theorem firstProducts_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x115565)
      (codeRange 0x115565 firstProductsBytes) (Effect.post firstProductsEffect) := by
  advance_begin (mul_m64_effect_step 0x115565 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 0x68)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 0 5)
  case pre =>
    intro s hP
    refine ⟨hP.2, ?_⟩
    change MemReadable s (s.regValue .rsp + 0x68) 8
    rw [hP.1.rsp]
    exact stack_readable ctx hP.1 (offset := 0x68) (by decide) (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1556a (by decide))
  advance_then (mov_r64_r64_effect_step 0x11556a 0x49 0xd2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 5 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1556d (by decide))
  advance_then (mov_r64_r64_effect_step 0x11556d 0x49 0xc1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15570 (by decide))
  advance_then (lea_r64_effect_step 0x115570 0x48 (by simp [RexWPrefix]) 7 (.sib 0 (some 1) 0 .none) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 11 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15574 (by decide))
  advance_then (show StepEffect _ _
      (P256.Proofs.Common.Instructions.imulR64R64Effect 0x115574 7 12) from
    P256.Proofs.Common.Instructions.imul_r64_r64_effect_step
      0x115574 0x49 0xfc (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 15 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15578 (by decide))
  advance_then (neg_r64_effect_step 0x115578 0x48 0xdf (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1557b (by decide))
  advance_then (mov_r64_r64_effect_step 0x11557b 0x48 0xf8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1557e (by decide))
  advance_then (show StepEffect _ _ (mulR64Effect 0x11557e 3#5) from
    mul_r64_effect_step 0x11557e 0x48 0xe3 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 25 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15581 (by decide))
  advance_then (mov_r64_r64_effect_step 0x115581 0x48 0xc3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 28 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15584 (by decide))
  advance_then (mov_r64_r64_effect_step 0x115584 0x49 0xd0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115565 firstProductsBytes 31 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15587 (by decide))
  advance_finish [firstProductsEffect, gprNumber, rexB, rexR, modrmRm, modrmReg,
    BitVec.shiftLeft_zero, BitVec.add_zero]

theorem firstProducts_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x115565) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (firstProductsEffect t).Holds t u := by
  obtain ⟨fuel, u, he, hr, _, hh⟩ := firstProducts_correct ctx t
    (readyToStep hf.machine hf.bindingsSupported)
    (programText_slice (programLoaded_codeIn hf.loaded) 0x15565 firstProductsBytes
      (by decide) (by decide +kernel)) ⟨hf, hip⟩
  refine ⟨u, fuel, he, frame_of_agrees ctx hf hr (hh.agrees.mono ?_), hh⟩
  simp [firstProductsEffect, Effect.components, components]

end P256.Proofs.Sec1.SquareRoot.SquareFour
