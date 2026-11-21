import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.Correction.Support
import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.FirstProducts
import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Correction.Arithmetic
import P256.Proofs.Common.Field.Operations.Neg.SubLoad
import P256.Proofs.Common.Instructions.Sar.Triple
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Sec1.SquareRoot.SquareFour
open P256.Proofs.Common.Field (AdvanceTriple)

def middleBytes : List UInt8 :=
  [0x48, 0x89, 0xee, 0x48, 0x29, 0xde, 0x48, 0xc1, 0xfa, 0x3f, 0x48, 0x1, 0xf2, 0x48, 0x89, 0xee, 0x48, 0xf7, 0xd6, 0x48, 0x89, 0xdf, 0x48, 0x21, 0xf7, 0x48, 0x9, 0xde, 0x48, 0x21, 0xd6, 0x48, 0x9, 0xfe, 0x48, 0xc1, 0xee, 0x3f, 0x48, 0x89, 0x74, 0x24, 0x8, 0x31, 0xf6, 0x48, 0x2b, 0x74, 0x24, 0x8]

def middleEffect (s : RamState) : Effect :=
  let v0 := ((Operand.reg 5#5 : Operand 64).read s)
  let v1 := v0 - ((Operand.reg 3#5 : Operand 64).read s)
  let v2 := ((Operand.reg 2#5 : Operand 64).read s).sshiftRight 63
  let v3 := v2 + v1
  let v4 := ((Operand.reg 5#5 : Operand 64).read s)
  let v5 := ~~~v4
  let v6 := ((Operand.reg 3#5 : Operand 64).read s)
  let v7 := v6 &&& v5
  let v8 := v5 ||| ((Operand.reg 3#5 : Operand 64).read s)
  let v9 := v8 &&& v3
  let v10 := v9 ||| v7
  let v11 := v10 >>> 63
  let v12 := v11
  let v13 := (0 : BitVec 64)
  let v14 := v13 - v12
  { rip := 0x1156f0
    writes := [
      ⟨(Operand.reg 6#5 : Operand 64), v14⟩,
      ⟨(Operand.reg 2#5 : Operand 64), v3⟩,
      ⟨(Operand.reg 7#5 : Operand 64), v7⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x8#64) : Operand 64), v12⟩ ]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem middle_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x1156be)
      (codeRange 0x1156be middleBytes) (Effect.post middleEffect) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect 0x1156be 6#5 5#5) from
    mov_r64_r64_effect_step 0x1156be 0x48 0xee (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 0 3)
  case pre => intro s hP; exact hP.2
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156c1 (by decide))
  advance_then (show StepEffect _ _ (subR64R64Effect 0x1156c1 6#5 3#5) from
    sub_r64_r64_effect_step 0x1156c1 0x48 0xde (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 3 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156c4 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.sarR64Effect 0x1156c4 4 2#5 63) from
    P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x1156c4 0x48 0xfa 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 6 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156c8 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x1156c8 2#5 6#5) from
    add_r64_r64_effect_step 0x1156c8 0x48 0xf2 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 10 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156cb (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x1156cb 6#5 5#5) from
    mov_r64_r64_effect_step 0x1156cb 0x48 0xee (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 13 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156ce (by decide))
  advance_then (show StepEffect _ _ (notR64Effect 0x1156ce 6#5) from
    not_r64_effect_step 0x1156ce 0x48 0xd6 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156d1 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x1156d1 7#5 3#5) from
    mov_r64_r64_effect_step 0x1156d1 0x48 0xdf (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156d4 (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x1156d4 7#5 6#5) from
    and_r64_r64_effect_step 0x1156d4 0x48 0xf7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156d7 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect 0x1156d7 6#5 3#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1156d7 0x48 0xde (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 25 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156da (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x1156da 6#5 2#5) from
    and_r64_r64_effect_step 0x1156da 0x48 0xd6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 28 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156dd (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect 0x1156dd 6#5 7#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1156dd 0x48 0xfe (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 31 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156e0 (by decide))
  advance_then (show StepEffect _ _ (shrR64Effect 0x1156e0 4 6#5 63) from
    shr_r64_imm8_effect_step 0x1156e0 0x48 0xee 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 34 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156e4 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1156e4 6#5 (.sib 4 none 0 (.d8 0x8))) from
    mov_m64_r64_effect_step 0x1156e4 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 38 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        change MemWritable s (s.regValue .rsp + 0x8) 8
        rw [hP.1.rsp]
        exact stack_writable ctx hP.1 (offset := 0x8) (by decide) (by decide) (.inl ⟨rfl, by decide⟩)
      · x86_norm
        change RangeApart (s.regValue .rsp + 0x8) 8 0x1156e4 5
        rw [hP.1.rsp]
        exact stack_apart_code ctx (offset := 0x8) (len := 8) (codeOffset := 0x156e4) (codeLen := 5)
          (by decide) (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (s.regValue .rsp + 0x8) 8 0x1156be middleBytes.length
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 0x8) (len := 8) (codeOffset := 0x156be) (codeLen := middleBytes.length)
        (by decide) (by decide) (by decide)
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156e9 (by decide))
  advance_then (show StepEffect _ _ (xorR32R32Effect 0x1156e9 2 6#5 6#5) from
    xor_r32_r32_effect_step 0x1156e9 0xf6 rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 43 2)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156eb (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.Instructions.subR64M64Effect 0x1156eb 6#5 (.sib 4 none 0 (.d8 0x8))) from
    P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x1156eb 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156be middleBytes 45 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x8) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x8) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156f0 (by decide))
  advance_finish [middleEffect, gprNumber, rexB, rexR, modrmRm, modrmReg, BitVec.xor_self, BitVec.zero_sub]

theorem middle_local : Effect.Local middleEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [middleEffect, h.read_reg]
  · intro s
    simp [middleEffect, Write.Full, Operand.Full]

theorem middle_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x1156be) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (middleEffect t).Holds t u ∧ AgreesExcept (Correction.components (exponentFrameBase s)) t u := by
  apply run ctx hf (pc := 0x156be) hip (middle_correct ctx)
    (by decide) (by decide +kernel)
  have sp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  simp [middleEffect, Effect.components, Correction.components, sp]

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
