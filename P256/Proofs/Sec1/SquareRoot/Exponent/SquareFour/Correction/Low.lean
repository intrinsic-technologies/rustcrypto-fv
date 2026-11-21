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

def lowBytes : List UInt8 :=
  [0x48, 0x89, 0xc8, 0x4c, 0x29, 0xd8, 0x48, 0x89, 0xca, 0x48, 0xf7, 0xd2, 0x4c, 0x89, 0xde, 0x48, 0x21, 0xd6, 0x4c, 0x9, 0xda, 0x48, 0x21, 0xc2, 0x48, 0x9, 0xf2, 0x48, 0xc1, 0xea, 0x3f, 0x48, 0x89, 0x54, 0x24, 0x8, 0x4c, 0x8d, 0x74, 0x24, 0x8, 0x31, 0xd2, 0x48, 0x2b, 0x54, 0x24, 0x8]

def lowEffect (s : RamState) : Effect :=
  let v0 := ((Operand.reg 1#5 : Operand 64).read s)
  let v1 := v0 - ((Operand.reg 11#5 : Operand 64).read s)
  let v2 := ((Operand.reg 1#5 : Operand 64).read s)
  let v3 := ~~~v2
  let v4 := ((Operand.reg 11#5 : Operand 64).read s)
  let v5 := v4 &&& v3
  let v6 := v3 ||| ((Operand.reg 11#5 : Operand 64).read s)
  let v7 := v6 &&& v1
  let v8 := v7 ||| v5
  let v9 := v8 >>> 63
  let v10 := v9
  let v11 := ((Operand.reg 4#5 : Operand 64).read s) + 0x8#64
  let v12 := (0 : BitVec 64)
  let v13 := v12 - v10
  { rip := 0x1156be
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), v1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), v13⟩,
      ⟨(Operand.reg 6#5 : Operand 64), v5⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x8#64) : Operand 64), v10⟩,
      ⟨(Operand.reg 14#5 : Operand 64), v11⟩ ]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem low_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x11568e)
      (codeRange 0x11568e lowBytes) (Effect.post lowEffect) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect 0x11568e 0#5 1#5) from
    mov_r64_r64_effect_step 0x11568e 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 0 3)
  case pre => intro s hP; exact hP.2
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15691 (by decide))
  advance_then (show StepEffect _ _ (subR64R64Effect 0x115691 0#5 11#5) from
    sub_r64_r64_effect_step 0x115691 0x4c 0xd8 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 3 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15694 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115694 2#5 1#5) from
    mov_r64_r64_effect_step 0x115694 0x48 0xca (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 6 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15697 (by decide))
  advance_then (show StepEffect _ _ (notR64Effect 0x115697 2#5) from
    not_r64_effect_step 0x115697 0x48 0xd2 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 9 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1569a (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x11569a 6#5 11#5) from
    mov_r64_r64_effect_step 0x11569a 0x4c 0xde (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 12 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1569d (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x11569d 6#5 2#5) from
    and_r64_r64_effect_step 0x11569d 0x48 0xd6 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 15 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156a0 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect 0x1156a0 2#5 11#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1156a0 0x4c 0xda (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156a3 (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x1156a3 2#5 0#5) from
    and_r64_r64_effect_step 0x1156a3 0x48 0xc2 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156a6 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect 0x1156a6 2#5 6#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1156a6 0x48 0xf2 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156a9 (by decide))
  advance_then (show StepEffect _ _ (shrR64Effect 0x1156a9 4 2#5 63) from
    shr_r64_imm8_effect_step 0x1156a9 0x48 0xea 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 27 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156ad (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1156ad 2#5 (.sib 4 none 0 (.d8 0x8))) from
    mov_m64_r64_effect_step 0x1156ad 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 31 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        change MemWritable s (s.regValue .rsp + 0x8) 8
        rw [hP.1.rsp]
        exact stack_writable ctx hP.1 (offset := 0x8) (by decide) (by decide) (.inl ⟨rfl, by decide⟩)
      · x86_norm
        change RangeApart (s.regValue .rsp + 0x8) 8 0x1156ad 5
        rw [hP.1.rsp]
        exact stack_apart_code ctx (offset := 0x8) (len := 8) (codeOffset := 0x156ad) (codeLen := 5)
          (by decide) (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (s.regValue .rsp + 0x8) 8 0x11568e lowBytes.length
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 0x8) (len := 8) (codeOffset := 0x1568e) (codeLen := lowBytes.length)
        (by decide) (by decide) (by decide)
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156b2 (by decide))
  advance_then (show StepEffect _ _ (leaR64Effect 0x1156b2 14#5 (.sib 4 none 0 (.d8 0x8))) from
    lea_r64_effect_step 0x1156b2 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 36 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156b7 (by decide))
  advance_then (show StepEffect _ _ (xorR32R32Effect 0x1156b7 2 2#5 2#5) from
    xor_r32_r32_effect_step 0x1156b7 0xd2 rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 41 2)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156b9 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.Instructions.subR64M64Effect 0x1156b9 2#5 (.sib 4 none 0 (.d8 0x8))) from
    P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x1156b9 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11568e lowBytes 43 5)
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
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156be (by decide))
  advance_finish [lowEffect, gprNumber, rexB, rexR, modrmRm, modrmReg, BitVec.xor_self, BitVec.zero_sub]

theorem low_local : Effect.Local lowEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [lowEffect, h.read_reg]
  · intro s
    simp [lowEffect, Write.Full, Operand.Full]

theorem low_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x11568e) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (lowEffect t).Holds t u ∧ AgreesExcept (Correction.components (exponentFrameBase s)) t u := by
  apply run ctx hf (pc := 0x1568e) hip (low_correct ctx)
    (by decide) (by decide +kernel)
  have sp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  simp [lowEffect, Effect.components, Correction.components, sp]

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
