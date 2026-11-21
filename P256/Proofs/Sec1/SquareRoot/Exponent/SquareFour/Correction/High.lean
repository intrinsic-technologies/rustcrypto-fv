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

def highBytes : List UInt8 :=
  [0x4c, 0x89, 0xc7, 0x4c, 0x8b, 0x94, 0x24, 0x98, 0x0, 0x0, 0x0, 0x4c, 0x29, 0xd7, 0x48, 0xc1, 0xfe, 0x3f, 0x48, 0x1, 0xfe, 0x4c, 0x89, 0xc7, 0x48, 0xf7, 0xd7, 0x4c, 0x89, 0x44, 0x24, 0x70, 0x4d, 0x89, 0xd0, 0x49, 0x21, 0xf8, 0x4c, 0x9, 0xd7, 0x48, 0x21, 0xf7, 0x4c, 0x9, 0xc7, 0x48, 0xc1, 0xef, 0x3f, 0x48, 0x89, 0x7c, 0x24, 0x8, 0x31, 0xff, 0x48, 0x2b, 0x7c, 0x24, 0x8]

def highEffect (s : RamState) : Effect :=
  let v0 := ((Operand.reg 8#5 : Operand 64).read s)
  let v1 := ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x98#64) : Operand 64).read s)
  let v2 := v0 - v1
  let v3 := ((Operand.reg 6#5 : Operand 64).read s).sshiftRight 63
  let v4 := v3 + v2
  let v5 := ((Operand.reg 8#5 : Operand 64).read s)
  let v6 := ~~~v5
  let v7 := ((Operand.reg 8#5 : Operand 64).read s)
  let v8 := v1
  let v9 := v8 &&& v6
  let v10 := v6 ||| v1
  let v11 := v10 &&& v4
  let v12 := v11 ||| v9
  let v13 := v12 >>> 63
  let v14 := v13
  let v15 := (0 : BitVec 64)
  let v16 := v15 - v14
  { rip := 0x11572f
    writes := [
      ⟨(Operand.reg 7#5 : Operand 64), v16⟩,
      ⟨(Operand.reg 10#5 : Operand 64), v1⟩,
      ⟨(Operand.reg 6#5 : Operand 64), v4⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x70#64) : Operand 64), v7⟩,
      ⟨(Operand.reg 8#5 : Operand 64), v9⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x8#64) : Operand 64), v14⟩ ]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem high_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x1156f0)
      (codeRange 0x1156f0 highBytes) (Effect.post highEffect) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect 0x1156f0 7#5 8#5) from
    mov_r64_r64_effect_step 0x1156f0 0x4c 0xc7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 0 3)
  case pre => intro s hP; exact hP.2
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156f3 (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x1156f3 10#5 (.sib 4 none 0 (.d32 0x98))) from
    mov_r64_m64_effect_step 0x1156f3 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 0x98)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 3 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x98) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x98) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156fb (by decide))
  advance_then (show StepEffect _ _ (subR64R64Effect 0x1156fb 7#5 10#5) from
    sub_r64_r64_effect_step 0x1156fb 0x4c 0xd7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x156fe (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.sarR64Effect 0x1156fe 4 6#5 63) from
    P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x1156fe 0x48 0xfe 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 14 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15702 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x115702 6#5 7#5) from
    add_r64_r64_effect_step 0x115702 0x48 0xfe (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15705 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115705 7#5 8#5) from
    mov_r64_r64_effect_step 0x115705 0x4c 0xc7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15708 (by decide))
  advance_then (show StepEffect _ _ (notR64Effect 0x115708 7#5) from
    not_r64_effect_step 0x115708 0x48 0xd7 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1570b (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x11570b 8#5 (.sib 4 none 0 (.d8 0x70))) from
    mov_m64_r64_effect_step 0x11570b 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 0x70)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 27 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        change MemWritable s (s.regValue .rsp + 0x70) 8
        rw [hP.1.rsp]
        exact stack_writable ctx hP.1 (offset := 0x70) (by decide) (by decide) (.inl ⟨rfl, by decide⟩)
      · x86_norm
        change RangeApart (s.regValue .rsp + 0x70) 8 0x11570b 5
        rw [hP.1.rsp]
        exact stack_apart_code ctx (offset := 0x70) (len := 8) (codeOffset := 0x1570b) (codeLen := 5)
          (by decide) (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (s.regValue .rsp + 0x70) 8 0x1156f0 highBytes.length
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 0x70) (len := 8) (codeOffset := 0x156f0) (codeLen := highBytes.length)
        (by decide) (by decide) (by decide)
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15710 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115710 8#5 10#5) from
    mov_r64_r64_effect_step 0x115710 0x4d 0xd0 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 32 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15713 (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x115713 8#5 7#5) from
    and_r64_r64_effect_step 0x115713 0x49 0xf8 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 35 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15716 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect 0x115716 7#5 10#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x115716 0x4c 0xd7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 38 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15719 (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x115719 7#5 6#5) from
    and_r64_r64_effect_step 0x115719 0x48 0xf7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 41 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1571c (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.FieldNeg.Instructions.orR64R64Effect 0x11571c 7#5 8#5) from
    P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x11571c 0x4c 0xc7 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 44 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1571f (by decide))
  advance_then (show StepEffect _ _ (shrR64Effect 0x11571f 4 7#5 63) from
    shr_r64_imm8_effect_step 0x11571f 0x48 0xef 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 47 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15723 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x115723 7#5 (.sib 4 none 0 (.d8 0x8))) from
    mov_m64_r64_effect_step 0x115723 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 51 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        change MemWritable s (s.regValue .rsp + 0x8) 8
        rw [hP.1.rsp]
        exact stack_writable ctx hP.1 (offset := 0x8) (by decide) (by decide) (.inl ⟨rfl, by decide⟩)
      · x86_norm
        change RangeApart (s.regValue .rsp + 0x8) 8 0x115723 5
        rw [hP.1.rsp]
        exact stack_apart_code ctx (offset := 0x8) (len := 8) (codeOffset := 0x15723) (codeLen := 5)
          (by decide) (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (s.regValue .rsp + 0x8) 8 0x1156f0 highBytes.length
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 0x8) (len := 8) (codeOffset := 0x156f0) (codeLen := highBytes.length)
        (by decide) (by decide) (by decide)
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15728 (by decide))
  advance_then (show StepEffect _ _ (xorR32R32Effect 0x115728 2 7#5 7#5) from
    xor_r32_r32_effect_step 0x115728 0xff rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 56 2)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1572a (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Field.Instructions.subR64M64Effect 0x11572a 7#5 (.sib 4 none 0 (.d8 0x8))) from
    P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x11572a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1156f0 highBytes 58 5)
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
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1572f (by decide))
  advance_finish [highEffect, gprNumber, rexB, rexR, modrmRm, modrmReg, BitVec.xor_self, BitVec.zero_sub]

theorem high_local : Effect.Local highEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [highEffect, h.read_reg, h.read_mem]
  · intro s
    simp [highEffect, Write.Full, Operand.Full]

theorem high_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x1156f0) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (highEffect t).Holds t u ∧ AgreesExcept (Correction.components (exponentFrameBase s)) t u := by
  apply run ctx hf (pc := 0x156f0) hip (high_correct ctx)
    (by decide) (by decide +kernel)
  have sp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  simp [highEffect, Effect.components, Correction.components, sp]

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
