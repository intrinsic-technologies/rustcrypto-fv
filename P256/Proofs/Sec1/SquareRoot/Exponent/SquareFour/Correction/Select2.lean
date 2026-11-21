import P256.Proofs.Field.Add.Correction
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Common.Instructions.Neg64
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
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

def select2Bytes : List UInt8 :=
  [0x44, 0x88, 0x44, 0x24, 0x8, 0xf, 0xb6, 0x44, 0x24, 0x8, 0x48, 0x8b, 0x4c, 0x24, 0x70, 0x48, 0x31, 0xf1, 0x48, 0xf7, 0xd8, 0x48, 0x21, 0xc8, 0x48, 0x31, 0xf0, 0x48, 0x89, 0x44, 0x24, 0x58]

def select2Effect (s : RamState) : Effect :=
  let v0 := ((Operand.reg 8 : Operand 8).read s)
  let v1 := v0.setWidth 64
  let v2 := ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x70#64) : Operand 64).read s)
  let v3 := v2 ^^^ ((Operand.reg 6#5 : Operand 64).read s)
  let v4 := -v1
  let v5 := v4 &&& v3
  let v6 := v5 ^^^ ((Operand.reg 6#5 : Operand 64).read s)
  let v7 := v6
  { rip := 0x1157f2
    writes := [
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x8#64) : Operand 8), v0⟩,
      ⟨(Operand.reg 0#5 : Operand 64), v6⟩,
      ⟨(Operand.reg 1#5 : Operand 64), v3⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x58#64) : Operand 64), v7⟩ ]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem select2_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x1157d2)
      (codeRange 0x1157d2 select2Bytes) (Effect.post select2Effect) := by
  advance_begin (show StepEffect _ _ (storeEffect 0x1157d2 5 (fun t => stackPtr t + 0x8) (fun t => (Operand.reg 8 : Operand 8).read t)) from
    P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x1157d2 0x44 (by simp [RexPrefix]) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157d2 select2Bytes 0 5)
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    change RangeApart (s.regValue .rsp + 8) 1 0x1157d2 select2Bytes.length
    rw [hP.1.rsp]
    exact stack_apart_code ctx (offset := 8) (len := 1) (codeOffset := 0x157d2) (codeLen := select2Bytes.length)
      (by decide) (by decide) (by decide)
  case pre =>
    intro s hP
    refine ⟨hP.2, ?_, ?_⟩
    · change MemWritable s (s.regValue .rsp + 8) 1
      rw [hP.1.rsp]
      exact stack_writable ctx hP.1 (offset := 8) (len := 1) (by decide) (by decide) (.inr (.inr rfl))
    · change RangeApart (s.regValue .rsp + 8) 1 0x1157d2 5
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 8) (len := 1) (codeOffset := 0x157d2) (codeLen := 5) (by decide) (by decide) (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157d7 (by decide))
  advance_then (show StepEffect _ _ (movzxR32M8Effect 0x1157d7 5 0#5 (.sib 4 none 0 (.d8 0x8))) from
    movzx_r32_m8_effect_step 0x1157d7 0 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157d2 select2Bytes 5 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x8) 1
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x8) (len := 1) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157dc (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x1157dc 1#5 (.sib 4 none 0 (.d8 0x70))) from
    mov_r64_m64_effect_step 0x1157dc 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157d2 select2Bytes 10 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x70) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x70) (len := 8) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157e1 (by decide))
  advance_then (show StepEffect _ _ (xorR64R64Effect 0x1157e1 1#5 6#5) from
    xor_r64_r64_effect_step 0x1157e1 0x48 0xf1 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1157d2 select2Bytes 15 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157e4 (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.Neg64.negR64Effect 0x1157e4 0#5) from
    P256.Proofs.Common.Instructions.Neg64.neg_r64_effect_step 0x1157e4 0x48 0xd8 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157d2 select2Bytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157e7 (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x1157e7 0#5 1#5) from
    and_r64_r64_effect_step 0x1157e7 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1157d2 select2Bytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157ea (by decide))
  advance_then (show StepEffect _ _ (xorR64R64Effect 0x1157ea 0#5 6#5) from
    xor_r64_r64_effect_step 0x1157ea 0x48 0xf0 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1157d2 select2Bytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157ed (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1157ed 0#5 (.sib 4 none 0 (.d8 0x58))) from
    mov_m64_r64_effect_step 0x1157ed 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 0x58)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157d2 select2Bytes 27 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        change MemWritable s (s.regValue .rsp + 0x58) 8
        rw [hP.1.rsp]
        exact stack_writable ctx hP.1 (offset := 0x58) (len := 8) (by decide) (by decide) (.inl ⟨rfl, by decide⟩)
      · x86_norm
        change RangeApart (s.regValue .rsp + 0x58) 8 0x1157ed 5
        rw [hP.1.rsp]
        exact stack_apart_code ctx (offset := 0x58) (len := 8) (codeOffset := 0x157ed) (codeLen := 5)
          (by decide) (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (s.regValue .rsp + 0x58) 8 0x1157d2 select2Bytes.length
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 0x58) (len := 8) (codeOffset := 0x157d2) (codeLen := select2Bytes.length)
        (by decide) (by decide) (by decide)
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157f2 (by decide))
  advance_finish [select2Effect, gprNumber, rexB, rexR, modrmRm, modrmReg, BitVec.xor_self, BitVec.zero_sub]

theorem select2_local : Effect.Local select2Effect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [select2Effect, h.read_reg, h.read_mem]
  · intro s
    simp [select2Effect, Write.Full, Operand.Full]

theorem select2_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x1157d2) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (select2Effect t).Holds t u ∧ AgreesExcept (Correction.components (exponentFrameBase s)) t u := by
  apply run ctx hf (pc := 0x157d2) hip (select2_correct ctx)
    (by decide) (by decide +kernel)
  have sp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  simp [select2Effect, Effect.components, Correction.components, sp]

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
