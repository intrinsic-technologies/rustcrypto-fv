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

def select3Bytes : List UInt8 :=
  [0x44, 0x88, 0x44, 0x24, 0x8, 0xf, 0xb6, 0x44, 0x24, 0x8, 0x49, 0x31, 0xfd, 0x48, 0xf7, 0xd8, 0x4c, 0x21, 0xe8, 0x48, 0x31, 0xf8, 0x48, 0x89, 0x44, 0x24, 0x50]

def select3Effect (s : RamState) : Effect :=
  let v0 := ((Operand.reg 8 : Operand 8).read s)
  let v1 := v0.setWidth 64
  let v2 := ((Operand.reg 13#5 : Operand 64).read s) ^^^ ((Operand.reg 7#5 : Operand 64).read s)
  let v3 := -v1
  let v4 := v3 &&& v2
  let v5 := v4 ^^^ ((Operand.reg 7#5 : Operand 64).read s)
  let v6 := v5
  { rip := 0x11580d
    writes := [
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x8#64) : Operand 8), v0⟩,
      ⟨(Operand.reg 0#5 : Operand 64), v5⟩,
      ⟨(Operand.reg 13#5 : Operand 64), v2⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x50#64) : Operand 64), v6⟩ ]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem select3_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x1157f2)
      (codeRange 0x1157f2 select3Bytes) (Effect.post select3Effect) := by
  advance_begin (show StepEffect _ _ (storeEffect 0x1157f2 5 (fun t => stackPtr t + 0x8) (fun t => (Operand.reg 8 : Operand 8).read t)) from
    P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x1157f2 0x44 (by simp [RexPrefix]) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157f2 select3Bytes 0 5)
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    change RangeApart (s.regValue .rsp + 8) 1 0x1157f2 select3Bytes.length
    rw [hP.1.rsp]
    exact stack_apart_code ctx (offset := 8) (len := 1) (codeOffset := 0x157f2) (codeLen := select3Bytes.length)
      (by decide) (by decide) (by decide)
  case pre =>
    intro s hP
    refine ⟨hP.2, ?_, ?_⟩
    · change MemWritable s (s.regValue .rsp + 8) 1
      rw [hP.1.rsp]
      exact stack_writable ctx hP.1 (offset := 8) (len := 1) (by decide) (by decide) (.inr (.inr rfl))
    · change RangeApart (s.regValue .rsp + 8) 1 0x1157f2 5
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 8) (len := 1) (codeOffset := 0x157f2) (codeLen := 5) (by decide) (by decide) (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157f7 (by decide))
  advance_then (show StepEffect _ _ (movzxR32M8Effect 0x1157f7 5 0#5 (.sib 4 none 0 (.d8 0x8))) from
    movzx_r32_m8_effect_step 0x1157f7 0 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157f2 select3Bytes 5 5)
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
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157fc (by decide))
  advance_then (show StepEffect _ _ (xorR64R64Effect 0x1157fc 13#5 7#5) from
    xor_r64_r64_effect_step 0x1157fc 0x49 0xfd (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1157f2 select3Bytes 10 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x157ff (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.Neg64.negR64Effect 0x1157ff 0#5) from
    P256.Proofs.Common.Instructions.Neg64.neg_r64_effect_step 0x1157ff 0x48 0xd8 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157f2 select3Bytes 13 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15802 (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x115802 0#5 13#5) from
    and_r64_r64_effect_step 0x115802 0x4c 0xe8 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1157f2 select3Bytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15805 (by decide))
  advance_then (show StepEffect _ _ (xorR64R64Effect 0x115805 0#5 7#5) from
    xor_r64_r64_effect_step 0x115805 0x48 0xf8 (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1157f2 select3Bytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15808 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x115808 0#5 (.sib 4 none 0 (.d8 0x50))) from
    mov_m64_r64_effect_step 0x115808 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 0x50)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1157f2 select3Bytes 22 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        change MemWritable s (s.regValue .rsp + 0x50) 8
        rw [hP.1.rsp]
        exact stack_writable ctx hP.1 (offset := 0x50) (len := 8) (by decide) (by decide) (.inl ⟨rfl, by decide⟩)
      · x86_norm
        change RangeApart (s.regValue .rsp + 0x50) 8 0x115808 5
        rw [hP.1.rsp]
        exact stack_apart_code ctx (offset := 0x50) (len := 8) (codeOffset := 0x15808) (codeLen := 5)
          (by decide) (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (s.regValue .rsp + 0x50) 8 0x1157f2 select3Bytes.length
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 0x50) (len := 8) (codeOffset := 0x157f2) (codeLen := select3Bytes.length)
        (by decide) (by decide) (by decide)
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1580d (by decide))
  advance_finish [select3Effect, gprNumber, rexB, rexR, modrmRm, modrmReg, BitVec.xor_self, BitVec.zero_sub]

theorem select3_local : Effect.Local select3Effect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [select3Effect, h.read_reg]
  · intro s
    simp [select3Effect, Write.Full, Operand.Full]

theorem select3_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x1157f2) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (select3Effect t).Holds t u ∧ AgreesExcept (Correction.components (exponentFrameBase s)) t u := by
  apply run ctx hf (pc := 0x157f2) hip (select3_correct ctx)
    (by decide) (by decide +kernel)
  have sp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  simp [select3Effect, Effect.components, Correction.components, sp]

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
