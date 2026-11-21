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

def deadBytes : List UInt8 :=
  [0x44, 0x88, 0x44, 0x24, 0x8, 0x44, 0xf, 0xb6, 0x54, 0x24, 0x8, 0x49, 0xff, 0xca, 0x4d, 0x21, 0xca, 0x49, 0xc1, 0xfa, 0x3f, 0x4d, 0x1, 0xfa, 0x49, 0xc1, 0xea, 0x3f, 0x4c, 0x89, 0x54, 0x24, 0x8]

def deadEffect (s : RamState) : Effect :=
  let v0 := ((Operand.reg 8 : Operand 8).read s)
  let v1 := v0.setWidth 64
  let v2 := v1 - 1#64
  let v3 := v2 &&& ((Operand.reg 9#5 : Operand 64).read s)
  let v4 := v3.sshiftRight 63
  let v5 := v4 + ((Operand.reg 15#5 : Operand 64).read s)
  let v6 := v5 >>> 63
  let v7 := v6
  { rip := 0x11579b
    writes := [
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x8#64) : Operand 8), v7.setWidth 8⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x8#64) : Operand 64), v7⟩,
      ⟨(Operand.reg 10#5 : Operand 64), v6⟩ ]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem dead_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x11577a)
      (codeRange 0x11577a deadBytes) (Effect.post deadEffect) := by
  advance_begin (show StepEffect _ _ (storeEffect 0x11577a 5 (fun t => stackPtr t + 0x8) (fun t => (Operand.reg 8 : Operand 8).read t)) from
    P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x11577a 0x44 (by simp [RexPrefix]) 0 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11577a deadBytes 0 5)
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    change RangeApart (s.regValue .rsp + 8) 1 0x11577a deadBytes.length
    rw [hP.1.rsp]
    exact stack_apart_code ctx (offset := 8) (len := 1) (codeOffset := 0x1577a) (codeLen := deadBytes.length)
      (by decide) (by decide) (by decide)
  case pre =>
    intro s hP
    refine ⟨hP.2, ?_, ?_⟩
    · change MemWritable s (s.regValue .rsp + 8) 1
      rw [hP.1.rsp]
      exact stack_writable ctx hP.1 (offset := 8) (len := 1) (by decide) (by decide) (.inr (.inr rfl))
    · change RangeApart (s.regValue .rsp + 8) 1 0x11577a 5
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 8) (len := 1) (codeOffset := 0x1577a) (codeLen := 5) (by decide) (by decide) (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1577f (by decide))
  advance_then (show StepEffect _ _ (movzxR32M8Effect 0x11577f 6 10#5 (.sib 4 none 0 (.d8 0x8))) from
    movzx_r_m8_rex_effect_step 0x11577f 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (fun _ => rfl) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11577a deadBytes 5 6)
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
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15785 (by decide))
  advance_then (show StepEffect _ _ (decR64Effect 0x115785 10#5) from
    dec_r64_effect_step 0x115785 0x49 0xca (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11577a deadBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15788 (by decide))
  advance_then (show StepEffect _ _ (andR64R64Effect 0x115788 10#5 9#5) from
    and_r64_r64_effect_step 0x115788 0x4d 0xca (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11577a deadBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1578b (by decide))
  advance_then (show StepEffect _ _ (P256.Proofs.Common.Instructions.sarR64Effect 0x11578b 4 10#5 63) from
    P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x11578b 0x49 0xfa 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11577a deadBytes 17 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1578f (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x11578f 10#5 15#5) from
    add_r64_r64_effect_step 0x11578f 0x4d 0xfa (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11577a deadBytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15792 (by decide))
  advance_then (show StepEffect _ _ (shrR64Effect 0x115792 4 10#5 63) from
    shr_r64_imm8_effect_step 0x115792 0x49 0xea 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11577a deadBytes 24 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15796 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x115796 10#5 (.sib 4 none 0 (.d8 0x8))) from
    mov_m64_r64_effect_step 0x115796 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 0x8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11577a deadBytes 28 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        change MemWritable s (s.regValue .rsp + 0x8) 8
        rw [hP.1.rsp]
        exact stack_writable ctx hP.1 (offset := 0x8) (len := 8) (by decide) (by decide) (.inl ⟨rfl, by decide⟩)
      · x86_norm
        change RangeApart (s.regValue .rsp + 0x8) 8 0x115796 5
        rw [hP.1.rsp]
        exact stack_apart_code ctx (offset := 0x8) (len := 8) (codeOffset := 0x15796) (codeLen := 5)
          (by decide) (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (s.regValue .rsp + 0x8) 8 0x11577a deadBytes.length
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 0x8) (len := 8) (codeOffset := 0x1577a) (codeLen := deadBytes.length)
        (by decide) (by decide) (by decide)
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1579b (by decide))
  advance_finish [deadEffect, gprNumber, rexB, rexR, modrmRm, modrmReg, BitVec.xor_self, BitVec.zero_sub]

theorem dead_local : Effect.Local deadEffect := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [deadEffect, h.read_reg]
  · intro s
    simp [deadEffect, Write.Full, Operand.Full]

theorem dead_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x11577a) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (deadEffect t).Holds t u ∧ AgreesExcept (Correction.components (exponentFrameBase s)) t u := by
  apply run ctx hf (pc := 0x1577a) hip (dead_correct ctx)
    (by decide) (by decide +kernel)
  have sp : (Operand.reg 4#5 : Operand 64).read t = exponentFrameBase s := hf.rsp
  simp [deadEffect, Effect.components, Correction.components, sp]

end P256.Proofs.Sec1.SquareRoot.SquareFour.Correction
