import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.FirstProducts
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose

set_option autoImplicit false

open P256.Proofs.Common.Instructions (addR64M64Effect add_r64_m64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def topCarryBytes : List UInt8 :=
  [0x4c, 0x3, 0x84, 0x24, 0xf0, 0x2, 0x0, 0x0, 0x4c, 0x11, 0xfe, 0x49, 0x83, 0xd6, 0x0, 0x48, 0x1, 0xd6, 0x49, 0x83, 0xd6, 0x0, 0x49, 0x1, 0xc0, 0x49, 0x89, 0xf1, 0x49, 0x83, 0xd1, 0x0, 0x4d, 0x89, 0xf7, 0x49, 0x83, 0xd7, 0x0]

def topCarryEffect (s : RamState) : Effect :=
  let v0 := addSpec ((Operand.reg 8#5 : Operand 64).read s) ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x2f0#64) : Operand 64).read s)
  let v1 := adcSpec ((Operand.reg 6#5 : Operand 64).read s) ((Operand.reg 15#5 : Operand 64).read s) (BitVec.ofBool v0.2.CF)
  let v2 := adcSpec ((Operand.reg 14#5 : Operand 64).read s) 0x0#64 (BitVec.ofBool v1.2.CF)
  let v3 := addSpec v1.1 ((Operand.reg 2#5 : Operand 64).read s)
  let v4 := adcSpec v2.1 0x0#64 (BitVec.ofBool v3.2.CF)
  let v5 := addSpec v0.1 ((Operand.reg 0#5 : Operand 64).read s)
  let v6 := v3.1
  let v7 := adcSpec v6 0x0#64 (BitVec.ofBool v5.2.CF)
  let v8 := v4.1
  let v9 := adcSpec v8 0x0#64 (BitVec.ofBool v7.2.CF)
  { rip := 0x11567b
    writes := [
      ⟨(Operand.reg 8#5 : Operand 64), v5.1⟩,
      ⟨(Operand.reg 6#5 : Operand 64), v3.1⟩,
      ⟨(Operand.reg 14#5 : Operand 64), v4.1⟩,
      ⟨(Operand.reg 9#5 : Operand 64), v7.1⟩,
      ⟨(Operand.reg 15#5 : Operand 64), v9.1⟩]
    flags := some (.ofStatusFlags v9.2) }

theorem topCarry_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x115654)
      (codeRange 0x115654 topCarryBytes) (Effect.post topCarryEffect) := by
  advance_begin (show StepEffect _ _ (addR64M64Effect 0x115654 8#5 (.sib 4 none 0 (.d32 0x2f0))) from
    add_r64_m64_effect_step 0x115654 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 0x2f0)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 0 8)
  case pre =>
    intro s hP
    refine ⟨hP.2, ?_⟩
    change MemReadable s (s.regValue .rsp + 0x2f0) 8
    rw [hP.1.rsp]
    exact stack_readable ctx hP.1 (offset := 0x2f0) (by decide) (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1565c (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect 0x11565c 6#5 15#5) from
    adc_r64_r64_effect_step 0x11565c 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 8 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1565f (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x11565f 14#5 0#8) from
    adc_r64_imm8_effect_step 0x11565f 0x49 0xd6 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 11 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15663 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x115663 6#5 2#5) from
    add_r64_r64_effect_step 0x115663 0x48 0xd6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 15 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15666 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x115666 14#5 0#8) from
    adc_r64_imm8_effect_step 0x115666 0x49 0xd6 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 18 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1566a (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x11566a 8#5 0#5) from
    add_r64_r64_effect_step 0x11566a 0x49 0xc0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1566d (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x11566d 9#5 6#5) from
    mov_r64_r64_effect_step 0x11566d 0x49 0xf1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 25 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15670 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x115670 9#5 0#8) from
    adc_r64_imm8_effect_step 0x115670 0x49 0xd1 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 28 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15674 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115674 15#5 14#5) from
    mov_r64_r64_effect_step 0x115674 0x4d 0xf7 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 32 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15677 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x115677 15#5 0#8) from
    adc_r64_imm8_effect_step 0x115677 0x49 0xd7 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115654 topCarryBytes 35 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1567b (by decide))
  advance_finish [topCarryEffect, gprNumber, rexB, rexR, modrmRm, modrmReg, addSpec]

theorem topCarry_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x115654) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (topCarryEffect t).Holds t u := by
  obtain ⟨fuel, u, he, hr, _, hh⟩ := topCarry_correct ctx t
    (readyToStep hf.machine hf.bindingsSupported)
    (programText_slice (programLoaded_codeIn hf.loaded) 0x15654 topCarryBytes
      (by decide) (by decide +kernel)) ⟨hf, hip⟩
  refine ⟨u, fuel, he, frame_of_agrees ctx hf hr (hh.agrees.mono ?_), hh⟩
  simp [topCarryEffect, Effect.components, components]

end P256.Proofs.Sec1.SquareRoot.SquareFour
