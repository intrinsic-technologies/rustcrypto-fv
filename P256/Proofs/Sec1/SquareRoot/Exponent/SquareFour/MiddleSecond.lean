import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.FirstProducts
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def middleSecondBytes : List UInt8 :=
  [0x48, 0x89, 0xf0, 0x48, 0xf7, 0x64, 0x24, 0x50, 0x48, 0x89, 0xd6, 0x49, 0x89, 0xc0, 0x48, 0x89, 0xf8, 0x48, 0xf7, 0xa4, 0x24, 0x90, 0x0, 0x0, 0x0, 0x4c, 0x3, 0x4c, 0x24, 0x70, 0x48, 0x13, 0x84, 0x24, 0xe8, 0x2, 0x0, 0x0, 0x48, 0x83, 0xd2, 0x0, 0x48, 0x1, 0xd8, 0x48, 0x8b, 0x9c, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x83, 0xd2, 0x0, 0x4c, 0x89, 0xcd, 0x4c, 0x1, 0xd5, 0x48, 0x83, 0xd0, 0x0, 0x48, 0x83, 0xd2, 0x0]

def middleSecondEffect (s : RamState) : Effect :=
  let v0 := ((Operand.reg 6#5 : Operand 64).read s)
  let v1 := v0 * ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x50#64) : Operand 64).read s)
  let h1 := mulHigh64 v0 ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x50#64) : Operand 64).read s)
  let v2 := h1
  let v3 := v1
  let v4 := ((Operand.reg 7#5 : Operand 64).read s)
  let v5 := v4 * ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x90#64) : Operand 64).read s)
  let h5 := mulHigh64 v4 ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x90#64) : Operand 64).read s)
  let v6 := addSpec ((Operand.reg 9#5 : Operand 64).read s) ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x70#64) : Operand 64).read s)
  let v7 := adcSpec v5 ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x2e8) : Operand 64).read s) (BitVec.ofBool v6.2.CF)
  let v8 := ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x80#64) : Operand 64).read s)
  let v9 := adcSpec h5 0x0#64 (BitVec.ofBool v7.2.CF)
  let v10 := addSpec v7.1 ((Operand.reg 3#5 : Operand 64).read s)
  let v12 := adcSpec v9.1 0x0#64 (BitVec.ofBool v10.2.CF)
  let v13 := v6.1
  let v14 := addSpec v13 ((Operand.reg 10#5 : Operand 64).read s)
  let v15 := adcSpec v10.1 0x0#64 (BitVec.ofBool v14.2.CF)
  let v16 := adcSpec v12.1 0x0#64 (BitVec.ofBool v15.2.CF)
  { rip := 0x115654
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), v15.1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), v16.1⟩,
      ⟨(Operand.reg 6#5 : Operand 64), v2⟩,
      ⟨(Operand.reg 8#5 : Operand 64), v3⟩,
      ⟨(Operand.reg 9#5 : Operand 64), v6.1⟩,
      ⟨(Operand.reg 3#5 : Operand 64), v8⟩,
      ⟨(Operand.reg 5#5 : Operand 64), v14.1⟩]
    flags := some (.ofStatusFlags v16.2) }


theorem middleSecond_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x11560d)
      (codeRange 0x11560d middleSecondBytes) (Effect.post middleSecondEffect) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect 0x11560d 0#5 6#5) from
    mov_r64_r64_effect_step 0x11560d 0x48 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 0 3)
  case pre => intro s hP; exact hP.2
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15610 (by decide))
  advance_then (show StepEffect _ _ (mulM64Effect 0x115610 (.sib 4 none 0 (.d8 0x50))) from
    mul_m64_effect_step 0x115610 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 0x50)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x50) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x50) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15615 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115615 6#5 2#5) from
    mov_r64_r64_effect_step 0x115615 0x48 0xd6 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 8 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15618 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115618 8#5 0#5) from
    mov_r64_r64_effect_step 0x115618 0x49 0xc0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1561b (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x11561b 0#5 7#5) from
    mov_r64_r64_effect_step 0x11561b 0x48 0xf8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1561e (by decide))
  advance_then (show StepEffect _ _ (mulM64Effect 0x11561e (.sib 4 none 0 (.d32 0x90))) from
    mul_m64_effect_step 0x11561e 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 0x90)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 17 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x90) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x90) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15626 (by decide))
  advance_then (show StepEffect _ _ (addR64M64Effect 0x115626 9#5 (.sib 4 none 0 (.d8 0x70))) from
    add_r64_m64_effect_step 0x115626 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 0x70)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 25 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x70) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x70) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1562b (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64M64Effect 0x11562b 0#5 (.sib 4 none 0 (.d32 0x2e8))) from
    adc_r64_m64_effect_step 0x11562b 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 0x2e8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 30 8)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x2e8) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x2e8) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15633 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x115633 2#5 0#8) from
    adc_r64_imm8_effect_step 0x115633 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 38 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15637 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x115637 0#5 3#5) from
    add_r64_r64_effect_step 0x115637 0x48 0xd8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 42 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1563a (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x11563a 3#5 (.sib 4 none 0 (.d32 0x80))) from
    mov_r64_m64_effect_step 0x11563a 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 0x80)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 45 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x80) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x80) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15642 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x115642 2#5 0#8) from
    adc_r64_imm8_effect_step 0x115642 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 53 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15646 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115646 5#5 9#5) from
    mov_r64_r64_effect_step 0x115646 0x4c 0xcd (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 57 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15649 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x115649 5#5 10#5) from
    add_r64_r64_effect_step 0x115649 0x4c 0xd5 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 60 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1564c (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x11564c 0#5 0#8) from
    adc_r64_imm8_effect_step 0x11564c 0x48 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 63 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15650 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x115650 2#5 0#8) from
    adc_r64_imm8_effect_step 0x115650 0x48 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x11560d middleSecondBytes 67 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15654 (by decide))
  advance_finish [middleSecondEffect, gprNumber, rexB, rexR, modrmRm, modrmReg, addSpec]

theorem middleSecond_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x11560d) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (middleSecondEffect t).Holds t u := by
  obtain ⟨fuel, u, he, hr, _, hh⟩ := middleSecond_correct ctx t
    (readyToStep hf.machine hf.bindingsSupported)
    (programText_slice (programLoaded_codeIn hf.loaded) 0x1560d middleSecondBytes
      (by decide) (by decide +kernel)) ⟨hf, hip⟩
  refine ⟨u, fuel, he, frame_of_agrees ctx hf hr ?_, hh⟩
  exact hh.agrees.mono (by simp [middleSecondEffect, Effect.components, components])

end P256.Proofs.Sec1.SquareRoot.SquareFour
