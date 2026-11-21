import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.FirstProducts

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64 mulM64Effect mulR64Effect mul_m64_effect_step mul_r64_effect_step)
open P256.Proofs.Common.Instructions.Carry (adcR64Imm8Effect adcR64R64Effect adcSpec adc_r64_imm8_effect_step adc_r64_r64_effect_step)
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstCarryBytes : List UInt8 :=
  [0x49, 0x1, 0xc9, 0x4c, 0x11, 0xd3, 0x49, 0x83, 0xd0, 0x0, 0x48, 0x89, 0xf8, 0x49, 0xf7, 0xe3, 0x49, 0x89, 0xd3, 0x48, 0x89, 0xc1, 0x48, 0x89, 0xf0, 0x48, 0xf7, 0x64, 0x24, 0x60, 0x49, 0x89, 0xd4, 0x49, 0x1, 0xdb, 0x49, 0x83, 0xd0, 0x0, 0x4c, 0x1, 0xc9, 0x49, 0x83, 0xd3, 0x0, 0x49, 0x83, 0xd0, 0x0]

def firstCarryEffect (s : RamState) : Effect :=
  let q := (Operand.reg 7#5 : Operand 64).read s
  let p0 := (Operand.reg 11#5 : Operand 64).read s
  let a := (Operand.reg 6#5 : Operand 64).read s
  let b1 := (Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x60#64) : Operand 64).read s
  let x := addSpec ((Operand.reg 9#5 : Operand 64).read s) ((Operand.reg 1#5 : Operand 64).read s)
  let y := adcSpec ((Operand.reg 3#5 : Operand 64).read s) ((Operand.reg 10#5 : Operand 64).read s) (BitVec.ofBool x.2.CF)
  let z := adcSpec ((Operand.reg 8#5 : Operand 64).read s) 0#64 (BitVec.ofBool y.2.CF)
  let u := addSpec (mulHigh64 q p0) y.1
  let v := adcSpec z.1 0#64 (BitVec.ofBool u.2.CF)
  let w := addSpec (q*p0) x.1
  let k := adcSpec u.1 0#64 (BitVec.ofBool w.2.CF)
  let l := adcSpec v.1 0#64 (BitVec.ofBool k.2.CF)
  { rip := 0x1155ba
    writes := [
      ⟨(Operand.reg 0#5 : Operand 64), a*b1⟩,
      ⟨(Operand.reg 2#5 : Operand 64), mulHigh64 a b1⟩,
      ⟨(Operand.reg 9#5 : Operand 64), x.1⟩,
      ⟨(Operand.reg 3#5 : Operand 64), y.1⟩,
      ⟨(Operand.reg 8#5 : Operand 64), l.1⟩,
      ⟨(Operand.reg 11#5 : Operand 64), k.1⟩,
      ⟨(Operand.reg 1#5 : Operand 64), w.1⟩,
      ⟨(Operand.reg 12#5 : Operand 64), mulHigh64 a b1⟩]
    flags := some (.ofStatusFlags l.2) }

theorem firstCarry_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x115587)
      (codeRange 0x115587 firstCarryBytes) (Effect.post firstCarryEffect) := by
  advance_begin (show StepEffect _ _ (addR64R64Effect 0x115587 9#5 1#5) from
    add_r64_r64_effect_step 0x115587 0x49 0xc9 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 0 3)
  case pre => intro s hP; exact hP.2
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1558a (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect 0x11558a 3#5 10#5) from
    adc_r64_r64_effect_step 0x11558a 0x4c 0xd3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 3 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1558d (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x11558d 8#5 0#8) from
    adc_r64_imm8_effect_step 0x11558d 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 6 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15591 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115591 0#5 7#5) from
    mov_r64_r64_effect_step 0x115591 0x48 0xf8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 10 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15594 (by decide))
  advance_then (show StepEffect _ _ (mulR64Effect 0x115594 11#5) from
    mul_r64_effect_step 0x115594 0x49 0xe3 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 13 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15597 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x115597 11#5 2#5) from
    mov_r64_r64_effect_step 0x115597 0x49 0xd3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 16 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1559a (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x11559a 1#5 0#5) from
    mov_r64_r64_effect_step 0x11559a 0x48 0xc1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1559d (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x11559d 0#5 6#5) from
    mov_r64_r64_effect_step 0x11559d 0x48 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155a0 (by decide))
  advance_then (show StepEffect _ _ (mulM64Effect 0x1155a0 (.sib 4 none 0 (.d8 0x60))) from
    mul_m64_effect_step 0x1155a0 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 0x60)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 25 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x60) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x60) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155a5 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x1155a5 12#5 2#5) from
    mov_r64_r64_effect_step 0x1155a5 0x49 0xd4 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 30 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155a8 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x1155a8 11#5 3#5) from
    add_r64_r64_effect_step 0x1155a8 0x49 0xdb (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 33 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155ab (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x1155ab 8#5 0#8) from
    adc_r64_imm8_effect_step 0x1155ab 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 36 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155af (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x1155af 1#5 9#5) from
    add_r64_r64_effect_step 0x1155af 0x4c 0xc9 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 40 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155b2 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x1155b2 11#5 0#8) from
    adc_r64_imm8_effect_step 0x1155b2 0x49 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 43 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155b6 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x1155b6 8#5 0#8) from
    adc_r64_imm8_effect_step 0x1155b6 0x49 0xd0 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x115587 firstCarryBytes 47 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155ba (by decide))
  advance_finish [firstCarryEffect, gprNumber, rexB, rexR, modrmRm, modrmReg, addSpec]

theorem firstCarry_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x115587) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (firstCarryEffect t).Holds t u ∧ AgreesExcept (components (exponentFrameBase s)) t u := by
  obtain ⟨fuel, u, he, hr, _, hh⟩ := firstCarry_correct ctx t
    (readyToStep hf.machine hf.bindingsSupported)
    (programText_slice (programLoaded_codeIn hf.loaded) 0x15587 firstCarryBytes
      (by decide) (by decide +kernel)) ⟨hf, hip⟩
  have hb : AgreesExcept (components (exponentFrameBase s)) t u :=
    hh.agrees.mono (by simp [firstCarryEffect, Effect.components, components])
  exact ⟨u, fuel, he, frame_of_agrees ctx hf hr hb, hh, hb⟩

end P256.Proofs.Sec1.SquareRoot.SquareFour
