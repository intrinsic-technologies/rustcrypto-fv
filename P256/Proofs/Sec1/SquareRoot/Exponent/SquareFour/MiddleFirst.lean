import P256.Proofs.Sec1.SquareRoot.Exponent.SquareFour.FirstProducts
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.SquareFour

open P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def middleFirstBytes : List UInt8 :=
  [0x48, 0x89, 0xc1, 0x48, 0x89, 0xf0, 0x48, 0xf7, 0x64, 0x24, 0x58, 0x48, 0x89, 0x94, 0x24, 0xe8, 0x2, 0x0, 0x0, 0x49, 0x89, 0xc1, 0x48, 0x89, 0xf8, 0x48, 0xf7, 0xa4, 0x24, 0x98, 0x0, 0x0, 0x0, 0x49, 0x89, 0xc2, 0x48, 0x89, 0xd3, 0x48, 0x1, 0xe9, 0x4d, 0x11, 0xe2, 0x4c, 0x8b, 0xa4, 0x24, 0xe0, 0x2, 0x0, 0x0, 0x48, 0x83, 0xd3, 0x0, 0x4d, 0x1, 0xc2, 0x48, 0x83, 0xd3, 0x0, 0x4c, 0x1, 0xd9, 0x4c, 0x8b, 0x9c, 0x24, 0x88, 0x0, 0x0, 0x0, 0x49, 0x83, 0xd2, 0x0, 0x48, 0x83, 0xd3, 0x0]

def middleFirstEffect (s : RamState) : Effect :=
  let v0 := ((Operand.reg 0#5 : Operand 64).read s)
  let v1 := ((Operand.reg 6#5 : Operand 64).read s)
  let v2 := v1 * ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x58#64) : Operand 64).read s)
  let h2 := mulHigh64 v1 ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x58#64) : Operand 64).read s)
  let v3 := h2
  let v4 := v2
  let v5 := ((Operand.reg 7#5 : Operand 64).read s)
  let v6 := v5 * ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x98#64) : Operand 64).read s)
  let h6 := mulHigh64 v5 ((Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x98#64) : Operand 64).read s)
  let v7 := v6
  let v8 := h6
  let v9 := addSpec v0 ((Operand.reg 5#5 : Operand 64).read s)
  let v10 := adcSpec v7 ((Operand.reg 12#5 : Operand 64).read s) (BitVec.ofBool v9.2.CF)
  let v11 := adcSpec v8 0x0#64 (BitVec.ofBool v10.2.CF)
  let v12 := addSpec v10.1 ((Operand.reg 8#5 : Operand 64).read s)
  let v13 := adcSpec v11.1 0x0#64 (BitVec.ofBool v12.2.CF)
  let v14 := addSpec v9.1 ((Operand.reg 11#5 : Operand 64).read s)
  let v15 := adcSpec v12.1 0x0#64 (BitVec.ofBool v14.2.CF)
  let v16 := adcSpec v13.1 0x0#64 (BitVec.ofBool v15.2.CF)
  { rip := 0x11560d
    writes := [
      ⟨(Operand.reg 1#5 : Operand 64), v14.1⟩,
      ⟨(Operand.reg 0#5 : Operand 64), v6⟩,
      ⟨(Operand.reg 2#5 : Operand 64), h6⟩,
      ⟨(Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x2e8) : Operand 64), v3⟩,
      ⟨(Operand.reg 9#5 : Operand 64), v4⟩,
      ⟨(Operand.reg 10#5 : Operand 64), v15.1⟩,
      ⟨(Operand.reg 3#5 : Operand 64), v16.1⟩,
      ⟨(Operand.reg 12#5 : Operand 64), (Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x2e0) : Operand 64).read s⟩,
      ⟨(Operand.reg 11#5 : Operand 64), (Operand.mem ((Operand.reg 4#5 : Operand 64).read s + 0x88) : Operand 64).read s⟩]
    flags := some (.ofStatusFlags v16.2) }


theorem middleFirst_correct [Bindings] {origin : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre origin boundary x) :
    AdvanceTriple boundary (fun s => ExponentFrame origin s ∧ s.RIP = 0x1155ba)
      (codeRange 0x1155ba middleFirstBytes) (Effect.post middleFirstEffect) := by
  advance_begin (show StepEffect _ _ (movR64R64Effect 0x1155ba 1#5 0#5) from
    mov_r64_r64_effect_step 0x1155ba 0x48 0xc1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 0 3)
  case pre => intro s hP; exact hP.2
  case next =>
    intro s hP
    exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155bd (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x1155bd 0#5 6#5) from
    mov_r64_r64_effect_step 0x1155bd 0x48 0xf0 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 3 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155c0 (by decide))
  advance_then (show StepEffect _ _ (mulM64Effect 0x1155c0 (.sib 4 none 0 (.d8 0x58))) from
    mul_m64_effect_step 0x1155c0 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 0x58)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 6 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x58) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x58) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155c5 (by decide))
  advance_then (show StepEffect _ _ (movM64R64Effect 0x1155c5 2#5 (.sib 4 none 0 (.d32 0x2e8))) from
    mov_m64_r64_effect_step 0x1155c5 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 0x2e8)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 11 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        change MemWritable s (s.regValue .rsp + 0x2e8) 8
        rw [hP.1.rsp]
        exact stack_writable ctx hP.1 (offset := 0x2e8) (by decide) (by decide) (.inl ⟨rfl, by decide⟩)
      · x86_norm
        change RangeApart (s.regValue .rsp + 0x2e8) 8 0x1155c5 8
        rw [hP.1.rsp]
        exact stack_apart_code ctx (offset := 0x2e8) (len := 8) (codeOffset := 0x155c5) (codeLen := 8)
          (by decide) (by decide) (by decide)
    · apply Effect.avoids_codeRange
      x86_norm
      change RangeApart (s.regValue .rsp + 0x2e8) 8 0x1155ba middleFirstBytes.length
      rw [hP.1.rsp]
      exact stack_apart_code ctx (offset := 0x2e8) (len := 8) (codeOffset := 0x155ba) (codeLen := middleFirstBytes.length)
        (by decide) (by decide) (by decide)
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155cd (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x1155cd 9#5 0#5) from
    mov_r64_r64_effect_step 0x1155cd 0x49 0xc1 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 19 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155d0 (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x1155d0 0#5 7#5) from
    mov_r64_r64_effect_step 0x1155d0 0x48 0xf8 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 22 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155d3 (by decide))
  advance_then (show StepEffect _ _ (mulM64Effect 0x1155d3 (.sib 4 none 0 (.d32 0x98))) from
    mul_m64_effect_step 0x1155d3 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 0x98)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 25 8)
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
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155db (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x1155db 10#5 0#5) from
    mov_r64_r64_effect_step 0x1155db 0x49 0xc2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 33 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155de (by decide))
  advance_then (show StepEffect _ _ (movR64R64Effect 0x1155de 3#5 2#5) from
    mov_r64_r64_effect_step 0x1155de 0x48 0xd3 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 36 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155e1 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x1155e1 1#5 5#5) from
    add_r64_r64_effect_step 0x1155e1 0x48 0xe9 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 39 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155e4 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64R64Effect 0x1155e4 10#5 12#5) from
    adc_r64_r64_effect_step 0x1155e4 0x4d 0xe2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 42 3)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155e7 (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x1155e7 12#5 (.sib 4 none 0 (.d32 0x2e0))) from
    mov_r64_m64_effect_step 0x1155e7 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 0x2e0)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 45 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x2e0) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x2e0) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155ef (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x1155ef 3#5 0#8) from
    adc_r64_imm8_effect_step 0x1155ef 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 53 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155f3 (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x1155f3 10#5 8#5) from
    add_r64_r64_effect_step 0x1155f3 0x4d 0xc2 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 57 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155f6 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x1155f6 3#5 0#8) from
    adc_r64_imm8_effect_step 0x1155f6 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 60 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155fa (by decide))
  advance_then (show StepEffect _ _ (addR64R64Effect 0x1155fa 1#5 11#5) from
    add_r64_r64_effect_step 0x1155fa 0x4c 0xd9 (by simp [RexWPrefix]) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 64 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x155fd (by decide))
  advance_then (show StepEffect _ _ (movR64M64Effect 0x1155fd 11#5 (.sib 4 none 0 (.d32 0x88))) from
    mov_r64_m64_effect_step 0x1155fd 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 0x88)) (by decide) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 67 8)
  case mid =>
    intro s t hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_
      x86_norm
      change MemReadable s (s.regValue .rsp + 0x88) 8
      rw [hP.1.rsp]
      exact stack_readable ctx hP.1 (offset := 0x88) (by decide) (by decide)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15605 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x115605 10#5 0#8) from
    adc_r64_imm8_effect_step 0x115605 0x49 0xd2 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 75 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x15609 (by decide))
  advance_then_on [.CF] using (show StepEffect _ _ (adcR64Imm8Effect 0x115609 3#5 0#8) from
    adc_r64_imm8_effect_step 0x115609 0x48 0xd3 0 (by simp [RexWPrefix]) (by decide) (by decide))
  try (case sub => exact codeRange_slice_subset 0x1155ba middleFirstBytes 79 4)
  case mid =>
    intro s t hP hH hO hF
    refine ⟨?_, P256.Proofs.Common.EffectCompose.Effect.LocalOn.avoids (by simp only [x86_local_on]) (hO true) (hF true) ?_, ?_⟩
    · exact hH.rip_of (by x86_norm)
    · x86_avoid
    · x86_norm
      exact boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x1560d (by decide))
  advance_finish [middleFirstEffect, gprNumber, rexB, rexR, modrmRm, modrmReg, addSpec]

theorem middleFirst_run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : ExponentFrame s t) (hip : t.RIP = 0x1155ba) :
    ∃ u fuel, Advances boundary fuel t u ∧ ExponentFrame s u ∧
      (middleFirstEffect t).Holds t u := by
  obtain ⟨fuel, u, he, hr, _, hh⟩ := middleFirst_correct ctx t
    (readyToStep hf.machine hf.bindingsSupported)
    (programText_slice (programLoaded_codeIn hf.loaded) 0x155ba middleFirstBytes
      (by decide) (by decide +kernel)) ⟨hf, hip⟩
  refine ⟨u, fuel, he, frame_of_agrees ctx hf hr ?_, hh⟩
  refine ⟨?_, ?_, hh.agrees.rest, hh.agrees.grow⟩
  · intro c hn hm
    apply hh.agrees.agree c _ hm
    intro hc
    apply hn
    simp only [middleFirstEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      Write.component_reg, Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try contradiction
    all_goals simp [components]
  · intro a hn
    apply hh.agrees.memory a
    intro c hc ha
    simp only [middleFirstEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      Write.component_reg, Write.component_mem, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact False.elim ha
    obtain ⟨i, hi, he⟩ := ha
    apply hn (.mem (exponentFrameBase s + 0x2e8) 16) (by simp [components])
    refine ⟨i, by omega, ?_⟩
    change a = t.regValue .rsp + 0x2e8 + BitVec.ofNat 64 i at he
    rwa [hf.rsp] at he

end P256.Proofs.Sec1.SquareRoot.SquareFour
