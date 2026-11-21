import P256.Proofs.Common.Field.Montgomery.Schoolbook.CarryCompose
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.Carry
open P256.Proofs.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prefixBytes : List UInt8 :=
  [73, 137, 204, 77, 15, 175, 230, 76, 137, 224, 72, 247, 229, 72, 137, 213, 72, 137, 193, 76, 137, 224, 73, 247, 229, 73, 137, 208, 73, 137, 197, 77, 1, 253, 73, 131, 208, 0, 76, 1, 241]

def prefixEffect (s : RamState) : Effect :=
  let a := (Operand.reg 1 : Operand 64).read s * (Operand.reg 14 : Operand 64).read s
  let p0 := a * (Operand.reg 5 : Operand 64).read s
  let h0 := mulHigh64 a ((Operand.reg 5 : Operand 64).read s)
  let p1 := a * (Operand.reg 13 : Operand 64).read s
  let h1 := mulHigh64 a ((Operand.reg 13 : Operand 64).read s)
  let x := addSpec p1 ((Operand.reg 15 : Operand 64).read s)
  let xh := adcSpec h1 0 (BitVec.ofBool x.2.CF)
  let z := addSpec p0 ((Operand.reg 14 : Operand 64).read s)
  { rip := 0x1134b9
    writes := [⟨(Operand.reg 12 : Operand 64), a⟩,
      ⟨(Operand.reg 0 : Operand 64), p1⟩,
      ⟨(Operand.reg 2 : Operand 64), h1⟩,
      ⟨(Operand.reg 5 : Operand 64), h0⟩,
      ⟨(Operand.reg 1 : Operand 64), z.1⟩,
      ⟨(Operand.reg 8 : Operand 64), xh.1⟩,
      ⟨(Operand.reg 13 : Operand 64), x.1⟩]
    flags := some (.ofStatusFlags z.2) }

set_option maxHeartbeats 1200000 in
theorem prefix_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x113490)
      (codeRange 0x113490 prefixBytes) (Effect.post prefixEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x113490 0x49 0xcc (by simp [RexWPrefix]) rfl)
  case next => intro _ _; exact boundary_ne_program hout (inProgram_of_textOffset 0x13493 (by decide))
  advance_then (imul_r64_r64_effect_step 0x113493 0x4d 0xe6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 3 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [imulR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x13497 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x113497 0x4c 0xe0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x1349a (by decide))⟩
  advance_then (mul_r64_effect_step 0x11349a 0x48 0xe5 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [mulR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x1349d (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x11349d 0x48 0xd5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 13 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134a0 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1134a0 0x48 0xc1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 16 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134a3 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1134a3 0x4c 0xe0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 19 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134a6 (by decide))⟩
  advance_then (mul_r64_effect_step 0x1134a6 0x49 0xe5 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 22 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [mulR64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134a9 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1134a9 0x49 0xd0 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 25 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134ac (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1134ac 0x49 0xc5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 28 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [movR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134af (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x1134af 0x4d 0xfd (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 31 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [addR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134b2 (by decide))⟩
  advance_then_on [.CF] using (adc_r64_imm8_effect_step 0x1134b2 0x49 0xd0 0 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 34 4
  case mid =>
    intro s t hP hH hO hF
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [adcR64Imm8Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134b6 (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x1134b6 0x4c 0xf1 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x113490 prefixBytes 38 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [addR64R64Effect, Effect.components, Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x134b9 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t _ hH
  apply hH.weaken
  · x86_norm [prefixEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [prefixEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [prefixEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [prefixEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Sec1.SquareRoot.Square.Reduction.Body.Second
