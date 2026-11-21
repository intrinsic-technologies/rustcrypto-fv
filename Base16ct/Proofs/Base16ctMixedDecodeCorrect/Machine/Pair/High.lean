import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Pair.Effects
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Alu32
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.BitOps.Extensions
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.BitOps.Shifts
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Arithmetic
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Base16ct.Proofs.Copied.Md5.Proofs.Block
open Base16ct.Proofs.Copied.Md5.Proofs.Block.Rounds.Register Base16ct.Proofs.Copied.Md5.Proofs.Buffered.FinalizeReset.Length

private theorem high_read_low32 (s : RamState) (r : BitVec 5) :
    ((Operand.reg r : Operand 64).read s).setWidth 32 =
      (Operand.reg r : Operand 32).read s := by
  simp [Operand.read]

attribute [local x86_compose] BitVec.setWidth_setWidth_of_le BitVec.setWidth_add
  high_read_low32 shiftCount

private def highRangeMask (x a b : BitVec 32) : BitVec 32 :=
  (((x + b) &&& (a - x)).setWidth 16).signExtend 32 >>> 8

private def highDigitEffect (s : RamState) : Effect :=
  let x := (Operand.reg 8 : Operand 32).read s
  let m := highRangeMask x 47 (-58)
  { rip := 0x100217
    writes := [⟨(.reg 10 : Operand 64), m.zeroExtend 64⟩,
      ⟨(.reg 11 : Operand 64), ((x + 4049) &&& m).zeroExtend 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

private def highUpperEffect (s : RamState) : Effect :=
  let x := (Operand.reg 8 : Operand 32).read s
  let m := highRangeMask x 64 (-71)
  { rip := 0x10023c
    writes := [⟨(.reg 10 : Operand 64), m.zeroExtend 64⟩,
      ⟨(.reg 3 : Operand 64), (((x + 4042) &&& m) +
        (Operand.reg 11 : Operand 32).read s).zeroExtend 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

private def highLowerEffect (s : RamState) : Effect :=
  let x := (Operand.reg 8 : Operand 32).read s
  let a := (x + (-103)) &&& (96 - x)
  let m := (a.setWidth 16).signExtend 32 >>> 8
  { rip := 0x100269
    writes := [⟨(.reg 10 : Operand 64), m.zeroExtend 64⟩,
      ⟨(.reg 11 : Operand 64), a.zeroExtend 64⟩,
      ⟨(.reg 8 : Operand 64),
        (((((x + 4010) &&& m) + (Operand.reg 3 : Operand 32).read s) <<< 4) +
          (-16)).zeroExtend 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

private def highDigitBytes : List UInt8 :=
  [0x41, 0xba, 0x2f, 0x0, 0x0, 0x0, 0x45, 0x29, 0xc2, 0x45, 0x8d, 0x58, 0xc6, 0x45,
    0x21, 0xd3, 0x45, 0xf, 0xbf, 0xd3, 0x41, 0xc1, 0xea, 0x8, 0x45, 0x8d, 0x98, 0xd1,
    0xf, 0x0, 0x0, 0x45, 0x21, 0xd3]

set_option maxRecDepth 4096 in
private theorem highDigit_block [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x1001f5)
      (codeRange 0x1001f5 highDigitBytes) highDigitEffect := by
  unfold highDigitBytes
  md5_run_begin (forgetFlags_step (mov_r32_imm32_rex_effect_step 0x1001f5 0x41 0xba
    (by unfold RexNoWPrefix; decide) (by decide) 47))
  case boundary =>
    intro _ _
    change (0x1001fb : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sub_r32_r32_rex_effect_step 0x1001fb 0x45 0xc2
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x1001f5) 6 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x1001fe : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x1001fe 0x45
    (by unfold RexNoWPrefix; decide) 3 (.base 8 (.d8 0xc6)) (by decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x1001f5) 9 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100202 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x100202 0x45 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x1001f5) 13 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100205 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (movsx_r32_r16_effect_step 0x100205 0x45 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x1001f5) 16 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100209 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (shr_r32_imm8_rex_effect_step 0x100209 0x41 0xea 8
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x1001f5) 20 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x10020d : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x10020d 0x45
    (by unfold RexNoWPrefix; decide) 3 (.base 8 (.d32 4049)) (by decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x1001f5) 24 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100214 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x100214 0x45 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x1001f5) 31 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100217 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [highDigitEffect]
  · x86_norm [highDigitEffect, highRangeMask, BitVec.setWidth_add, high_read_low32]
    exact ⟨rfl, rfl⟩
  · intro i; left; cases i <;> rfl
  · x86_norm [highDigitEffect]

private def highUpperBytes : List UInt8 :=
  [0x41, 0xba, 0x40, 0x0, 0x0, 0x0, 0x45, 0x29, 0xc2, 0x41, 0x8d, 0x58, 0xb9, 0x44,
    0x21, 0xd3, 0x44, 0xf, 0xbf, 0xd3, 0x41, 0xc1, 0xea, 0x8, 0x41, 0x8d, 0x98, 0xca,
    0xf, 0x0, 0x0, 0x44, 0x21, 0xd3, 0x44, 0x1, 0xdb]

set_option maxRecDepth 4096 in
private theorem highUpper_block [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100217)
      (codeRange 0x100217 highUpperBytes) highUpperEffect := by
  unfold highUpperBytes
  md5_run_begin (forgetFlags_step (mov_r32_imm32_rex_effect_step 0x100217 0x41 0xba
    (by unfold RexNoWPrefix; decide) (by decide) 64))
  case boundary =>
    intro _ _
    change (0x10021d : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sub_r32_r32_rex_effect_step 0x10021d 0x45 0xc2
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x100217) 6 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100220 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x100220 0x41
    (by unfold RexNoWPrefix; decide) 3 (.base 8 (.d8 0xb9)) (by decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x100217) 9 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100224 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x100224 0x44 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x100217) 13 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100227 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (movsx_r32_r16_effect_step 0x100227 0x44 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x100217) 16 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x10022b : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (shr_r32_imm8_rex_effect_step 0x10022b 0x41 0xea 8
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x100217) 20 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x10022f : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x10022f 0x41
    (by unfold RexNoWPrefix; decide) 3 (.base 8 (.d32 4042)) (by decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x100217) 24 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100236 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x100236 0x44 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x100217) 31 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100239 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (add_r32_r32_rex_effect_step 0x100239 0x44 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x100217) 34 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x10023c : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [highUpperEffect]
  · x86_norm [highUpperEffect, highRangeMask, BitVec.setWidth_add, high_read_low32]
    exact ⟨rfl, rfl⟩
  · intro i; left; cases i <;> rfl
  · x86_norm [highUpperEffect]

private def highLowerBytes : List UInt8 :=
  [0x41, 0xba, 0x60, 0x0, 0x0, 0x0, 0x45, 0x29, 0xc2, 0x45, 0x8d, 0x58, 0x99, 0x45,
    0x21, 0xd3, 0x45, 0xf, 0xbf, 0xd3, 0x41, 0xc1, 0xea, 0x8, 0x41, 0x81, 0xc0, 0xaa,
    0xf, 0x0, 0x0, 0x45, 0x21, 0xd0, 0x41, 0x1, 0xd8, 0x41, 0xc1, 0xe0, 0x4, 0x41,
    0x83, 0xc0, 0xf0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
private theorem highLower_block [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (fun s => s.RIP = 0x10023c)
      (codeRange 0x10023c highLowerBytes) highLowerEffect := by
  unfold highLowerBytes
  md5_run_begin (forgetFlags_step (mov_r32_imm32_rex_effect_step 0x10023c 0x41 0xba
    (by unfold RexNoWPrefix; decide) (by decide) 96))
  case boundary =>
    intro _ _
    change (0x100242 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sub_r32_r32_rex_effect_step 0x100242 0x45 0xc2
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 6 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100245 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x100245 0x45
    (by unfold RexNoWPrefix; decide) 3 (.base 8 (.d8 0x99)) (by decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 9 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100249 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x100249 0x45 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 13 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x10024c : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (movsx_r32_r16_effect_step 0x10024c 0x45 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 16 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100250 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (shr_r32_imm8_rex_effect_step 0x100250 0x41 0xea 8
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 20 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100254 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (add_r32_imm32_rex_effect_step 0x100254 0x41 0xc0 4010
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 24 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x10025b : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x10025b 0x45 0xd0
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 31 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x10025e : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (add_r32_r32_rex_effect_step 0x10025e 0x41 0xd8
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 34 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100261 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (shl_r32_imm8_rex_effect_step 0x100261 0x41 0xe0 4
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 37 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100265 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (add_r32_imm8_rex_effect_step 0x100265 0x41 0xc0 0xf0
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub => exact codeRange_mem_of_drop (p := 0x10023c) 41 (by decide +kernel)
  case boundary =>
    intro _ _
    change (0x100269 : BitVec 64) ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [highLowerEffect]
  · x86_norm [highLowerEffect, highRangeMask, BitVec.setWidth_add, high_read_low32]
    exact ⟨rfl, rfl, rfl⟩
  · intro i; left; cases i <;> rfl
  · x86_norm [highLowerEffect]

private theorem high_combination (c : UInt8) :
    let x := c.toBitVec.zeroExtend 32
    (((((x + 4010) &&& highRangeMask x 96 (-103)) +
      (((x + 4042) &&& highRangeMask x 64 (-71)) +
        ((x + 4049) &&& highRangeMask x 47 (-58)))) <<< 4) + (-16)) = high32 c := by
  simp only [highRangeMask, high32, BitVec.sub_eq_add_neg, BitVec.and_comm,
    BitVec.add_comm]

theorem high_pair_advances [Bindings] {s : RamState} {boundary : ReturnBoundary} {hi : UInt8}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : OutsideMixed boundary.rip) (hRip : s.RIP = 0x1001f0)
    (hReadable : MemReadable s ((Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s * 2) 1)
    (hByte : (Operand.mem ((Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s * 2) : Operand 8).read s = hi.toBitVec) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x100269 ∧
      (Operand.reg 8 : Operand 64).read t = (high32 hi).zeroExtend 64 ∧
      AgreesExcept [.reg 8, .reg 10, .reg 11, .reg 3, .flags, .rip] s t := by
  have hAddress : (AddrMode.sib 7 (some 0) 1 .none).addr s 0x1001f5 =
      (Operand.reg 7 : Operand 64).read s + (Operand.reg 0 : Operand 64).read s * 2 := by
    change (Operand.reg 7 : Operand 64).read s +
      ((Operand.reg 0 : Operand 64).read s <<< 1) + (0#64) = _
    simp only [BitVec.add_zero, BitVec.shiftLeft_eq_mul_twoPow,
      show BitVec.twoPow 64 1 = 2 from rfl]
  have hLoad := movzx_r_m8_rex_effect_step 0x1001f0 0x44 (by unfold RexPrefix; decide)
    32 (.inr rfl)
    (by intro seg; exact RexNoWPrefix.operand_size (by unfold RexNoWPrefix; decide) seg)
    0 (.sib 7 (some 0) 1 .none)
    (by decide) (by decide) (by decide)
  change StepEffect (LoadPre 0x1001f0
    (fun s => (AddrMode.sib 7 (some 0) 1 .none).addr s 0x1001f5) 1)
    (codeRange 0x1001f0 [0x44, 0xf, 0xb6, 0x4, 0x47])
    (movzxR32M8Effect 0x1001f0 5 8 (.sib 7 (some 0) 1 .none)) at hLoad
  have hLoadCode : CodeIn (codeRange 0x1001f0 [0x44, 0xf, 0xb6, 0x4, 0x47]) s :=
    program_text_slice hCode 0x1f0 5 (by decide +kernel)
  obtain ⟨u, hAu, hRu, hEu⟩ := hLoad.advances hReady hLoadCode
    ⟨hRip, by simpa (config := { decide := true }) only [hAddress] using hReadable⟩
    (by
      change (0x1001f5 : BitVec 64) ≠ boundary.rip
      exact outsideMixed_ne hOutside (by decide) (by decide))
  have hCu : CodeIn Extracted.programImage u := hEu.codeIn
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) hCode
  have hX64 : (Operand.reg 8 : Operand 64).read u = hi.toBitVec.zeroExtend 64 := by
    have h := hEu.writes
    change (Operand.reg 8 : Operand 64).read u =
      ((Operand.mem ((AddrMode.sib 7 (some 0) 1 .none).addr s 0x1001f5) :
        Operand 8).read s).zeroExtend 64 at h
    rw [hAddress, hByte] at h
    exact h
  have hX : (Operand.reg 8 : Operand 32).read u = hi.toBitVec.zeroExtend 32 := by
    have h := congrArg (BitVec.setWidth 32) hX64
    simpa (config := { decide := true }) only [high_read_low32, BitVec.setWidth_setWidth_of_le] using h
  obtain ⟨fd, d, hAd, hRd, _, hEd⟩ := highDigit_block boundary hOutside u hRu
    (program_text_slice hCu 0x1f5 34 (by decide +kernel)) hEu.rip
  have hCd : CodeIn Extracted.programImage d := hEd.codeIn
    (Effect.Avoids.of_noMem (by simp [highDigitEffect, Effect.components, Component.Covers]) _) hCu
  have hXd : (Operand.reg 8 : Operand 32).read d = hi.toBitVec.zeroExtend 32 :=
    (hEd.agrees.read (by simp [highDigitEffect, Effect.components])).trans hX
  have hDigit : (Operand.reg 11 : Operand 32).read d =
      ((hi.toBitVec.zeroExtend 32 + 4049) &&&
        highRangeMask (hi.toBitVec.zeroExtend 32) 47 (-58)) := by
    have h := congrArg (BitVec.setWidth 32) hEd.writes.2
    simpa (config := { decide := true }) only [highDigitEffect, high_read_low32, hX,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] using h
  obtain ⟨fu, v, hAv, hRv, _, hEv⟩ := highUpper_block boundary hOutside d hRd
    (program_text_slice hCd 0x217 37 (by decide +kernel)) hEd.rip
  have hCv : CodeIn Extracted.programImage v := hEv.codeIn
    (Effect.Avoids.of_noMem (by simp [highUpperEffect, Effect.components, Component.Covers]) _) hCd
  have hXv : (Operand.reg 8 : Operand 32).read v = hi.toBitVec.zeroExtend 32 :=
    (hEv.agrees.read (by simp [highUpperEffect, Effect.components])).trans hXd
  have hUpper : (Operand.reg 3 : Operand 32).read v =
      ((hi.toBitVec.zeroExtend 32 + 4042) &&&
        highRangeMask (hi.toBitVec.zeroExtend 32) 64 (-71)) +
      ((hi.toBitVec.zeroExtend 32 + 4049) &&&
        highRangeMask (hi.toBitVec.zeroExtend 32) 47 (-58)) := by
    have h := congrArg (BitVec.setWidth 32) hEv.writes.2
    simpa (config := { decide := true }) only [highUpperEffect, high_read_low32, hXd, hDigit,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] using h
  obtain ⟨fl, t, hAt, hRt, _, hEt⟩ := highLower_block boundary hOutside v hRv
    (program_text_slice hCv 0x23c 45 (by decide +kernel)) hEv.rip
  refine ⟨1 + fd + fu + fl, t, ((hAu.trans hAd).trans hAv).trans hAt, hRt,
    hEt.codeIn (Effect.Avoids.of_noMem
      (by simp [highLowerEffect, Effect.components, Component.Covers]) _) hCv,
    hEt.rip, ?_, ?_⟩
  · have h := hEt.writes.2.2
    rw [hXv, hUpper] at h
    have hc := congrArg (fun x : BitVec 32 => x.zeroExtend 64) (high_combination hi)
    exact h.trans hc
  · apply (((hEu.agrees.trans hEd.agrees).trans hEv.agrees).trans hEt.agrees).mono
    simp [movzxR32M8Effect, highDigitEffect, highUpperEffect, highLowerEffect, Effect.components]

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
