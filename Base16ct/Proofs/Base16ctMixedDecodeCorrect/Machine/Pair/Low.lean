import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Basic
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Pair.Effects
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Alu32
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Alu32.Immediate
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.BitOps.Extensions
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.BitOps.Sar
import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Arithmetic
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import Base16ct.Proofs.Copied.Md5.Proofs.Block.Rounds.Register.Lea
namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Base16ct.Proofs.Copied.Md5.Proofs.Block
open Base16ct.Proofs.Copied.Md5.Proofs.Block.Rounds.Register

attribute [local x86_compose] movzxR32M8Effect

private theorem low_read64_low32 (s : RamState) (r : BitVec 5) :
    ((Operand.reg r : Operand 64).read s).setWidth 32 =
      (Operand.reg r : Operand 32).read s := by
  simp [Operand.read]

attribute [local x86_compose] BitVec.setWidth_setWidth_of_le BitVec.setWidth_add
  low_read64_low32 shiftCount

private def lowMask (x a b : BitVec 32) : BitVec 32 :=
  ((((x - b) &&& (a - x)).setWidth 16).signExtend 32).sshiftRight 8

private def lowSource (s : RamState) : BitVec 8 :=
  (Operand.mem ((Operand.reg 7 : Operand 64).read s +
    (Operand.reg 0 : Operand 64).read s * 2 + 1) : Operand 8).read s

private def lowDigitEffect (s : RamState) : Effect :=
  let x := (lowSource s).setWidth 32
  { rip := 0x10028e
    writes := [⟨(Operand.reg 10 : Operand 64), (lowSource s).setWidth 64⟩,
      ⟨(Operand.reg 11 : Operand 64), (lowMask x 47 58).setWidth 64⟩,
      ⟨(Operand.reg 3 : Operand 64), ((x - 47) &&& lowMask x 47 58).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

private def lowUpperEffect (s : RamState) : Effect :=
  let x := (Operand.reg 10 : Operand 32).read s
  { rip := 0x1002b0
    writes := [⟨(Operand.reg 5 : Operand 64), ((x - 71) &&& (64 - x)).setWidth 64⟩,
      ⟨(Operand.reg 11 : Operand 64), (lowMask x 64 71).setWidth 64⟩,
      ⟨(Operand.reg 14 : Operand 64),
        (((x - 54) &&& lowMask x 64 71) +
          (Operand.reg 3 : Operand 32).read s).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

private def lowFinalEffect (s : RamState) : Effect :=
  let x := (Operand.reg 10 : Operand 32).read s
  let y := (x - 86) &&& lowMask x 96 103
  { rip := 0x1002d8
    writes := [⟨(Operand.reg 11 : Operand 64), (lowMask x 96 103).setWidth 64⟩,
      ⟨(Operand.reg 10 : Operand 64), y.setWidth 64⟩,
      ⟨(Operand.reg 3 : Operand 64),
        (((Operand.reg 14 : Operand 32).read s + y - 1) |||
          (Operand.reg 8 : Operand 32).read s).setWidth 64⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

private def lowDigitBytes : List UInt8 :=
  [0x44, 0xf, 0xb6, 0x54, 0x47, 0x1, 0x41, 0xbb, 0x2f, 0x0, 0x0, 0x0, 0x45, 0x29,
    0xd3, 0x41, 0x8d, 0x5a, 0xc6, 0x44, 0x21, 0xdb, 0x44, 0xf, 0xbf, 0xdb, 0x41, 0xc1,
    0xfb, 0x8, 0x41, 0x8d, 0x5a, 0xd1, 0x44, 0x21, 0xdb]

private theorem lowDigit_block [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (LoadPre 0x100269 (fun s ↦ (Operand.reg 7 : Operand 64).read s +
        (Operand.reg 0 : Operand 64).read s * 2 + 1) 1)
      (codeRange 0x100269 lowDigitBytes) lowDigitEffect := by
  unfold lowDigitBytes
  md5_run_begin (forgetFlags_step (movzx_r_m8_rex_effect_step 0x100269 0x44
    (by unfold RexPrefix; decide) 32 (.inr rfl)
    (by intro seg; exact RexNoWPrefix.operand_size (by unfold RexNoWPrefix; decide) seg)
    2 (.sib 7 (some 0) 1 (.d8 1)) (by decide) (by decide) (by decide)))
  case pre =>
    intro s hs
    refine ⟨hs.rip, ?_⟩
    change MemReadable s ((Operand.reg 7 : Operand 64).read s +
      ((Operand.reg 0 : Operand 64).read s <<< 1) + 1) 1
    simpa only [BitVec.shiftLeft_eq_mul_twoPow,
      show BitVec.twoPow 64 1 = 2 from rfl] using hs.read
  case boundary =>
    intro _ _
    change 0x10026f#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (mov_r32_imm32_rex_effect_step 0x10026f 0x41 0xbb
    (by unfold RexNoWPrefix; decide) (by decide) 47))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x100269)
      (all := lowDigitBytes) 6 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x100275#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sub_r32_r32_rex_effect_step 0x100275 0x45 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x100269)
      (all := lowDigitBytes) 12 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x100278#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x100278 0x41
    (by unfold RexNoWPrefix; decide) 3 (.base 10 (.d8 0xc6))
    (by decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x100269)
      (all := lowDigitBytes) 15 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x10027c#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x10027c 0x44 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x100269)
      (all := lowDigitBytes) 19 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x10027f#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (movsx_r32_r16_effect_step 0x10027f 0x44 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x100269)
      (all := lowDigitBytes) 22 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x100283#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sar_r32_imm8_rex_effect_step 0x100283 0x41 0xfb 8
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x100269)
      (all := lowDigitBytes) 26 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x100287#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x100287 0x41
    (by unfold RexNoWPrefix; decide) 3 (.base 10 (.d8 0xd1))
    (by decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x100269)
      (all := lowDigitBytes) 30 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x10028b#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x10028b 0x44 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x100269)
      (all := lowDigitBytes) 34 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x10028e#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hEffect
  apply hEffect.weaken
  · x86_norm [lowDigitEffect]
  · x86_norm [lowDigitEffect, lowMask, lowSource, BitVec.sub_eq_add_neg,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 1 = 2 from rfl]
    exact ⟨rfl, rfl⟩
  · intro i; left; cases i <;> rfl
  · x86_norm [lowDigitEffect]

private def lowUpperBytes : List UInt8 :=
  [0x41, 0xbb, 0x40, 0x0, 0x0, 0x0, 0x45, 0x29, 0xd3, 0x41, 0x8d, 0x6a, 0xb9, 0x44,
    0x21, 0xdd, 0x44, 0xf, 0xbf, 0xdd, 0x41, 0xc1, 0xfb, 0x8, 0x45, 0x8d, 0x72, 0xca,
    0x45, 0x21, 0xde, 0x41, 0x1, 0xde]

private theorem lowUpper_block [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x10028e)
      (codeRange 0x10028e lowUpperBytes) lowUpperEffect := by
  unfold lowUpperBytes
  md5_run_begin (forgetFlags_step (mov_r32_imm32_rex_effect_step 0x10028e 0x41 0xbb
    (by unfold RexNoWPrefix; decide) (by decide) 64))
  case boundary =>
    intro _ _
    change 0x100294#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sub_r32_r32_rex_effect_step 0x100294 0x45 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x10028e)
      (all := lowUpperBytes) 6 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x100297#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x100297 0x41
    (by unfold RexNoWPrefix; decide) 5 (.base 10 (.d8 0xb9))
    (by decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x10028e)
      (all := lowUpperBytes) 9 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x10029b#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x10029b 0x44 0xdd
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x10028e)
      (all := lowUpperBytes) 13 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x10029e#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (movsx_r32_r16_effect_step 0x10029e 0x44 0xdd
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x10028e)
      (all := lowUpperBytes) 16 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002a2#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sar_r32_imm8_rex_effect_step 0x1002a2 0x41 0xfb 8
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x10028e)
      (all := lowUpperBytes) 20 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002a6#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x1002a6 0x45
    (by unfold RexNoWPrefix; decide) 6 (.base 10 (.d8 0xca))
    (by decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x10028e)
      (all := lowUpperBytes) 24 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002aa#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x1002aa 0x45 0xde
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x10028e)
      (all := lowUpperBytes) 28 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002ad#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (add_r32_r32_rex_effect_step 0x1002ad 0x41 0xde
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x10028e)
      (all := lowUpperBytes) 31 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002b0#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hEffect
  apply hEffect.weaken
  · x86_norm [lowUpperEffect]
  · x86_norm [lowUpperEffect, lowMask, lowSource, BitVec.sub_eq_add_neg,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 1 = 2 from rfl]
    exact ⟨rfl, rfl, rfl⟩
  · intro i; left; cases i <;> rfl
  · x86_norm [lowUpperEffect]

private def lowFinalBytes : List UInt8 :=
  [0x41, 0xbb, 0x60, 0x0, 0x0, 0x0, 0x45, 0x29, 0xd3, 0x41, 0x8d, 0x5a, 0x99, 0x44,
    0x21, 0xdb, 0x44, 0xf, 0xbf, 0xdb, 0x41, 0xc1, 0xfb, 0x8, 0x41, 0x83, 0xc2, 0xaa,
    0x45, 0x21, 0xda, 0x43, 0x8d, 0x1c, 0x32, 0xff, 0xcb, 0x44, 0x9, 0xc3]

set_option maxHeartbeats 400000 in
private theorem lowFinal_block [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1002b0)
      (codeRange 0x1002b0 lowFinalBytes) lowFinalEffect := by
  unfold lowFinalBytes
  md5_run_begin (forgetFlags_step (mov_r32_imm32_rex_effect_step 0x1002b0 0x41 0xbb
    (by unfold RexNoWPrefix; decide) (by decide) 96))
  case boundary =>
    intro _ _
    change 0x1002b6#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sub_r32_r32_rex_effect_step 0x1002b6 0x45 0xd3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 6 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002b9#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x1002b9 0x41
    (by unfold RexNoWPrefix; decide) 3 (.base 10 (.d8 0x99))
    (by decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 9 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002bd#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x1002bd 0x44 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 13 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002c0#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (movsx_r32_r16_effect_step 0x1002c0 0x44 0xdb
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 16 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002c4#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (sar_r32_imm8_rex_effect_step 0x1002c4 0x41 0xfb 8
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 20 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002c8#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (add_r32_imm8_rex_effect_step 0x1002c8 0x41 0xc2 0xaa
    (by unfold RexNoWPrefix; decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 24 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002cc#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (and_r32_r32_rex_effect_step 0x1002cc 0x45 0xda
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 28 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002cf#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (lea_r32_rex_effect_step 0x1002cf 0x43
    (by unfold RexNoWPrefix; decide) 3 (.sib 10 (some 14) 0 .none)
    (by decide) (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 31 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002d3#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (dec_r32_effect_step 0x1002d3 0xcb (by decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 35 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002d5#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  md5_run_then (forgetFlags_step (or_r32_r32_rex_effect_step 0x1002d5 0x44 0xc3
    (by unfold RexNoWPrefix; decide) (by decide)))
  case sub =>
    exact codeRange_mem_of_drop (p := 0x1002b0)
      (all := lowFinalBytes) 37 (by decide +kernel)
  case boundary =>
    intro _ _
    change 0x1002d8#64 ≠ boundary.rip
    exact outsideMixed_ne hOutside (by decide) (by decide)
  apply AdvancesBlock.block_end
  intro s t _ hEffect
  apply hEffect.weaken
  · x86_norm [lowFinalEffect]
  · x86_norm [lowFinalEffect, lowMask, lowSource, BitVec.sub_eq_add_neg,
      BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 1 = 2 from rfl]
    refine ⟨rfl, rfl, ?_⟩
    x86_norm [BitVec.twoPow_zero, BitVec.mul_one, low_read64_low32,
      BitVec.add_assoc]
    ac_rfl
  · intro i; left; cases i <;> rfl
  · x86_norm [lowFinalEffect]

private theorem low_read32 {s : RamState} {r : BitVec 5} {v : BitVec 64}
    (h : (Operand.reg r : Operand 64).read s = v) :
    (Operand.reg r : Operand 32).read s = v.setWidth 32 := by
  simpa [Operand.read] using congrArg (fun x : BitVec 64 ↦ x.setWidth 32) h

theorem low_pair_advances [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {hi lo : UInt8} (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : OutsideMixed boundary.rip) (hRip : s.RIP = 0x100269)
    (hReadable : MemReadable s ((Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s * 2 + 1) 1)
    (hLo : (Operand.mem ((Operand.reg 7 : Operand 64).read s +
      (Operand.reg 0 : Operand 64).read s * 2 + 1) : Operand 8).read s = lo.toBitVec)
    (hHi : (Operand.reg 8 : Operand 64).read s = (high32 hi).zeroExtend 64) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = 0x1002d8 ∧
      (Operand.reg 3 : Operand 64).read t = (pairWord hi lo).zeroExtend 64 ∧
      AgreesExcept [.reg 5, .reg 14, .reg 10, .reg 11, .reg 3, .flags, .rip] s t := by
  obtain ⟨fa, a, runA, readyA, _, effectA⟩ := lowDigit_block boundary hOutside s hReady
    (program_text_slice hCode 0x269 0x25 (by decide +kernel)) ⟨hRip, hReadable⟩
  have frameA : AgreesExcept [.reg 10, .reg 11, .reg 3, .flags, .rip] s a := effectA.agrees
  have codeA := frameA.codeIn (by simp [Component.Covers]) hCode
  obtain ⟨fb, b, runB, readyB, _, effectB⟩ := lowUpper_block boundary hOutside a readyA
    (program_text_slice codeA 0x28e 0x22 (by decide +kernel)) effectA.rip
  have frameB : AgreesExcept [.reg 5, .reg 11, .reg 14, .flags, .rip] a b := effectB.agrees
  have codeB := frameB.codeIn (by simp [Component.Covers]) codeA
  obtain ⟨fc, t, runC, readyC, _, effectC⟩ := lowFinal_block boundary hOutside b readyB
    (program_text_slice codeB 0x2b0 0x28 (by decide +kernel)) effectB.rip
  have frameC : AgreesExcept [.reg 11, .reg 10, .reg 3, .flags, .rip] b t :=
    effectC.agrees
  have frame : AgreesExcept [.reg 5, .reg 14, .reg 10, .reg 11, .reg 3, .flags, .rip] s t :=
    ((frameA.trans frameB).trans frameC).mono (by simp)
  refine ⟨fa + fb + fc, t, (runA.trans runB).trans runC, readyC,
    frame.codeIn (by simp [Component.Covers]) hCode, effectC.rip, ?_, frame⟩
  have hByte : lowSource s = lo.toBitVec := hLo
  have ha10 : (Operand.reg 10 : Operand 32).read a = lo.toBitVec.setWidth 32 := by
    simpa (config := { decide := true }) only [lowDigitEffect, hByte,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] using low_read32 effectA.writes.1
  have ha3 : (Operand.reg 3 : Operand 32).read a =
      ((lo.toBitVec.setWidth 32 - 47) &&& lowMask (lo.toBitVec.setWidth 32) 47 58) := by
    simpa (config := { decide := true }) only [lowDigitEffect, hByte,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] using low_read32 effectA.writes.2.2
  have hb10 : (Operand.reg 10 : Operand 32).read b = lo.toBitVec.setWidth 32 :=
    (frameB.read (by simp)).trans ha10
  have hb8 : (Operand.reg 8 : Operand 32).read b = high32 hi := by
    simpa (config := { decide := true }) only [BitVec.setWidth_setWidth_of_le,
      BitVec.setWidth_eq] using low_read32 (((frameA.trans frameB).read (by simp)).trans hHi)
  have hb14 : (Operand.reg 14 : Operand 32).read b =
      ((lo.toBitVec.setWidth 32 - 54) &&& lowMask (lo.toBitVec.setWidth 32) 64 71) +
      ((lo.toBitVec.setWidth 32 - 47) &&& lowMask (lo.toBitVec.setWidth 32) 47 58) := by
    simpa (config := { decide := true }) only [lowUpperEffect, ha10, ha3,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq] using low_read32 effectB.writes.2.2
  have hResult := effectC.writes.2.2
  change (Operand.reg 3 : Operand 64).read t =
    (((Operand.reg 14 : Operand 32).read b +
      (((Operand.reg 10 : Operand 32).read b - 86) &&&
        lowMask ((Operand.reg 10 : Operand 32).read b) 96 103) - 1) |||
      (Operand.reg 8 : Operand 32).read b).setWidth 64 at hResult
  rw [hb10, hb8, hb14] at hResult
  simpa only [pairWord, low32, lowMask, BitVec.and_comm, BitVec.add_comm] using hResult

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
