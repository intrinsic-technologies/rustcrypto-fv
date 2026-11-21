import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Contracts
import Md5.Proofs.Buffered.Finalize.Store8
import Md5.Proofs.Buffered.Xor
import Md5.Proofs.Block.Rounds.Store.Compose
import Md5.Proofs.Block.Execution
import Md5.Proofs.MemoryRoutines.Register.Compose

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] addR64Imm32Effect

@[local x86_local] theorem addR64Imm32Effect_local (p : BitVec 64) (dst : BitVec 5)
    (imm : BitVec 32) : Effect.Local (addR64Imm32Effect p dst imm) := by
  refine ⟨fun _ _ _ ↦ rfl, fun s t h ↦ ?_, fun _ _ _ ↦ rfl,
    fun s t h i _ ↦ ?_, fun _ ↦ ?_⟩
  · simp only [addR64Imm32Effect, h.read_reg]
  · cases i <;> simp [addR64Imm32Effect, Effect.flag, h.read_reg]
  · simp [addR64Imm32Effect, Write.Full, Operand.Full]

def paddingBytes (variant : Variant := .original) : List UInt8 :=
  match variant with
  | .original | .finalize => [0x4c, 0x89, 0xfb, 0x48, 0x83, 0xf3, 0x3f, 0x42, 0xc6, 0x44, 0x3c, 0x60, 0x80,
    0x4a, 0x8d, 0x3c, 0x3c, 0x48, 0x83, 0xc7, 0x61, 0x31, 0xf6, 0x48, 0x89, 0xda]
  | .discard => [0x4c,0x89,0xfb,0x48,0x83,0xf3,0x3f,0x42,0xc6,0x84,0x3c,0x88,0,0,0,0x80,0x4a,0x8d,0x3c,0x3c,0x48,0x81,0xc7,0x89,0,0,0,0x31,0xf6,0x48,0x89,0xda]

structure PaddingPre (s : RamState) (variant : Variant := .original) : Prop extends Storage variant.toKind s where
  rip : s.RIP = (match variant with | .original => 0x100acf | .finalize => 0x10115f | .discard => 0x10163c)
  positionBound : ((.reg 15 : Operand 64).read s).toNat < 64

def paddingEffect (s : RamState) (variant : Variant := .original) : Effect :=
  let pos := (.reg 15 : Operand 64).read s
  { rip := match variant with | .original => 0x100ae9 | .finalize => 0x101179 | .discard => 0x10165c
    writes := [⟨(.reg 3 : Operand 64), pos ^^^ 63⟩,
      ⟨(.mem (stackPtr s + pos + BitVec.ofNat 64 variant.tailOffset) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + pos + BitVec.ofNat 64 (variant.tailOffset + 1)⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), pos ^^^ 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 600000 in
theorem padding_execution {variant : Variant} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s => PaddingPre s variant) (codeRange (match variant with | .original => 0x100acf | .finalize => 0x10115f | .discard => 0x10163c) (paddingBytes variant)) (fun s => paddingEffect s variant) := by
  cases variant with
  | original =>
      simp only [paddingBytes]

      md5_run_begin (mov_r64_r64_effect_step 0x100acf 0x4c 0xfb
        (by unfold RexWPrefix; decide) (by decide))
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xad2 (by decide +kernel)
      md5_run_then (xor_r64_imm8_effect_step 0x100ad2 0x48 0xf3 63
        (by unfold RexWPrefix; decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100acf) 3 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xad6 (by decide +kernel)
      md5_run_then (mov_m8_imm8_rex_effect_step 0x100ad6 0x42
        (by unfold RexPrefix; decide) (.sib 4 (some 15) 0 (.d8 96))
        (by decide) (by decide) (by decide) 128)
      case sub => exact codeRange_mem_of_drop (p := 0x100acf) 7 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hs : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        have hp : (.reg 15 : Operand 64).read t = (.reg 15 : Operand 64).read s :=
          hE.agrees.read (by x86_norm)
        have hw := h.toStorage.stackWritable (((.reg 15 : Operand 64).read s).toNat + 96) 1
          (by have := h.positionBound; change _ ≤ 296; omega)
        have hc (off len : Nat) (hcode : off + len ≤ Extracted.textBytes.size) :=
          h.toStorage.stackApart (offset := ((.reg 15 : Operand 64).read s).toNat + 96)
            (len := 1) (codeOffset := off) (codeLen := len)
            (by have := h.positionBound; change _ ≤ 296; omega) hcode
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hw
        · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hc 0xad6 6 (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip (show
            (movM8Imm8RexEffect 0x100ad6 (.sib 4 (some 15) 0 (.d8 96)) 128 t).components =
              [.mem (stackPtr t + (.reg 15 : Operand 64).read t + 96) 1, .rip] by
            x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero, stackPtr]; rfl)
          rw [hs, hp]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hc 0xacf 26 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xadc (by decide +kernel)
      md5_run_then (lea_r64_effect_step 0x100adc 0x4a (by unfold RexWPrefix; decide)
        7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100acf) 13 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xae0 (by decide +kernel)
      md5_run_then (add_r64_imm8_effect_step 0x100ae0 0x48 0xc7 97
        (by unfold RexWPrefix; decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100acf) 17 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xae4 (by decide +kernel)
      md5_run_then (xor_r32_r32_effect_step 0x100ae4 0xf6 (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100acf) 21 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xae6 (by decide +kernel)
      md5_run_then (mov_r64_r64_effect_step 0x100ae6 0x48 0xda
        (by unfold RexWPrefix; decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x100acf) 23 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xae9 (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect]
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
        simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
      · intro i; cases i <;> x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect]
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
        simp [Operand.read]
  | finalize =>
      simp only [paddingBytes]

      md5_run_begin (mov_r64_r64_effect_step 0x10115f 0x4c 0xfb
        (by unfold RexWPrefix; decide) (by decide))
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1162 (by decide +kernel)
      md5_run_then (xor_r64_imm8_effect_step 0x101162 0x48 0xf3 63
        (by unfold RexWPrefix; decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10115f) 3 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1166 (by decide +kernel)
      md5_run_then (mov_m8_imm8_rex_effect_step 0x101166 0x42
        (by unfold RexPrefix; decide) (.sib 4 (some 15) 0 (.d8 96))
        (by decide) (by decide) (by decide) 128)
      case sub => exact codeRange_mem_of_drop (p := 0x10115f) 7 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hs : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        have hp : (.reg 15 : Operand 64).read t = (.reg 15 : Operand 64).read s :=
          hE.agrees.read (by x86_norm)
        have hw := h.toStorage.stackWritable (((.reg 15 : Operand 64).read s).toNat + 96) 1
          (by have := h.positionBound; change _ ≤ 296; omega)
        have hc (off len : Nat) (hcode : off + len ≤ Extracted.textBytes.size) :=
          h.toStorage.stackApart (offset := ((.reg 15 : Operand 64).read s).toNat + 96)
            (len := 1) (codeOffset := off) (codeLen := len)
            (by have := h.positionBound; change _ ≤ 296; omega) hcode
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hw
        · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hc 0x1166 6 (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip (show
            (movM8Imm8RexEffect 0x101166 (.sib 4 (some 15) 0 (.d8 96)) 128 t).components =
              [.mem (stackPtr t + (.reg 15 : Operand 64).read t + 96) 1, .rip] by
            x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero, stackPtr]; rfl)
          rw [hs, hp]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hc 0x115f 26 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x116c (by decide +kernel)
      md5_run_then (lea_r64_effect_step 0x10116c 0x4a (by unfold RexWPrefix; decide)
        7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10115f) 13 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1170 (by decide +kernel)
      md5_run_then (add_r64_imm8_effect_step 0x101170 0x48 0xc7 97
        (by unfold RexWPrefix; decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10115f) 17 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1174 (by decide +kernel)
      md5_run_then (xor_r32_r32_effect_step 0x101174 0xf6 (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10115f) 21 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1176 (by decide +kernel)
      md5_run_then (mov_r64_r64_effect_step 0x101176 0x48 0xda
        (by unfold RexWPrefix; decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10115f) 23 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1179 (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect]
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
        simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
      · intro i; cases i <;> x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect]
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
        simp [Operand.read]
  | discard =>
      simp only [paddingBytes]

      md5_run_begin (mov_r64_r64_effect_step 0x10163c 0x4c 0xfb
        (by unfold RexWPrefix; decide) (by decide))
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x163f (by decide +kernel)
      md5_run_then (xor_r64_imm8_effect_step 0x10163f 0x48 0xf3 63
        (by unfold RexWPrefix; decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10163c) 3 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1643 (by decide +kernel)
      md5_run_then (mov_m8_imm8_rex_effect_step 0x101643 0x42
        (by unfold RexPrefix; decide) (.sib 4 (some 15) 0 (.d32 136))
        (by decide) (by decide) (by decide) 128)
      case sub => exact codeRange_mem_of_drop (p := 0x10163c) 7 (by decide +kernel)
      case mid =>
        intro s t h hE hO
        have hs : stackPtr t = stackPtr s := hE.agrees.read (n := 64) (r := 4) (by x86_norm)
        have hp : (.reg 15 : Operand 64).read t = (.reg 15 : Operand 64).read s :=
          hE.agrees.read (by x86_norm)
        have hw := h.toStorage.stackWritable (((.reg 15 : Operand 64).read s).toNat + 136) 1
          (by have := h.positionBound; change _ ≤ 288; omega)
        have hc (off len : Nat) (hcode : off + len ≤ Extracted.textBytes.size) :=
          h.toStorage.stackApart (offset := ((.reg 15 : Operand 64).read s).toNat + 136)
            (len := 1) (codeOffset := off) (codeLen := len)
            (by have := h.positionBound; change _ ≤ 288; omega) hcode
        refine ⟨Memory.StorePre.of_holds hE (hO true) (by x86_norm) ?_ ?_, ?_⟩
        · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hw
        · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hc 0x1643 9 (by decide +kernel)
        · apply Effect.avoids_of_components_mem_rip (show
            (movM8Imm8RexEffect 0x101643 (.sib 4 (some 15) 0 (.d32 136)) 128 t).components =
              [.mem (stackPtr t + (.reg 15 : Operand 64).read t + 136) 1, .rip] by
            x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.shiftLeft_zero, stackPtr]; rfl)
          rw [hs, hp]
          simpa [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, stackPtr, Operand.read, Extracted.textAddress]
            using hc 0x163c 32 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x164c (by decide +kernel)
      md5_run_then (lea_r64_effect_step 0x10164c 0x4a (by unfold RexWPrefix; decide)
        7 (.sib 4 (some 15) 0 .none) (by decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10163c) 16 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1650 (by decide +kernel)
      md5_run_then (add_r64_imm32_effect_step 0x101650 0x48 0xc7 137
        (by unfold RexWPrefix; decide) (by decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10163c) 20 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1657 (by decide +kernel)
      md5_run_then (xor_r32_r32_effect_step 0x101657 0xf6 (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10163c) 27 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1659 (by decide +kernel)
      md5_run_then (mov_r64_r64_effect_step 0x101659 0x48 0xda
        (by unfold RexWPrefix; decide) (by decide))
      case sub => exact codeRange_mem_of_drop (p := 0x10163c) 29 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x165c (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect]
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
        simp [Operand.read, gprNumber, rexB, rexR, modrmRm, modrmReg]
      · intro i; cases i <;> x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect]
      · x86_norm [Variant.toKind, Variant.tailOffset, Variant.resultOffset, Variant.preparedRip, paddingEffect, stackPtr, BitVec.add_zero, BitVec.shiftLeft_zero]
        simp [Operand.read]

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
