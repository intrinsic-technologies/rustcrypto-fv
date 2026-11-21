import Base16ct.Proofs.EncodeStr.Lower.Machine.Interface
import Base16ct.Proofs.EncodeStr.Lower.Machine.ByteArithmetic
import Base16ct.Proofs.EncodeStr.Lower.Machine.Instructions.Or
import Base16ct.Proofs.Copied.P256.Proofs.Common.Field.Operations.Run.Compose
import Base16ct.Proofs.Copied.P256.Proofs.Common.SHA256.Compression.Support
import Base16ct.Proofs.Copied.Md5.Proofs.MemoryRoutines.Register.Compose
import Base16ct.Proofs.EncodeStr.Lower.Machine.Instructions.ByteAlu

set_option autoImplicit false

namespace Base16ct.Proofs.EncodeStr.Lower.Loop.Compute

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Copied.P256.Proofs.Common.Field (AdvanceTriple)
open Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Update.Byte (mergeGPR8_setWidth)

attribute [local x86_compose] subR32R32Effect gprNumber
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq mergeGPR8_setWidth

@[local x86_local] private theorem subR32R32Effect_local (p : BitVec 64) (len : Nat)
    (dst src : BitVec 5) : Effect.Local (subR32R32Effect p len dst src) := by
  apply Base16ct.Proofs.Copied.P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [subR32R32Effect, h.read_reg]
  · intro s
    simp [subR32R32Effect, Write.Full, Operand.Full]

def highBytes : List UInt8 :=
  [0x45, 0x89, 0xca, 0x41, 0xc1, 0xea, 0x04, 0x41, 0x83, 0xca, 0x30,
   0x41, 0xbb, 0x39, 0x00, 0x00, 0x00, 0x45, 0x29, 0xd3,
   0x41, 0xc1, 0xeb, 0x08, 0x41, 0x80, 0xe3, 0x27, 0x45, 0x00, 0xd3]

def lowBytes : List UInt8 :=
  [0x41, 0x83, 0xe1, 0x0f, 0x41, 0x83, 0xc9, 0x30,
   0x41, 0xba, 0x39, 0x00, 0x00, 0x00, 0x45, 0x29, 0xca,
   0x41, 0xc1, 0xea, 0x08, 0x41, 0x80, 0xe2, 0x27, 0x45, 0x00, 0xca]

def digitWord (value : BitVec 32) : BitVec 64 :=
  let shifted := (57#32 - (value ||| 48#32)) >>> 8
  mergeGPR 8 (lowerDigit value)
    (mergeGPR 8 (shifted.setWidth 8 &&& 39#8) (shifted.setWidth 64))

def highEffect (s : RamState) : Effect :=
  let value := (Operand.reg 9 : Operand 32).read s >>> 4
  { rip := 0x1004f4
    writes := [⟨(Operand.reg 10 : Operand 64), (value ||| 48#32).setWidth 64⟩,
      ⟨(Operand.reg 11 : Operand 64), digitWord value⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

def lowEffect (s : RamState) : Effect :=
  let value := (Operand.reg 9 : Operand 32).read s &&& 15#32
  { rip := 0x100514
    writes := [⟨(Operand.reg 9 : Operand 64), (value ||| 48#32).setWidth 64⟩,
      ⟨(Operand.reg 10 : Operand 64), digitWord value⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem high_code {s : RamState} (hCode : CodeIn Extracted.programImage s) :
    CodeIn (codeRange 0x1004d5 highBytes) s :=
  program_text_slice hCode 0x4d5 31 (by decide +kernel)

theorem low_code {s : RamState} (hCode : CodeIn Extracted.programImage s) :
    CodeIn (codeRange 0x1004f8 lowBytes) s :=
  program_text_slice hCode 0x4f8 28 (by decide +kernel)

theorem highEffect_components (s : RamState) :
    (highEffect s).components = [.reg 10, .reg 11, .flags, .rip] := rfl

theorem lowEffect_components (s : RamState) :
    (lowEffect s).components = [.reg 9, .reg 10, .flags, .rip] := rfl

theorem highEffect_rip (s : RamState) : (highEffect s).rip = 0x1004f4 := rfl

theorem lowEffect_rip (s : RamState) : (lowEffect s).rip = 0x100514 := rfl

theorem highEffect_avoids (s : RamState) (code : CodeMap) :
    (highEffect s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [highEffect, Effect.components, Component.Covers]) code

theorem lowEffect_avoids (s : RamState) (code : CodeMap) :
    (lowEffect s).Avoids code :=
  Effect.Avoids.of_noMem (by simp [lowEffect, Effect.components, Component.Covers]) code

theorem highEffect_read8 {s t : RamState} {b : UInt8}
    (h : (highEffect s).Holds s t)
    (hByte : (Operand.reg 9 : Operand 64).read s = BitVec.ofNat 64 b.toNat) :
    (Operand.reg 11 : Operand 8).read t = lowerHighDigit b := by
  have hw := h.writes.2
  change (Operand.reg 11 : Operand 64).read t = _ at hw
  change ((Operand.reg 11 : Operand 64).read t).setWidth 8 = _
  rw [hw, digitWord, mergeGPR8_setWidth]
  change lowerDigit (((Operand.reg 9 : Operand 64).read s).setWidth 32 >>> 4) = _
  simp only [hByte, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64), lowerHighDigit]

theorem highEffect_read9 {s t : RamState} (h : (highEffect s).Holds s t) :
    (Operand.reg 9 : Operand 64).read t = (Operand.reg 9 : Operand 64).read s :=
  h.agrees.read (by simp [highEffect, Effect.components])

theorem lowEffect_read8 {s t : RamState} {b : UInt8}
    (h : (lowEffect s).Holds s t)
    (hByte : (Operand.reg 9 : Operand 64).read s = BitVec.ofNat 64 b.toNat) :
    (Operand.reg 10 : Operand 8).read t = lowerLowDigit b := by
  have hw := h.writes.2
  change (Operand.reg 10 : Operand 64).read t = _ at hw
  change ((Operand.reg 10 : Operand 64).read t).setWidth 8 = _
  rw [hw, digitWord, mergeGPR8_setWidth]
  change lowerDigit (((Operand.reg 9 : Operand 64).read s).setWidth 32 &&& 15#32) = _
  simp only [hByte, BitVec.setWidth_ofNat_of_le (by decide : 32 ≤ 64), lowerLowDigit]

set_option maxHeartbeats 2000000 in
theorem high_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1004d5)
      (codeRange 0x1004d5 highBytes) (Effect.post highEffect) := by
  have nexte58 := text_address_ne_return outside 0x4d8 (by decide +kernel)
  have nexte5c := text_address_ne_return outside 0x4dc (by decide +kernel)
  have nexte60 := text_address_ne_return outside 0x4e0 (by decide +kernel)
  have nexte66 := text_address_ne_return outside 0x4e6 (by decide +kernel)
  have nexte69 := text_address_ne_return outside 0x4e9 (by decide +kernel)
  have nexte6d := text_address_ne_return outside 0x4ed (by decide +kernel)
  have nexte71 := text_address_ne_return outside 0x4f1 (by decide +kernel)
  have nexte74 := text_address_ne_return outside 0x4f4 (by decide +kernel)
  advance_begin (mov_r32_r32_rex_effect_step 0x1004d5 0x45 0xca (by simp [RexNoWPrefix]) rfl)
  advance_then (shr_r32_imm8_rex_effect_step 0x1004d8 0x41 0xea 4 (by simp [RexNoWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1004d5 highBytes 3 4
  advance_then (or_r32_imm8_rex_effect_step 0x1004dc 0x41 0xca 0x30 (by simp [RexNoWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1004d5 highBytes 7 4
  advance_then (mov_r32_imm32_rex_effect_step 0x1004e0 0x41 0xbb (by simp [RexNoWPrefix]) (by decide +kernel) 57)
  case sub => exact codeRange_slice_subset 0x1004d5 highBytes 11 6
  advance_then (sub_r32_r32_rex_effect_step 0x1004e6 0x45 0xd3 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1004d5 highBytes 17 3
  advance_then (shr_r32_imm8_rex_effect_step 0x1004e9 0x41 0xeb 8 (by simp [RexNoWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1004d5 highBytes 20 4
  advance_then (and_r11b_imm27_effect_step 0x1004ed)
  case sub => exact codeRange_slice_subset 0x1004d5 highBytes 24 4
  advance_then (add_r11b_r10b_effect_step 0x1004f1)
  case sub => exact codeRange_slice_subset 0x1004d5 highBytes 28 3
  advance_finish [highEffect, digitWord, lowerDigit, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 32)]

set_option maxHeartbeats 2000000 in
theorem low_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x1004f8)
      (codeRange 0x1004f8 lowBytes) (Effect.post lowEffect) := by
  have nexte7c := text_address_ne_return outside 0x4fc (by decide +kernel)
  have nexte80 := text_address_ne_return outside 0x500 (by decide +kernel)
  have nexte86 := text_address_ne_return outside 0x506 (by decide +kernel)
  have nexte89 := text_address_ne_return outside 0x509 (by decide +kernel)
  have nexte8d := text_address_ne_return outside 0x50d (by decide +kernel)
  have nexte91 := text_address_ne_return outside 0x511 (by decide +kernel)
  have nexte94 := text_address_ne_return outside 0x514 (by decide +kernel)
  advance_begin (and_r32_imm8_rex_effect_step 0x1004f8 0x41 0xe1 15 (by simp [RexNoWPrefix]) rfl rfl)
  advance_then (or_r32_imm8_rex_effect_step 0x1004fc 0x41 0xc9 0x30 (by simp [RexNoWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1004f8 lowBytes 4 4
  advance_then (mov_r32_imm32_rex_effect_step 0x100500 0x41 0xba (by simp [RexNoWPrefix]) (by decide +kernel) 57)
  case sub => exact codeRange_slice_subset 0x1004f8 lowBytes 8 6
  advance_then (sub_r32_r32_rex_effect_step 0x100506 0x45 0xca (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1004f8 lowBytes 14 3
  advance_then (shr_r32_imm8_rex_effect_step 0x100509 0x41 0xea 8 (by simp [RexNoWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1004f8 lowBytes 17 4
  advance_then (and_r10b_imm27_effect_step 0x10050d)
  case sub => exact codeRange_slice_subset 0x1004f8 lowBytes 21 4
  advance_then (add_r10b_r9b_effect_step 0x100511)
  case sub => exact codeRange_slice_subset 0x1004f8 lowBytes 25 3
  advance_finish [lowEffect, digitWord, lowerDigit, ← BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 32)]

end Base16ct.Proofs.EncodeStr.Lower.Loop.Compute
