import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part48 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ba79 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ba7b 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ba7e 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba81 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10ba84 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ba88 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba8b 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ba8e 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ba91 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ba93 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ba96 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ba99 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10ba9c 0x43 (by simp [RexNoWPrefix]) 7 (.sib 11 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10baa0 0xc7 0x84c87814 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10baa6 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10baa9 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10baad 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bab0 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bab4 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bab7 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bab9 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10babc 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10babf 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bac2 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bac5 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bac8 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bacb 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bace 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bad1 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bad4 0xfe rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bad6 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bad9 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10badc 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10badf 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bae2 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bae5 0x41 0xc3 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bae9 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10baec 0xeb 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10baef 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10baf2 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10baf4 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10baf7 0x45 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bafa 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bafd 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bb00 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb04 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb07 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb09 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb0c 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb0f 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb12 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bb15 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb18 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb1b 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb1e 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb21 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bb24 0xc7 0x8cc70208 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb2a 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bb2d 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb31 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bb34 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bb38 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb3b 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10bb3e 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part48Bytes : List UInt8 :=
  [0x89,0xc7,0xc1,0xc7,0x15,0x44,0x31,0xdf,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x7,0x41,0x31,0xfb,0x44,0x89,0xef,0x44,0x31,0xcf,0x21,0xc7,0x44,0x31,0xcf,0x41,0x1,0xea,0x41,0x1,0xfa,0x43,0x8d,0x3c,0x13,0x81,0xc7,0x14,0x78,0xc8,0x84,0x41,0x89,0xd2,0x41,0xc1,0xc2,0x1e,0x41,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xd3,0x89,0xd3,0xc1,0xc3,0xa,0x44,0x31,0xdb,0x41,0x89,0xcb,0x45,0x21,0xc3,0x41,0x89,0xca,0x45,0x31,0xc2,0x41,0x21,0xd2,0x45,0x31,0xda,0x41,0x1,0xda,0x1,0xfe,0x41,0x1,0xfa,0x44,0x89,0xf3,0x44,0x89,0xf7,0xc1,0xc7,0xf,0x45,0x89,0xf3,0x41,0xc1,0xc3,0xd,0x41,0x31,0xfb,0xc1,0xeb,0xa,0x44,0x31,0xdb,0x89,0xf7,0xc1,0xc7,0x1a,0x45,0x89,0xe7,0x41,0x1,0xdf,0x41,0x89,0xf3,0x41,0xc1,0xc3,0x15,0x41,0x31,0xfb,0x89,0xf7,0xc1,0xc7,0x7,0x44,0x31,0xdf,0x41,0x89,0xc3,0x45,0x31,0xeb,0x41,0x21,0xf3,0x45,0x31,0xeb,0x45,0x1,0xf9,0x45,0x1,0xd9,0x44,0x1,0xcf,0x81,0xc7,0x8,0x2,0xc7,0x8c,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x1e,0x45,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x45,0x89,0xd1,0x41,0xc1,0xc1,0xa]

set_option maxRecDepth 4096 in
theorem part48_bytes [Bindings] : part48.flatMap CheckedInstruction.bytes = part48Bytes  := by
  rfl

def part48Layout : List (BitVec 64 × Nat) :=
  [(0x10ba79, 2), (0x10ba7b, 3), (0x10ba7e, 3), (0x10ba81, 3), (0x10ba84, 4), (0x10ba88, 3), (0x10ba8b, 3), (0x10ba8e, 3), (0x10ba91, 2), (0x10ba93, 3), (0x10ba96, 3), (0x10ba99, 3), (0x10ba9c, 4), (0x10baa0, 6), (0x10baa6, 3), (0x10baa9, 4), (0x10baad, 3), (0x10bab0, 4), (0x10bab4, 3), (0x10bab7, 2), (0x10bab9, 3), (0x10babc, 3), (0x10babf, 3), (0x10bac2, 3), (0x10bac5, 3), (0x10bac8, 3), (0x10bacb, 3), (0x10bace, 3), (0x10bad1, 3), (0x10bad4, 2), (0x10bad6, 3), (0x10bad9, 3), (0x10badc, 3), (0x10badf, 3), (0x10bae2, 3), (0x10bae5, 4), (0x10bae9, 3), (0x10baec, 3), (0x10baef, 3), (0x10baf2, 2), (0x10baf4, 3), (0x10baf7, 3), (0x10bafa, 3), (0x10bafd, 3), (0x10bb00, 4), (0x10bb04, 3), (0x10bb07, 2), (0x10bb09, 3), (0x10bb0c, 3), (0x10bb0f, 3), (0x10bb12, 3), (0x10bb15, 3), (0x10bb18, 3), (0x10bb1b, 3), (0x10bb1e, 3), (0x10bb21, 3), (0x10bb24, 6), (0x10bb2a, 3), (0x10bb2d, 4), (0x10bb31, 3), (0x10bb34, 4), (0x10bb38, 3), (0x10bb3b, 3), (0x10bb3e, 4)]

theorem part48_layout [Bindings] : InstructionTrace.layout part48 = part48Layout := by
  rfl

theorem part48_ordered [Bindings] : InstructionTrace.ordered 0x10ba79 part48 = true := by
  rw [InstructionTrace.ordered_eq_layout, part48_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part48_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xba79 201 = part48Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
