import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part48 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d999 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d99b 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d99e 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d9a1 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d9a4 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d9a8 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d9ab 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d9ae 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d9b1 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d9b3 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d9b6 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d9b9 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10d9bc 0x43 (by simp [RexNoWPrefix]) 7 (.sib 11 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10d9c0 0xc7 0x84c87814 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d9c6 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d9c9 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d9cd 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d9d0 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d9d4 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d9d7 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d9d9 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d9dc 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d9df 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d9e2 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d9e5 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d9e8 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d9eb 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d9ee 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d9f1 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d9f4 0xfe rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d9f6 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d9f9 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d9fc 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d9ff 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da02 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10da05 0x41 0xc3 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da09 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10da0c 0xeb 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da0f 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10da12 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10da14 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da17 0x45 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10da1a 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da1d 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10da20 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da24 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10da27 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10da29 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da2c 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da2f 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da32 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10da35 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da38 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10da3b 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10da3e 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10da41 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10da44 0xc7 0x8cc70208 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da4a 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10da4d 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da51 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10da54 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10da58 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10da5b 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10da5e 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part48Bytes : List UInt8 :=
  [0x89,0xc7,0xc1,0xc7,0x15,0x44,0x31,0xdf,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x7,0x41,0x31,0xfb,0x44,0x89,0xef,0x44,0x31,0xcf,0x21,0xc7,0x44,0x31,0xcf,0x41,0x1,0xea,0x41,0x1,0xfa,0x43,0x8d,0x3c,0x13,0x81,0xc7,0x14,0x78,0xc8,0x84,0x41,0x89,0xd2,0x41,0xc1,0xc2,0x1e,0x41,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xd3,0x89,0xd3,0xc1,0xc3,0xa,0x44,0x31,0xdb,0x41,0x89,0xcb,0x45,0x21,0xc3,0x41,0x89,0xca,0x45,0x31,0xc2,0x41,0x21,0xd2,0x45,0x31,0xda,0x41,0x1,0xda,0x1,0xfe,0x41,0x1,0xfa,0x44,0x89,0xf3,0x44,0x89,0xf7,0xc1,0xc7,0xf,0x45,0x89,0xf3,0x41,0xc1,0xc3,0xd,0x41,0x31,0xfb,0xc1,0xeb,0xa,0x44,0x31,0xdb,0x89,0xf7,0xc1,0xc7,0x1a,0x45,0x89,0xe7,0x41,0x1,0xdf,0x41,0x89,0xf3,0x41,0xc1,0xc3,0x15,0x41,0x31,0xfb,0x89,0xf7,0xc1,0xc7,0x7,0x44,0x31,0xdf,0x41,0x89,0xc3,0x45,0x31,0xeb,0x41,0x21,0xf3,0x45,0x31,0xeb,0x45,0x1,0xf9,0x45,0x1,0xd9,0x44,0x1,0xcf,0x81,0xc7,0x8,0x2,0xc7,0x8c,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x1e,0x45,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x45,0x89,0xd1,0x41,0xc1,0xc1,0xa]

set_option maxRecDepth 4096 in
theorem part48_bytes [Bindings] : part48.flatMap CheckedInstruction.bytes = part48Bytes  := by
  rfl

def part48Layout : List (BitVec 64 × Nat) :=
  [(0x10d999, 2), (0x10d99b, 3), (0x10d99e, 3), (0x10d9a1, 3), (0x10d9a4, 4), (0x10d9a8, 3), (0x10d9ab, 3), (0x10d9ae, 3), (0x10d9b1, 2), (0x10d9b3, 3), (0x10d9b6, 3), (0x10d9b9, 3), (0x10d9bc, 4), (0x10d9c0, 6), (0x10d9c6, 3), (0x10d9c9, 4), (0x10d9cd, 3), (0x10d9d0, 4), (0x10d9d4, 3), (0x10d9d7, 2), (0x10d9d9, 3), (0x10d9dc, 3), (0x10d9df, 3), (0x10d9e2, 3), (0x10d9e5, 3), (0x10d9e8, 3), (0x10d9eb, 3), (0x10d9ee, 3), (0x10d9f1, 3), (0x10d9f4, 2), (0x10d9f6, 3), (0x10d9f9, 3), (0x10d9fc, 3), (0x10d9ff, 3), (0x10da02, 3), (0x10da05, 4), (0x10da09, 3), (0x10da0c, 3), (0x10da0f, 3), (0x10da12, 2), (0x10da14, 3), (0x10da17, 3), (0x10da1a, 3), (0x10da1d, 3), (0x10da20, 4), (0x10da24, 3), (0x10da27, 2), (0x10da29, 3), (0x10da2c, 3), (0x10da2f, 3), (0x10da32, 3), (0x10da35, 3), (0x10da38, 3), (0x10da3b, 3), (0x10da3e, 3), (0x10da41, 3), (0x10da44, 6), (0x10da4a, 3), (0x10da4d, 4), (0x10da51, 3), (0x10da54, 4), (0x10da58, 3), (0x10da5b, 3), (0x10da5e, 4)]

theorem part48_layout [Bindings] : InstructionTrace.layout part48 = part48Layout := by
  rfl

theorem part48_ordered [Bindings] : InstructionTrace.ordered 0x10d999 part48 = true := by
  rw [InstructionTrace.ordered_eq_layout, part48_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part48_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd999 201 = part48Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
