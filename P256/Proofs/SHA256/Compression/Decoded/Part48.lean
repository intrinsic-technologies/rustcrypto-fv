import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part48 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117e49 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117e4b 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e4e 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e51 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117e54 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e58 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e5b 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e5e 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117e61 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e63 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117e66 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117e69 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x117e6c 0x43 (by simp [RexNoWPrefix]) 7 (.sib 11 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117e70 0xc7 0x84c87814 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e76 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117e79 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e7d 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117e80 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e84 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117e87 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117e89 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e8c 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e8f 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117e92 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117e95 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e98 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117e9b 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117e9e 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117ea1 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117ea4 0xfe rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117ea6 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117ea9 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117eac 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117eaf 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117eb2 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117eb5 0x41 0xc3 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117eb9 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117ebc 0xeb 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117ebf 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117ec2 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ec4 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117ec7 0x45 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117eca 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117ecd 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117ed0 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117ed4 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117ed7 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ed9 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117edc 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117edf 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117ee2 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117ee5 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117ee8 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117eeb 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117eee 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117ef1 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117ef4 0xc7 0x8cc70208 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117efa 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117efd 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f01 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117f04 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117f08 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117f0b 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117f0e 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part48Bytes : List UInt8 :=
  [0x89,0xc7,0xc1,0xc7,0x15,0x44,0x31,0xdf,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x7,0x41,0x31,0xfb,0x44,0x89,0xef,0x44,0x31,0xcf,0x21,0xc7,0x44,0x31,0xcf,0x41,0x1,0xea,0x41,0x1,0xfa,0x43,0x8d,0x3c,0x13,0x81,0xc7,0x14,0x78,0xc8,0x84,0x41,0x89,0xd2,0x41,0xc1,0xc2,0x1e,0x41,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xd3,0x89,0xd3,0xc1,0xc3,0xa,0x44,0x31,0xdb,0x41,0x89,0xcb,0x45,0x21,0xc3,0x41,0x89,0xca,0x45,0x31,0xc2,0x41,0x21,0xd2,0x45,0x31,0xda,0x41,0x1,0xda,0x1,0xfe,0x41,0x1,0xfa,0x44,0x89,0xf3,0x44,0x89,0xf7,0xc1,0xc7,0xf,0x45,0x89,0xf3,0x41,0xc1,0xc3,0xd,0x41,0x31,0xfb,0xc1,0xeb,0xa,0x44,0x31,0xdb,0x89,0xf7,0xc1,0xc7,0x1a,0x45,0x89,0xe7,0x41,0x1,0xdf,0x41,0x89,0xf3,0x41,0xc1,0xc3,0x15,0x41,0x31,0xfb,0x89,0xf7,0xc1,0xc7,0x7,0x44,0x31,0xdf,0x41,0x89,0xc3,0x45,0x31,0xeb,0x41,0x21,0xf3,0x45,0x31,0xeb,0x45,0x1,0xf9,0x45,0x1,0xd9,0x44,0x1,0xcf,0x81,0xc7,0x8,0x2,0xc7,0x8c,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x1e,0x45,0x89,0xd3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x45,0x89,0xd1,0x41,0xc1,0xc1,0xa]

set_option maxRecDepth 4096 in
theorem part48_bytes [Bindings] : part48.flatMap CheckedInstruction.bytes = part48Bytes  := by
  rfl

def part48Layout : List (BitVec 64 × Nat) :=
  [(0x117e49, 2), (0x117e4b, 3), (0x117e4e, 3), (0x117e51, 3), (0x117e54, 4), (0x117e58, 3), (0x117e5b, 3), (0x117e5e, 3), (0x117e61, 2), (0x117e63, 3), (0x117e66, 3), (0x117e69, 3), (0x117e6c, 4), (0x117e70, 6), (0x117e76, 3), (0x117e79, 4), (0x117e7d, 3), (0x117e80, 4), (0x117e84, 3), (0x117e87, 2), (0x117e89, 3), (0x117e8c, 3), (0x117e8f, 3), (0x117e92, 3), (0x117e95, 3), (0x117e98, 3), (0x117e9b, 3), (0x117e9e, 3), (0x117ea1, 3), (0x117ea4, 2), (0x117ea6, 3), (0x117ea9, 3), (0x117eac, 3), (0x117eaf, 3), (0x117eb2, 3), (0x117eb5, 4), (0x117eb9, 3), (0x117ebc, 3), (0x117ebf, 3), (0x117ec2, 2), (0x117ec4, 3), (0x117ec7, 3), (0x117eca, 3), (0x117ecd, 3), (0x117ed0, 4), (0x117ed4, 3), (0x117ed7, 2), (0x117ed9, 3), (0x117edc, 3), (0x117edf, 3), (0x117ee2, 3), (0x117ee5, 3), (0x117ee8, 3), (0x117eeb, 3), (0x117eee, 3), (0x117ef1, 3), (0x117ef4, 6), (0x117efa, 3), (0x117efd, 4), (0x117f01, 3), (0x117f04, 4), (0x117f08, 3), (0x117f0b, 3), (0x117f0e, 4)]

theorem part48_layout [Bindings] : InstructionTrace.layout part48 = part48Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part48_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17e49 201 = part48Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
