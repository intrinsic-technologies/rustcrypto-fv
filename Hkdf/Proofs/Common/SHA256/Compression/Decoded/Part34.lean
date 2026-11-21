import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part34 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b028 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b02b 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b02e 0x41 0xc0 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b032 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b035 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b038 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b03b 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b03e 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b041 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b044 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b047 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b04a 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b04e 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b051 0xc1 0xa2bfe8a1 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b057 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b05a 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b05e 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b061 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b064 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b068 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b06b 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b06e 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b071 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b073 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b075 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b078 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b07b 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b07e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b080 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b083 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b087 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b089 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b08b 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b08e 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b091 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b094 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b098 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b09b 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b09f 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b0a2 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10b0a5 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b0a9 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b0ac 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b0b0 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10b0b3 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b0b8 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10b0bb 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b0bf 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b0c2 5 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b0c5 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b0c8 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b0ca 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b0cd 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b0d0 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b0d4 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b0d7 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b0d9 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b0dc 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b0df 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b0e2 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b0e5 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b0e8 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b0eb 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b0ee 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part34Bytes : List UInt8 :=
  [0x45,0x31,0xc1,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x7,0x45,0x31,0xc8,0x45,0x89,0xf1,0x45,0x31,0xd1,0x41,0x21,0xf9,0x45,0x31,0xd1,0x44,0x1,0xe1,0x44,0x1,0xc9,0x45,0x89,0xd9,0x41,0xc1,0xc1,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xa1,0xe8,0xbf,0xa2,0x45,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x45,0x31,0xc8,0x45,0x89,0xd9,0x41,0xc1,0xc1,0xa,0x45,0x31,0xc1,0x41,0x89,0xd0,0x41,0x21,0xf0,0x89,0xd3,0x31,0xf3,0x44,0x21,0xdb,0x44,0x31,0xc3,0x44,0x1,0xcb,0x1,0xc8,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xf,0x1,0xcb,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc1,0x45,0x89,0xe0,0x41,0xc1,0xc0,0x19,0x45,0x89,0xe1,0x41,0xc1,0xc1,0xe,0x45,0x31,0xc1,0x45,0x89,0xe0,0x41,0xc1,0xe8,0x3,0x45,0x31,0xc8,0x1,0x6c,0x24,0x4,0x41,0x1,0xe8,0x44,0x89,0x44,0x24,0x70,0x41,0x89,0xe8,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x8b,0x2c,0x24,0x44,0x1,0xc5,0x89,0xc1,0xc1,0xc1,0x1a,0x41,0x89,0xc0,0x41,0xc1,0xc0,0x15,0x41,0x31,0xc8,0x89,0xc1,0xc1,0xc1,0x7,0x44,0x31,0xc1,0x41,0x89,0xf8,0x45,0x31,0xf0,0x41,0x21,0xc0,0x45,0x31,0xf0,0x41,0x1,0xea,0x41,0x89,0xd9]

set_option maxRecDepth 4096 in
theorem part34_bytes [Bindings] : part34.flatMap CheckedInstruction.bytes = part34Bytes  := by
  rfl

def part34Layout : List (BitVec 64 × Nat) :=
  [(0x10b028, 3), (0x10b02b, 3), (0x10b02e, 4), (0x10b032, 3), (0x10b035, 3), (0x10b038, 3), (0x10b03b, 3), (0x10b03e, 3), (0x10b041, 3), (0x10b044, 3), (0x10b047, 3), (0x10b04a, 4), (0x10b04e, 3), (0x10b051, 6), (0x10b057, 3), (0x10b05a, 4), (0x10b05e, 3), (0x10b061, 3), (0x10b064, 4), (0x10b068, 3), (0x10b06b, 3), (0x10b06e, 3), (0x10b071, 2), (0x10b073, 2), (0x10b075, 3), (0x10b078, 3), (0x10b07b, 3), (0x10b07e, 2), (0x10b080, 3), (0x10b083, 4), (0x10b087, 2), (0x10b089, 2), (0x10b08b, 3), (0x10b08e, 3), (0x10b091, 3), (0x10b094, 4), (0x10b098, 3), (0x10b09b, 4), (0x10b09f, 3), (0x10b0a2, 3), (0x10b0a5, 4), (0x10b0a9, 3), (0x10b0ac, 4), (0x10b0b0, 3), (0x10b0b3, 5), (0x10b0b8, 3), (0x10b0bb, 4), (0x10b0bf, 3), (0x10b0c2, 3), (0x10b0c5, 3), (0x10b0c8, 2), (0x10b0ca, 3), (0x10b0cd, 3), (0x10b0d0, 4), (0x10b0d4, 3), (0x10b0d7, 2), (0x10b0d9, 3), (0x10b0dc, 3), (0x10b0df, 3), (0x10b0e2, 3), (0x10b0e5, 3), (0x10b0e8, 3), (0x10b0eb, 3), (0x10b0ee, 3)]

theorem part34_layout [Bindings] : InstructionTrace.layout part34 = part34Layout := by
  rfl

theorem part34_ordered [Bindings] : InstructionTrace.ordered 0x10b028 part34 = true := by
  rw [InstructionTrace.ordered_eq_layout, part34_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part34_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb028 201 = part34Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
