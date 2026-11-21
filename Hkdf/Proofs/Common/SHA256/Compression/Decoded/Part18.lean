import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part18 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a416 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a418 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a41b 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a41e 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a420 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a423 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a426 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a429 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a42c 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a42f 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a432 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a434 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a437 0xc7 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10a439 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a43e 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a441 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a444 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a447 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a44a 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a44c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a44f 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a452 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a455 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a459 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a45b 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a45d 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a460 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a463 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a466 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a46a 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a46c 0xc3 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a46f 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a472 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a475 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a479 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a47c 5 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a480 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10a483 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a488 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a48b 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a48f 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a492 5 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a496 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a498 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a49b 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a49e 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a4a1 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a4a4 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a4a7 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a4a9 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a4ac 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a4af 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a4b1 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a4b3 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a4b6 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a4b9 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a4bc 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a4bf 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10a4c2 0x42 (by simp [RexNoWPrefix]) 1 (.sib 0 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10a4c6 0xc1 0x5cb0a9dc rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a4cc 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a4ce 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a4d1 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a4d4 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part18Bytes : List UInt8 :=
  [0x31,0xcf,0x44,0x89,0xe9,0xc1,0xc1,0xa,0x31,0xf9,0x45,0x89,0xe0,0x45,0x21,0xf8,0x44,0x89,0xe7,0x44,0x31,0xff,0x44,0x21,0xef,0x44,0x31,0xc7,0x1,0xcf,0x41,0x1,0xc1,0x1,0xc7,0x44,0x8b,0x44,0x24,0x14,0x44,0x89,0xc0,0xc1,0xc0,0x19,0x44,0x89,0xc1,0xc1,0xc1,0xe,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xe8,0x3,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xf,0x31,0xc8,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc1,0x41,0x89,0xd0,0x41,0xc1,0xc0,0x19,0x89,0xd3,0xc1,0xc3,0xe,0x44,0x31,0xc3,0x41,0x89,0xd0,0x41,0xc1,0xe8,0x3,0x41,0x31,0xd8,0x1,0x6c,0x24,0x64,0x41,0x1,0xe8,0x44,0x89,0x44,0x24,0x78,0x41,0x89,0xe8,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x8b,0x6c,0x24,0x28,0x1,0xc5,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x44,0x1,0xc5,0x44,0x89,0xc9,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xc8,0x89,0xf1,0x44,0x31,0xd1,0x44,0x21,0xc9,0x44,0x31,0xd1,0x41,0x1,0xee,0x41,0x1,0xce,0x42,0x8d,0xc,0x30,0x81,0xc1,0xdc,0xa9,0xb0,0x5c,0x89,0xf8,0xc1,0xc0,0x1e,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x13]

set_option maxRecDepth 4096 in
theorem part18_bytes [Bindings] : part18.flatMap CheckedInstruction.bytes = part18Bytes  := by
  rfl

def part18Layout : List (BitVec 64 × Nat) :=
  [(0x10a416, 2), (0x10a418, 3), (0x10a41b, 3), (0x10a41e, 2), (0x10a420, 3), (0x10a423, 3), (0x10a426, 3), (0x10a429, 3), (0x10a42c, 3), (0x10a42f, 3), (0x10a432, 2), (0x10a434, 3), (0x10a437, 2), (0x10a439, 5), (0x10a43e, 3), (0x10a441, 3), (0x10a444, 3), (0x10a447, 3), (0x10a44a, 2), (0x10a44c, 3), (0x10a44f, 3), (0x10a452, 3), (0x10a455, 4), (0x10a459, 2), (0x10a45b, 2), (0x10a45d, 3), (0x10a460, 3), (0x10a463, 3), (0x10a466, 4), (0x10a46a, 2), (0x10a46c, 3), (0x10a46f, 3), (0x10a472, 3), (0x10a475, 4), (0x10a479, 3), (0x10a47c, 4), (0x10a480, 3), (0x10a483, 5), (0x10a488, 3), (0x10a48b, 4), (0x10a48f, 3), (0x10a492, 4), (0x10a496, 2), (0x10a498, 3), (0x10a49b, 3), (0x10a49e, 3), (0x10a4a1, 3), (0x10a4a4, 3), (0x10a4a7, 2), (0x10a4a9, 3), (0x10a4ac, 3), (0x10a4af, 2), (0x10a4b1, 2), (0x10a4b3, 3), (0x10a4b6, 3), (0x10a4b9, 3), (0x10a4bc, 3), (0x10a4bf, 3), (0x10a4c2, 4), (0x10a4c6, 6), (0x10a4cc, 2), (0x10a4ce, 3), (0x10a4d1, 3), (0x10a4d4, 4)]

theorem part18_layout [Bindings] : InstructionTrace.layout part18 = part18Layout := by
  rfl

theorem part18_ordered [Bindings] : InstructionTrace.ordered 0x10a416 part18 = true := by
  rw [InstructionTrace.ordered_eq_layout, part18_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part18_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa416 194 = part18Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
