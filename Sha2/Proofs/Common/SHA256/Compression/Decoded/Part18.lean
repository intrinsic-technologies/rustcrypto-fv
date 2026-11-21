import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part18 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c336 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c338 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c33b 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c33e 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c340 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c343 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c346 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c349 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c34c 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c34f 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c352 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c354 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c357 0xc7 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10c359 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c35e 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c361 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c364 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c367 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c36a 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c36c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c36f 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c372 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c375 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c379 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c37b 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c37d 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c380 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c383 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c386 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c38a 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c38c 0xc3 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c38f 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c392 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c395 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c399 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c39c 5 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c3a0 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10c3a3 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c3a8 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c3ab 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c3af 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c3b2 5 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c3b6 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c3b8 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c3bb 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c3be 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c3c1 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c3c4 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c3c7 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c3c9 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c3cc 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c3cf 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c3d1 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c3d3 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c3d6 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c3d9 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c3dc 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c3df 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10c3e2 0x42 (by simp [RexNoWPrefix]) 1 (.sib 0 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10c3e6 0xc1 0x5cb0a9dc rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c3ec 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c3ee 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c3f1 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c3f4 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part18Bytes : List UInt8 :=
  [0x31,0xcf,0x44,0x89,0xe9,0xc1,0xc1,0xa,0x31,0xf9,0x45,0x89,0xe0,0x45,0x21,0xf8,0x44,0x89,0xe7,0x44,0x31,0xff,0x44,0x21,0xef,0x44,0x31,0xc7,0x1,0xcf,0x41,0x1,0xc1,0x1,0xc7,0x44,0x8b,0x44,0x24,0x14,0x44,0x89,0xc0,0xc1,0xc0,0x19,0x44,0x89,0xc1,0xc1,0xc1,0xe,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xe8,0x3,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xf,0x31,0xc8,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc1,0x41,0x89,0xd0,0x41,0xc1,0xc0,0x19,0x89,0xd3,0xc1,0xc3,0xe,0x44,0x31,0xc3,0x41,0x89,0xd0,0x41,0xc1,0xe8,0x3,0x41,0x31,0xd8,0x1,0x6c,0x24,0x64,0x41,0x1,0xe8,0x44,0x89,0x44,0x24,0x78,0x41,0x89,0xe8,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x8b,0x6c,0x24,0x28,0x1,0xc5,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x44,0x1,0xc5,0x44,0x89,0xc9,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xc8,0x89,0xf1,0x44,0x31,0xd1,0x44,0x21,0xc9,0x44,0x31,0xd1,0x41,0x1,0xee,0x41,0x1,0xce,0x42,0x8d,0xc,0x30,0x81,0xc1,0xdc,0xa9,0xb0,0x5c,0x89,0xf8,0xc1,0xc0,0x1e,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x13]

set_option maxRecDepth 4096 in
theorem part18_bytes [Bindings] : part18.flatMap CheckedInstruction.bytes = part18Bytes  := by
  rfl

def part18Layout : List (BitVec 64 × Nat) :=
  [(0x10c336, 2), (0x10c338, 3), (0x10c33b, 3), (0x10c33e, 2), (0x10c340, 3), (0x10c343, 3), (0x10c346, 3), (0x10c349, 3), (0x10c34c, 3), (0x10c34f, 3), (0x10c352, 2), (0x10c354, 3), (0x10c357, 2), (0x10c359, 5), (0x10c35e, 3), (0x10c361, 3), (0x10c364, 3), (0x10c367, 3), (0x10c36a, 2), (0x10c36c, 3), (0x10c36f, 3), (0x10c372, 3), (0x10c375, 4), (0x10c379, 2), (0x10c37b, 2), (0x10c37d, 3), (0x10c380, 3), (0x10c383, 3), (0x10c386, 4), (0x10c38a, 2), (0x10c38c, 3), (0x10c38f, 3), (0x10c392, 3), (0x10c395, 4), (0x10c399, 3), (0x10c39c, 4), (0x10c3a0, 3), (0x10c3a3, 5), (0x10c3a8, 3), (0x10c3ab, 4), (0x10c3af, 3), (0x10c3b2, 4), (0x10c3b6, 2), (0x10c3b8, 3), (0x10c3bb, 3), (0x10c3be, 3), (0x10c3c1, 3), (0x10c3c4, 3), (0x10c3c7, 2), (0x10c3c9, 3), (0x10c3cc, 3), (0x10c3cf, 2), (0x10c3d1, 2), (0x10c3d3, 3), (0x10c3d6, 3), (0x10c3d9, 3), (0x10c3dc, 3), (0x10c3df, 3), (0x10c3e2, 4), (0x10c3e6, 6), (0x10c3ec, 2), (0x10c3ee, 3), (0x10c3f1, 3), (0x10c3f4, 4)]

theorem part18_layout [Bindings] : InstructionTrace.layout part18 = part18Layout := by
  rfl

theorem part18_ordered [Bindings] : InstructionTrace.ordered 0x10c336 part18 = true := by
  rw [InstructionTrace.ordered_eq_layout, part18_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part18_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc336 194 = part18Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
