import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part39 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d321 0xc7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10d323 1 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d327 0xcf rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10d329 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d32c 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d32e 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d331 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d333 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d336 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d339 1 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d33d 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d33f 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d342 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d345 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d347 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d34a 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d34d 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d34f 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d351 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d354 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d357 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d35a 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d35c 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10d35e 0 (.sib 6 (some 2) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10d361 0xf40e3585) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d366 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d369 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d36c 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d36f 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d372 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d374 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d377 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d37b 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d37e 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d381 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d384 0x45 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d387 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d38a 0x45 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d38d 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d390 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d392 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d395 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d398 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d39a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10d39d 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d3a2 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d3a4 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d3a7 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d3ab 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d3ae 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d3b0 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d3b3 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d3b5 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d3b8 0xca rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d3ba 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d3bd 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10d3bf 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d3c4 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10d3c7 2 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d3cb 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d3ce 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10d3d1 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d3d4 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d3d6 0xc7 0x1a rfl rfl) (by x86_local)]

def part39Bytes : List UInt8 :=
  [0x31,0xc7,0x1,0x4c,0x24,0x50,0x1,0xcf,0x89,0x3c,0x24,0x89,0xc8,0xc1,0xe8,0xa,0x31,0xf0,0x44,0x89,0xfe,0xc1,0xc6,0x1a,0x8b,0x4c,0x24,0x4,0x1,0xc1,0x44,0x89,0xf8,0xc1,0xc0,0x15,0x31,0xf0,0x44,0x89,0xfe,0xc1,0xc6,0x7,0x31,0xc6,0x89,0xd8,0x44,0x31,0xd8,0x44,0x21,0xf8,0x44,0x31,0xd8,0x1,0xca,0x1,0xc2,0x8d,0x4,0x16,0x5,0x85,0x35,0xe,0xf4,0x44,0x89,0xe2,0xc1,0xc2,0x1e,0x44,0x89,0xe6,0xc1,0xc6,0x13,0x31,0xd6,0x45,0x89,0xe0,0x41,0xc1,0xc0,0xa,0x41,0x31,0xf0,0x44,0x89,0xee,0x44,0x21,0xce,0x45,0x89,0xee,0x45,0x31,0xce,0x45,0x21,0xe6,0x41,0x31,0xf6,0x89,0xef,0xc1,0xc7,0xf,0x45,0x1,0xc6,0x89,0xee,0xc1,0xc6,0xd,0x48,0x8b,0x6c,0x24,0x38,0x1,0xc5,0x41,0x89,0xc8,0x41,0xc1,0xc0,0x19,0x41,0x1,0xc6,0x89,0xc8,0xc1,0xc0,0xe,0x31,0xfe,0x44,0x31,0xc0,0x89,0xca,0xc1,0xea,0x3,0x31,0xc2,0x44,0x1,0x54,0x24,0x78,0x44,0x1,0xd2,0x89,0x54,0x24,0x4,0x44,0x89,0xd0,0xc1,0xe8,0xa,0x48,0x89,0xea,0x89,0xef,0xc1,0xc7,0x1a]

set_option maxRecDepth 4096 in
theorem part39_bytes [Bindings] : part39.flatMap CheckedInstruction.bytes = part39Bytes  := by
  rfl

def part39Layout : List (BitVec 64 × Nat) :=
  [(0x10d321, 2), (0x10d323, 4), (0x10d327, 2), (0x10d329, 3), (0x10d32c, 2), (0x10d32e, 3), (0x10d331, 2), (0x10d333, 3), (0x10d336, 3), (0x10d339, 4), (0x10d33d, 2), (0x10d33f, 3), (0x10d342, 3), (0x10d345, 2), (0x10d347, 3), (0x10d34a, 3), (0x10d34d, 2), (0x10d34f, 2), (0x10d351, 3), (0x10d354, 3), (0x10d357, 3), (0x10d35a, 2), (0x10d35c, 2), (0x10d35e, 3), (0x10d361, 5), (0x10d366, 3), (0x10d369, 3), (0x10d36c, 3), (0x10d36f, 3), (0x10d372, 2), (0x10d374, 3), (0x10d377, 4), (0x10d37b, 3), (0x10d37e, 3), (0x10d381, 3), (0x10d384, 3), (0x10d387, 3), (0x10d38a, 3), (0x10d38d, 3), (0x10d390, 2), (0x10d392, 3), (0x10d395, 3), (0x10d398, 2), (0x10d39a, 3), (0x10d39d, 5), (0x10d3a2, 2), (0x10d3a4, 3), (0x10d3a7, 4), (0x10d3ab, 3), (0x10d3ae, 2), (0x10d3b0, 3), (0x10d3b3, 2), (0x10d3b5, 3), (0x10d3b8, 2), (0x10d3ba, 3), (0x10d3bd, 2), (0x10d3bf, 5), (0x10d3c4, 3), (0x10d3c7, 4), (0x10d3cb, 3), (0x10d3ce, 3), (0x10d3d1, 3), (0x10d3d4, 2), (0x10d3d6, 3)]

theorem part39_layout [Bindings] : InstructionTrace.layout part39 = part39Layout := by
  rfl

theorem part39_ordered [Bindings] : InstructionTrace.ordered 0x10d321 part39 = true := by
  rw [InstructionTrace.ordered_eq_layout, part39_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part39_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd321 184 = part39Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
