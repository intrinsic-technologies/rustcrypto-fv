import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part17 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c275 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c278 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c27b 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c27d 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c27f 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c282 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c285 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c288 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c28b 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c28e 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c291 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c294 0xc3 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c296 1 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c29d 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c2a0 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c2a3 0 (.sib 4 none 0 (.d32 172)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c2aa 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c2ad 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c2af 6 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c2b6 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c2b9 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c2bc 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c2bf 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c2c1 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c2c4 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c2c7 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c2c9 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c2cb 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c2ce 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c2d0 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c2d3 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c2d5 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c2d7 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c2da 0xf9 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10c2dc 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c2e4 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c2e7 1 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c2eb 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c2ee 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c2f1 0xc1 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c2f3 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c2f7 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c2f9 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c2fc 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c2fe 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c301 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c303 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c305 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c308 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c30a 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c30c 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c30f 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c311 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c314 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10c317 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c319 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c31c 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c31f 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c322 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10c325 0x4a7484aa) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c32a 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c32d 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c330 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c333 0xc7 0x13 rfl rfl) (by x86_local)]

def part17Bytes : List UInt8 :=
  [0x44,0x89,0xe7,0xc1,0xc7,0xa,0x31,0xd1,0x31,0xcf,0x44,0x89,0xf9,0x44,0x21,0xc9,0x45,0x89,0xfd,0x45,0x31,0xcd,0x45,0x21,0xe5,0x41,0x31,0xcd,0x41,0x1,0xfd,0x1,0xc3,0x8b,0x8c,0x24,0xa8,0x0,0x0,0x0,0xc1,0xc1,0x19,0x41,0x1,0xc5,0x8b,0x84,0x24,0xac,0x0,0x0,0x0,0xc1,0xc0,0xe,0x31,0xc8,0x8b,0xb4,0x24,0xb0,0x0,0x0,0x0,0xc1,0xee,0x3,0x44,0x89,0xc1,0xc1,0xc1,0xf,0x31,0xc6,0x44,0x89,0xc0,0xc1,0xc0,0xd,0x31,0xc8,0x89,0xe9,0xc1,0xc1,0x19,0x89,0xef,0xc1,0xc7,0xe,0x31,0xcf,0x89,0xe9,0xc1,0xe9,0x3,0x31,0xf9,0x44,0x1,0x84,0x24,0x88,0x0,0x0,0x0,0x44,0x1,0xc1,0x89,0x4c,0x24,0x50,0x44,0x89,0xc1,0xc1,0xe9,0xa,0x31,0xc1,0x8b,0x54,0x24,0x40,0x1,0xf2,0x48,0x89,0xde,0x89,0xf0,0xc1,0xc0,0x1a,0x1,0xca,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd1,0x44,0x31,0xf1,0x21,0xf1,0x44,0x31,0xf1,0x41,0x1,0xd3,0x41,0x1,0xcb,0x44,0x1,0xd8,0x5,0xaa,0x84,0x74,0x4a,0x44,0x89,0xe9,0xc1,0xc1,0x1e,0x44,0x89,0xef,0xc1,0xc7,0x13]

set_option maxRecDepth 4096 in
theorem part17_bytes [Bindings] : part17.flatMap CheckedInstruction.bytes = part17Bytes  := by
  rfl

def part17Layout : List (BitVec 64 × Nat) :=
  [(0x10c275, 3), (0x10c278, 3), (0x10c27b, 2), (0x10c27d, 2), (0x10c27f, 3), (0x10c282, 3), (0x10c285, 3), (0x10c288, 3), (0x10c28b, 3), (0x10c28e, 3), (0x10c291, 3), (0x10c294, 2), (0x10c296, 7), (0x10c29d, 3), (0x10c2a0, 3), (0x10c2a3, 7), (0x10c2aa, 3), (0x10c2ad, 2), (0x10c2af, 7), (0x10c2b6, 3), (0x10c2b9, 3), (0x10c2bc, 3), (0x10c2bf, 2), (0x10c2c1, 3), (0x10c2c4, 3), (0x10c2c7, 2), (0x10c2c9, 2), (0x10c2cb, 3), (0x10c2ce, 2), (0x10c2d0, 3), (0x10c2d3, 2), (0x10c2d5, 2), (0x10c2d7, 3), (0x10c2da, 2), (0x10c2dc, 8), (0x10c2e4, 3), (0x10c2e7, 4), (0x10c2eb, 3), (0x10c2ee, 3), (0x10c2f1, 2), (0x10c2f3, 4), (0x10c2f7, 2), (0x10c2f9, 3), (0x10c2fc, 2), (0x10c2fe, 3), (0x10c301, 2), (0x10c303, 2), (0x10c305, 3), (0x10c308, 2), (0x10c30a, 2), (0x10c30c, 3), (0x10c30f, 2), (0x10c311, 3), (0x10c314, 3), (0x10c317, 2), (0x10c319, 3), (0x10c31c, 3), (0x10c31f, 3), (0x10c322, 3), (0x10c325, 5), (0x10c32a, 3), (0x10c32d, 3), (0x10c330, 3), (0x10c333, 3)]

theorem part17_layout [Bindings] : InstructionTrace.layout part17 = part17Layout := by
  rfl

theorem part17_ordered [Bindings] : InstructionTrace.ordered 0x10c275 part17 = true := by
  rw [InstructionTrace.ordered_eq_layout, part17_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part17_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc275 193 = part17Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
