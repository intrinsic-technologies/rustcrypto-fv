import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part17 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a355 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a358 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a35b 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a35d 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a35f 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a362 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a365 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a368 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a36b 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a36e 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a371 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a374 0xc3 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a376 1 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a37d 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a380 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a383 0 (.sib 4 none 0 (.d32 172)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a38a 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a38d 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a38f 6 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a396 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a399 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a39c 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a39f 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a3a1 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a3a4 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a3a7 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a3a9 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a3ab 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a3ae 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a3b0 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a3b3 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a3b5 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a3b7 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a3ba 0xf9 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10a3bc 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a3c4 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a3c7 1 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a3cb 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a3ce 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a3d1 0xc1 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a3d3 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a3d7 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10a3d9 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a3dc 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a3de 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a3e1 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a3e3 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a3e5 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a3e8 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a3ea 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a3ec 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a3ef 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a3f1 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a3f4 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10a3f7 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a3f9 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a3fc 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a3ff 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a402 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10a405 0x4a7484aa) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a40a 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a40d 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a410 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a413 0xc7 0x13 rfl rfl) (by x86_local)]

def part17Bytes : List UInt8 :=
  [0x44,0x89,0xe7,0xc1,0xc7,0xa,0x31,0xd1,0x31,0xcf,0x44,0x89,0xf9,0x44,0x21,0xc9,0x45,0x89,0xfd,0x45,0x31,0xcd,0x45,0x21,0xe5,0x41,0x31,0xcd,0x41,0x1,0xfd,0x1,0xc3,0x8b,0x8c,0x24,0xa8,0x0,0x0,0x0,0xc1,0xc1,0x19,0x41,0x1,0xc5,0x8b,0x84,0x24,0xac,0x0,0x0,0x0,0xc1,0xc0,0xe,0x31,0xc8,0x8b,0xb4,0x24,0xb0,0x0,0x0,0x0,0xc1,0xee,0x3,0x44,0x89,0xc1,0xc1,0xc1,0xf,0x31,0xc6,0x44,0x89,0xc0,0xc1,0xc0,0xd,0x31,0xc8,0x89,0xe9,0xc1,0xc1,0x19,0x89,0xef,0xc1,0xc7,0xe,0x31,0xcf,0x89,0xe9,0xc1,0xe9,0x3,0x31,0xf9,0x44,0x1,0x84,0x24,0x88,0x0,0x0,0x0,0x44,0x1,0xc1,0x89,0x4c,0x24,0x50,0x44,0x89,0xc1,0xc1,0xe9,0xa,0x31,0xc1,0x8b,0x54,0x24,0x40,0x1,0xf2,0x48,0x89,0xde,0x89,0xf0,0xc1,0xc0,0x1a,0x1,0xca,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd1,0x44,0x31,0xf1,0x21,0xf1,0x44,0x31,0xf1,0x41,0x1,0xd3,0x41,0x1,0xcb,0x44,0x1,0xd8,0x5,0xaa,0x84,0x74,0x4a,0x44,0x89,0xe9,0xc1,0xc1,0x1e,0x44,0x89,0xef,0xc1,0xc7,0x13]

set_option maxRecDepth 4096 in
theorem part17_bytes [Bindings] : part17.flatMap CheckedInstruction.bytes = part17Bytes  := by
  rfl

def part17Layout : List (BitVec 64 × Nat) :=
  [(0x10a355, 3), (0x10a358, 3), (0x10a35b, 2), (0x10a35d, 2), (0x10a35f, 3), (0x10a362, 3), (0x10a365, 3), (0x10a368, 3), (0x10a36b, 3), (0x10a36e, 3), (0x10a371, 3), (0x10a374, 2), (0x10a376, 7), (0x10a37d, 3), (0x10a380, 3), (0x10a383, 7), (0x10a38a, 3), (0x10a38d, 2), (0x10a38f, 7), (0x10a396, 3), (0x10a399, 3), (0x10a39c, 3), (0x10a39f, 2), (0x10a3a1, 3), (0x10a3a4, 3), (0x10a3a7, 2), (0x10a3a9, 2), (0x10a3ab, 3), (0x10a3ae, 2), (0x10a3b0, 3), (0x10a3b3, 2), (0x10a3b5, 2), (0x10a3b7, 3), (0x10a3ba, 2), (0x10a3bc, 8), (0x10a3c4, 3), (0x10a3c7, 4), (0x10a3cb, 3), (0x10a3ce, 3), (0x10a3d1, 2), (0x10a3d3, 4), (0x10a3d7, 2), (0x10a3d9, 3), (0x10a3dc, 2), (0x10a3de, 3), (0x10a3e1, 2), (0x10a3e3, 2), (0x10a3e5, 3), (0x10a3e8, 2), (0x10a3ea, 2), (0x10a3ec, 3), (0x10a3ef, 2), (0x10a3f1, 3), (0x10a3f4, 3), (0x10a3f7, 2), (0x10a3f9, 3), (0x10a3fc, 3), (0x10a3ff, 3), (0x10a402, 3), (0x10a405, 5), (0x10a40a, 3), (0x10a40d, 3), (0x10a410, 3), (0x10a413, 3)]

theorem part17_layout [Bindings] : InstructionTrace.layout part17 = part17Layout := by
  rfl

theorem part17_ordered [Bindings] : InstructionTrace.ordered 0x10a355 part17 = true := by
  rw [InstructionTrace.ordered_eq_layout, part17_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part17_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa355 193 = part17Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
