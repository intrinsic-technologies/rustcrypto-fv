import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part35 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d011 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d015 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d018 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d01b 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d01f 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10d022 0x41 0xc2 0xa81a664b (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d029 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d02b 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d02e 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d031 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d034 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d037 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d03a 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d03d 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d040 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d043 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d046 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d049 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d04c 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d050 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d053 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d056 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d059 0x45 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d05c 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d05f 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d062 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d066 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d069 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d06c 0x41 0xc0 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d070 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d073 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10d076 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d07a 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10d07d 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d082 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10d085 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d08a 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10d08d 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d091 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d094 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d096 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d099 5 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d0a0 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d0a3 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d0a6 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d0aa 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d0ad 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d0af 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d0b2 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d0b5 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d0b8 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d0bb 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d0be 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d0c1 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d0c4 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d0c7 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10d0ca 0xc1 0xc24b8b70 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d0d0 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d0d3 0x41 0xc0 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d0d7 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d0da 0x41 0xc1 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d0de 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d0e1 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d0e4 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part35Bytes : List UInt8 :=
  [0x41,0xc1,0xc1,0x1e,0x45,0x1,0xc2,0x41,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x41,0x1,0xca,0x41,0x81,0xc2,0x4b,0x66,0x1a,0xa8,0x89,0xd9,0xc1,0xc1,0xa,0x45,0x31,0xc8,0x44,0x31,0xc1,0x45,0x89,0xd8,0x41,0x21,0xd0,0x45,0x89,0xdf,0x41,0x31,0xd7,0x41,0x21,0xdf,0x45,0x31,0xc7,0x41,0x1,0xcf,0x45,0x89,0xe0,0x41,0xc1,0xc0,0xf,0x44,0x1,0xd6,0x44,0x89,0xe1,0xc1,0xc1,0xd,0x45,0x1,0xd7,0x41,0x89,0xea,0x41,0x89,0xe9,0x41,0xc1,0xc1,0x19,0x44,0x31,0xc1,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xe,0x45,0x31,0xc8,0x41,0x89,0xe9,0x41,0xc1,0xe9,0x3,0x45,0x31,0xc1,0x44,0x1,0x64,0x24,0x40,0x45,0x1,0xe1,0x44,0x89,0x4c,0x24,0x68,0x45,0x89,0xe0,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x1a,0x8b,0xac,0x24,0x80,0x0,0x0,0x0,0x44,0x1,0xc5,0x41,0x89,0xf0,0x41,0xc1,0xc0,0x15,0x41,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x7,0x44,0x31,0xc1,0x41,0x89,0xc0,0x41,0x31,0xf8,0x41,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xee,0x45,0x1,0xc6,0x44,0x1,0xf1,0x81,0xc1,0x70,0x8b,0x4b,0xc2,0x45,0x89,0xf8,0x41,0xc1,0xc0,0x1e,0x45,0x89,0xf9,0x41,0xc1,0xc1,0x13,0x45,0x31,0xc1,0x45,0x89,0xf8,0x41,0xc1,0xc0,0xa]

set_option maxRecDepth 4096 in
theorem part35_bytes [Bindings] : part35.flatMap CheckedInstruction.bytes = part35Bytes  := by
  rfl

def part35Layout : List (BitVec 64 × Nat) :=
  [(0x10d011, 4), (0x10d015, 3), (0x10d018, 3), (0x10d01b, 4), (0x10d01f, 3), (0x10d022, 7), (0x10d029, 2), (0x10d02b, 3), (0x10d02e, 3), (0x10d031, 3), (0x10d034, 3), (0x10d037, 3), (0x10d03a, 3), (0x10d03d, 3), (0x10d040, 3), (0x10d043, 3), (0x10d046, 3), (0x10d049, 3), (0x10d04c, 4), (0x10d050, 3), (0x10d053, 3), (0x10d056, 3), (0x10d059, 3), (0x10d05c, 3), (0x10d05f, 3), (0x10d062, 4), (0x10d066, 3), (0x10d069, 3), (0x10d06c, 4), (0x10d070, 3), (0x10d073, 3), (0x10d076, 4), (0x10d07a, 3), (0x10d07d, 5), (0x10d082, 3), (0x10d085, 5), (0x10d08a, 3), (0x10d08d, 4), (0x10d091, 3), (0x10d094, 2), (0x10d096, 3), (0x10d099, 7), (0x10d0a0, 3), (0x10d0a3, 3), (0x10d0a6, 4), (0x10d0aa, 3), (0x10d0ad, 2), (0x10d0af, 3), (0x10d0b2, 3), (0x10d0b5, 3), (0x10d0b8, 3), (0x10d0bb, 3), (0x10d0be, 3), (0x10d0c1, 3), (0x10d0c4, 3), (0x10d0c7, 3), (0x10d0ca, 6), (0x10d0d0, 3), (0x10d0d3, 4), (0x10d0d7, 3), (0x10d0da, 4), (0x10d0de, 3), (0x10d0e1, 3), (0x10d0e4, 4)]

theorem part35_layout [Bindings] : InstructionTrace.layout part35 = part35Layout := by
  rfl

theorem part35_ordered [Bindings] : InstructionTrace.ordered 0x10d011 part35 = true := by
  rw [InstructionTrace.ordered_eq_layout, part35_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part35_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd011 215 = part35Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
