import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part35 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b0f1 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b0f5 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b0f8 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b0fb 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b0ff 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10b102 0x41 0xc2 0xa81a664b (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b109 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b10b 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b10e 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b111 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b114 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b117 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b11a 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b11d 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b120 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b123 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b126 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b129 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b12c 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b130 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b133 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b136 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b139 0x45 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b13c 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b13f 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b142 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b146 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b149 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b14c 0x41 0xc0 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b150 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b153 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10b156 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b15a 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10b15d 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b162 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10b165 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b16a 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10b16d 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b171 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b174 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b176 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b179 5 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b180 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b183 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b186 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b18a 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b18d 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b18f 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b192 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b195 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b198 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b19b 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b19e 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b1a1 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b1a4 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b1a7 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b1aa 0xc1 0xc24b8b70 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b1b0 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b1b3 0x41 0xc0 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b1b7 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b1ba 0x41 0xc1 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b1be 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b1c1 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b1c4 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part35Bytes : List UInt8 :=
  [0x41,0xc1,0xc1,0x1e,0x45,0x1,0xc2,0x41,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x41,0x1,0xca,0x41,0x81,0xc2,0x4b,0x66,0x1a,0xa8,0x89,0xd9,0xc1,0xc1,0xa,0x45,0x31,0xc8,0x44,0x31,0xc1,0x45,0x89,0xd8,0x41,0x21,0xd0,0x45,0x89,0xdf,0x41,0x31,0xd7,0x41,0x21,0xdf,0x45,0x31,0xc7,0x41,0x1,0xcf,0x45,0x89,0xe0,0x41,0xc1,0xc0,0xf,0x44,0x1,0xd6,0x44,0x89,0xe1,0xc1,0xc1,0xd,0x45,0x1,0xd7,0x41,0x89,0xea,0x41,0x89,0xe9,0x41,0xc1,0xc1,0x19,0x44,0x31,0xc1,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xe,0x45,0x31,0xc8,0x41,0x89,0xe9,0x41,0xc1,0xe9,0x3,0x45,0x31,0xc1,0x44,0x1,0x64,0x24,0x40,0x45,0x1,0xe1,0x44,0x89,0x4c,0x24,0x68,0x45,0x89,0xe0,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x1a,0x8b,0xac,0x24,0x80,0x0,0x0,0x0,0x44,0x1,0xc5,0x41,0x89,0xf0,0x41,0xc1,0xc0,0x15,0x41,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x7,0x44,0x31,0xc1,0x41,0x89,0xc0,0x41,0x31,0xf8,0x41,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xee,0x45,0x1,0xc6,0x44,0x1,0xf1,0x81,0xc1,0x70,0x8b,0x4b,0xc2,0x45,0x89,0xf8,0x41,0xc1,0xc0,0x1e,0x45,0x89,0xf9,0x41,0xc1,0xc1,0x13,0x45,0x31,0xc1,0x45,0x89,0xf8,0x41,0xc1,0xc0,0xa]

set_option maxRecDepth 4096 in
theorem part35_bytes [Bindings] : part35.flatMap CheckedInstruction.bytes = part35Bytes  := by
  rfl

def part35Layout : List (BitVec 64 × Nat) :=
  [(0x10b0f1, 4), (0x10b0f5, 3), (0x10b0f8, 3), (0x10b0fb, 4), (0x10b0ff, 3), (0x10b102, 7), (0x10b109, 2), (0x10b10b, 3), (0x10b10e, 3), (0x10b111, 3), (0x10b114, 3), (0x10b117, 3), (0x10b11a, 3), (0x10b11d, 3), (0x10b120, 3), (0x10b123, 3), (0x10b126, 3), (0x10b129, 3), (0x10b12c, 4), (0x10b130, 3), (0x10b133, 3), (0x10b136, 3), (0x10b139, 3), (0x10b13c, 3), (0x10b13f, 3), (0x10b142, 4), (0x10b146, 3), (0x10b149, 3), (0x10b14c, 4), (0x10b150, 3), (0x10b153, 3), (0x10b156, 4), (0x10b15a, 3), (0x10b15d, 5), (0x10b162, 3), (0x10b165, 5), (0x10b16a, 3), (0x10b16d, 4), (0x10b171, 3), (0x10b174, 2), (0x10b176, 3), (0x10b179, 7), (0x10b180, 3), (0x10b183, 3), (0x10b186, 4), (0x10b18a, 3), (0x10b18d, 2), (0x10b18f, 3), (0x10b192, 3), (0x10b195, 3), (0x10b198, 3), (0x10b19b, 3), (0x10b19e, 3), (0x10b1a1, 3), (0x10b1a4, 3), (0x10b1a7, 3), (0x10b1aa, 6), (0x10b1b0, 3), (0x10b1b3, 4), (0x10b1b7, 3), (0x10b1ba, 4), (0x10b1be, 3), (0x10b1c1, 3), (0x10b1c4, 4)]

theorem part35_layout [Bindings] : InstructionTrace.layout part35 = part35Layout := by
  rfl

theorem part35_ordered [Bindings] : InstructionTrace.ordered 0x10b0f1 part35 = true := by
  rw [InstructionTrace.ordered_eq_layout, part35_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part35_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb0f1 215 = part35Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
