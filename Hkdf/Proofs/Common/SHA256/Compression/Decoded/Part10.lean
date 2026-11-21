import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part10 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d91 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109d94 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d96 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109d99 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d9c 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109d9f 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109da2 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109da5 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109da8 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109dab 0xcb rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109dad 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109db2 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109db5 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109db8 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109dbb 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109dbe 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109dc1 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109dc3 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x109dc6 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109dc9 0xce rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109dcb 5 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109dcf 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109dd1 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109dd4 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109dd6 0xc7 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109dd9 0xcf rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x109ddb 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109dde 0xfd rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109de0 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x109de5 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109dea 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109ded 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109df0 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109df2 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109df5 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109df7 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109dfa 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109dfc 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109dfe 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e01 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e03 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e06 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109e08 0xde rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109e0a 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e12 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109e14 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e17 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109e1a 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109e1d 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e1f 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109e22 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109e25 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x109e27 0xe49b69c1) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e2c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x109e2f 0x4c 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109e32 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e35 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e37 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e39 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109e3c 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109e41 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e44 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109e47 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109e4a 0xef rfl) (by x86_local)]

def part10Bytes : List UInt8 :=
  [0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xf7,0x44,0x21,0xcf,0x45,0x89,0xf0,0x45,0x31,0xc8,0x45,0x21,0xd8,0x41,0x31,0xf8,0x41,0x1,0xf0,0x1,0xcb,0x4c,0x8b,0x64,0x24,0x38,0x44,0x89,0xe6,0xc1,0xc6,0x19,0x41,0x1,0xc8,0x44,0x89,0xe1,0xc1,0xc1,0xe,0x31,0xf1,0x44,0x89,0xe6,0xc1,0xee,0x3,0x31,0xce,0x89,0x6c,0x24,0x64,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xef,0xc1,0xc7,0xd,0x31,0xcf,0xc1,0xed,0xa,0x31,0xfd,0x4c,0x8b,0x54,0x24,0x50,0x44,0x3,0x54,0x24,0x8,0x41,0x1,0xf2,0x41,0x1,0xea,0x89,0xd9,0xc1,0xc1,0x1a,0x89,0xde,0xc1,0xc6,0x15,0x31,0xce,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf1,0x44,0x89,0xfe,0x31,0xd6,0x21,0xde,0x48,0x89,0x9c,0x24,0x80,0x0,0x0,0x0,0x31,0xd6,0x44,0x1,0xd0,0x44,0x89,0xc7,0xc1,0xc7,0x1e,0x1,0xf0,0x44,0x89,0xc6,0xc1,0xc6,0x13,0x1,0xc8,0x5,0xc1,0x69,0x9b,0xe4,0x44,0x89,0xc1,0x4c,0x89,0xc5,0xc1,0xc1,0xa,0x31,0xfe,0x31,0xf1,0x44,0x89,0xde,0x4c,0x89,0x74,0x24,0x58,0x44,0x21,0xf6,0x44,0x89,0xdf,0x44,0x31,0xf7,0x21,0xef]

set_option maxRecDepth 4096 in
theorem part10_bytes [Bindings] : part10.flatMap CheckedInstruction.bytes = part10Bytes  := by
  rfl

def part10Layout : List (BitVec 64 × Nat) :=
  [(0x109d91, 3), (0x109d94, 2), (0x109d96, 3), (0x109d99, 3), (0x109d9c, 3), (0x109d9f, 3), (0x109da2, 3), (0x109da5, 3), (0x109da8, 3), (0x109dab, 2), (0x109dad, 5), (0x109db2, 3), (0x109db5, 3), (0x109db8, 3), (0x109dbb, 3), (0x109dbe, 3), (0x109dc1, 2), (0x109dc3, 3), (0x109dc6, 3), (0x109dc9, 2), (0x109dcb, 4), (0x109dcf, 2), (0x109dd1, 3), (0x109dd4, 2), (0x109dd6, 3), (0x109dd9, 2), (0x109ddb, 3), (0x109dde, 2), (0x109de0, 5), (0x109de5, 5), (0x109dea, 3), (0x109ded, 3), (0x109df0, 2), (0x109df2, 3), (0x109df5, 2), (0x109df7, 3), (0x109dfa, 2), (0x109dfc, 2), (0x109dfe, 3), (0x109e01, 2), (0x109e03, 3), (0x109e06, 2), (0x109e08, 2), (0x109e0a, 8), (0x109e12, 2), (0x109e14, 3), (0x109e17, 3), (0x109e1a, 3), (0x109e1d, 2), (0x109e1f, 3), (0x109e22, 3), (0x109e25, 2), (0x109e27, 5), (0x109e2c, 3), (0x109e2f, 3), (0x109e32, 3), (0x109e35, 2), (0x109e37, 2), (0x109e39, 3), (0x109e3c, 5), (0x109e41, 3), (0x109e44, 3), (0x109e47, 3), (0x109e4a, 2)]

theorem part10_layout [Bindings] : InstructionTrace.layout part10 = part10Layout := by
  rfl

theorem part10_ordered [Bindings] : InstructionTrace.ordered 0x109d91 part10 = true := by
  rw [InstructionTrace.ordered_eq_layout, part10_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part10_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9d91 187 = part10Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
