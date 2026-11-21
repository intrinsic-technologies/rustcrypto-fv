import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part29 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cb7d 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cb80 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cb83 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10cb85 2 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10cb88 0xc2 0x4d2c6dfc rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb8e 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb91 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb94 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb97 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cb9a 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cb9c 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cb9f 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cba2 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cba4 0xce rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cba6 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cba9 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cbac 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cbaf 0x45 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cbb2 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cbb5 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cbb7 0xc6 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cbba 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cbbd 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cbbf 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cbc2 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cbc5 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cbc8 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cbcb 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cbce 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cbd1 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cbd4 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cbd6 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cbd8 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cbdb 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cbde 0xd6 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10cbe0 5 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cbe4 0xee rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10cbe6 6 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cbea 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cbec 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cbef 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cbf2 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cbf5 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cbf7 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cbfa 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10cbfd 5 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cc01 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc03 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc06 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc09 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc0b 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc0d 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cc10 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cc13 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cc16 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cc19 0x41 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cc1c 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10cc1f 0x42 (by simp [RexNoWPrefix]) 0 (.sib 2 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10cc23 0x53380d13) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc28 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc2b 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc2e 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc31 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc34 0xd6 rfl) (by x86_local)]

def part29Bytes : List UInt8 :=
  [0x44,0x31,0xe2,0x44,0x1,0xfe,0x1,0xd6,0x8d,0x14,0x30,0x81,0xc2,0xfc,0x6d,0x2c,0x4d,0x44,0x89,0xd0,0xc1,0xc0,0x1e,0x44,0x89,0xd6,0xc1,0xc6,0x13,0x31,0xc6,0x44,0x89,0xd0,0xc1,0xc0,0xa,0x31,0xf0,0x89,0xce,0x44,0x21,0xc6,0x41,0x89,0xce,0x45,0x31,0xc6,0x45,0x21,0xd6,0x41,0x31,0xf6,0x89,0xee,0xc1,0xc6,0xf,0x41,0x1,0xc6,0x89,0xe8,0xc1,0xc0,0xd,0x41,0x1,0xd5,0x44,0x89,0xff,0xc1,0xc7,0x19,0x41,0x1,0xd6,0x44,0x89,0xfa,0xc1,0xc2,0xe,0x31,0xf0,0x31,0xfa,0x44,0x89,0xfe,0xc1,0xee,0x3,0x31,0xd6,0x1,0x6c,0x24,0x70,0x1,0xee,0x89,0x74,0x24,0xc,0x89,0xea,0xc1,0xea,0xa,0x44,0x89,0xee,0xc1,0xc6,0x1a,0x31,0xc2,0x44,0x89,0xe8,0xc1,0xc0,0x15,0x8b,0x6c,0x24,0x50,0x1,0xd5,0x44,0x89,0xea,0xc1,0xc2,0x7,0x31,0xf0,0x31,0xc2,0x44,0x89,0xd8,0x44,0x31,0xc8,0x44,0x21,0xe8,0x44,0x31,0xc8,0x41,0x1,0xec,0x41,0x1,0xc4,0x42,0x8d,0x4,0x22,0x5,0x13,0xd,0x38,0x53,0x44,0x89,0xf2,0xc1,0xc2,0x1e,0x44,0x89,0xf6,0xc1,0xc6,0x13,0x31,0xd6]

set_option maxRecDepth 4096 in
theorem part29_bytes [Bindings] : part29.flatMap CheckedInstruction.bytes = part29Bytes  := by
  rfl

def part29Layout : List (BitVec 64 × Nat) :=
  [(0x10cb7d, 3), (0x10cb80, 3), (0x10cb83, 2), (0x10cb85, 3), (0x10cb88, 6), (0x10cb8e, 3), (0x10cb91, 3), (0x10cb94, 3), (0x10cb97, 3), (0x10cb9a, 2), (0x10cb9c, 3), (0x10cb9f, 3), (0x10cba2, 2), (0x10cba4, 2), (0x10cba6, 3), (0x10cba9, 3), (0x10cbac, 3), (0x10cbaf, 3), (0x10cbb2, 3), (0x10cbb5, 2), (0x10cbb7, 3), (0x10cbba, 3), (0x10cbbd, 2), (0x10cbbf, 3), (0x10cbc2, 3), (0x10cbc5, 3), (0x10cbc8, 3), (0x10cbcb, 3), (0x10cbce, 3), (0x10cbd1, 3), (0x10cbd4, 2), (0x10cbd6, 2), (0x10cbd8, 3), (0x10cbdb, 3), (0x10cbde, 2), (0x10cbe0, 4), (0x10cbe4, 2), (0x10cbe6, 4), (0x10cbea, 2), (0x10cbec, 3), (0x10cbef, 3), (0x10cbf2, 3), (0x10cbf5, 2), (0x10cbf7, 3), (0x10cbfa, 3), (0x10cbfd, 4), (0x10cc01, 2), (0x10cc03, 3), (0x10cc06, 3), (0x10cc09, 2), (0x10cc0b, 2), (0x10cc0d, 3), (0x10cc10, 3), (0x10cc13, 3), (0x10cc16, 3), (0x10cc19, 3), (0x10cc1c, 3), (0x10cc1f, 4), (0x10cc23, 5), (0x10cc28, 3), (0x10cc2b, 3), (0x10cc2e, 3), (0x10cc31, 3), (0x10cc34, 2)]

theorem part29_layout [Bindings] : InstructionTrace.layout part29 = part29Layout := by
  rfl

theorem part29_ordered [Bindings] : InstructionTrace.ordered 0x10cb7d part29 = true := by
  rw [InstructionTrace.ordered_eq_layout, part29_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part29_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xcb7d 185 = part29Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
