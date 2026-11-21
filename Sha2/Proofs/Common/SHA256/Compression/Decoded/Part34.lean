import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part34 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf48 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf4b 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cf4e 0x41 0xc0 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf52 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf55 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf58 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cf5b 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf5e 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cf61 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cf64 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf67 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cf6a 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cf6e 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10cf71 0xc1 0xa2bfe8a1 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf77 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cf7a 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf7e 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf81 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cf84 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf88 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cf8b 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cf8e 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cf91 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cf93 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cf95 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cf98 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cf9b 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cf9e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cfa0 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cfa3 0x41 0xc0 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cfa7 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cfa9 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cfab 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cfae 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cfb1 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cfb4 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cfb8 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cfbb 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cfbf 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cfc2 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10cfc5 0x41 0xe8 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cfc9 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10cfcc 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cfd0 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10cfd3 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cfd8 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10cfdb 0x41 0xe8 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cfdf 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10cfe2 5 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cfe5 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cfe8 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cfea 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cfed 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10cff0 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cff4 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cff7 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cff9 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cffc 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cfff 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d002 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d005 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d008 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d00b 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d00e 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part34Bytes : List UInt8 :=
  [0x45,0x31,0xc1,0x41,0x89,0xf8,0x41,0xc1,0xc0,0x7,0x45,0x31,0xc8,0x45,0x89,0xf1,0x45,0x31,0xd1,0x41,0x21,0xf9,0x45,0x31,0xd1,0x44,0x1,0xe1,0x44,0x1,0xc9,0x45,0x89,0xd9,0x41,0xc1,0xc1,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xa1,0xe8,0xbf,0xa2,0x45,0x89,0xd8,0x41,0xc1,0xc0,0x13,0x45,0x31,0xc8,0x45,0x89,0xd9,0x41,0xc1,0xc1,0xa,0x45,0x31,0xc1,0x41,0x89,0xd0,0x41,0x21,0xf0,0x89,0xd3,0x31,0xf3,0x44,0x21,0xdb,0x44,0x31,0xc3,0x44,0x1,0xcb,0x1,0xc8,0x41,0x89,0xe8,0x41,0xc1,0xc0,0xf,0x1,0xcb,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc1,0x45,0x89,0xe0,0x41,0xc1,0xc0,0x19,0x45,0x89,0xe1,0x41,0xc1,0xc1,0xe,0x45,0x31,0xc1,0x45,0x89,0xe0,0x41,0xc1,0xe8,0x3,0x45,0x31,0xc8,0x1,0x6c,0x24,0x4,0x41,0x1,0xe8,0x44,0x89,0x44,0x24,0x70,0x41,0x89,0xe8,0x41,0xc1,0xe8,0xa,0x41,0x31,0xc8,0x8b,0x2c,0x24,0x44,0x1,0xc5,0x89,0xc1,0xc1,0xc1,0x1a,0x41,0x89,0xc0,0x41,0xc1,0xc0,0x15,0x41,0x31,0xc8,0x89,0xc1,0xc1,0xc1,0x7,0x44,0x31,0xc1,0x41,0x89,0xf8,0x45,0x31,0xf0,0x41,0x21,0xc0,0x45,0x31,0xf0,0x41,0x1,0xea,0x41,0x89,0xd9]

set_option maxRecDepth 4096 in
theorem part34_bytes [Bindings] : part34.flatMap CheckedInstruction.bytes = part34Bytes  := by
  rfl

def part34Layout : List (BitVec 64 × Nat) :=
  [(0x10cf48, 3), (0x10cf4b, 3), (0x10cf4e, 4), (0x10cf52, 3), (0x10cf55, 3), (0x10cf58, 3), (0x10cf5b, 3), (0x10cf5e, 3), (0x10cf61, 3), (0x10cf64, 3), (0x10cf67, 3), (0x10cf6a, 4), (0x10cf6e, 3), (0x10cf71, 6), (0x10cf77, 3), (0x10cf7a, 4), (0x10cf7e, 3), (0x10cf81, 3), (0x10cf84, 4), (0x10cf88, 3), (0x10cf8b, 3), (0x10cf8e, 3), (0x10cf91, 2), (0x10cf93, 2), (0x10cf95, 3), (0x10cf98, 3), (0x10cf9b, 3), (0x10cf9e, 2), (0x10cfa0, 3), (0x10cfa3, 4), (0x10cfa7, 2), (0x10cfa9, 2), (0x10cfab, 3), (0x10cfae, 3), (0x10cfb1, 3), (0x10cfb4, 4), (0x10cfb8, 3), (0x10cfbb, 4), (0x10cfbf, 3), (0x10cfc2, 3), (0x10cfc5, 4), (0x10cfc9, 3), (0x10cfcc, 4), (0x10cfd0, 3), (0x10cfd3, 5), (0x10cfd8, 3), (0x10cfdb, 4), (0x10cfdf, 3), (0x10cfe2, 3), (0x10cfe5, 3), (0x10cfe8, 2), (0x10cfea, 3), (0x10cfed, 3), (0x10cff0, 4), (0x10cff4, 3), (0x10cff7, 2), (0x10cff9, 3), (0x10cffc, 3), (0x10cfff, 3), (0x10d002, 3), (0x10d005, 3), (0x10d008, 3), (0x10d00b, 3), (0x10d00e, 3)]

theorem part34_layout [Bindings] : InstructionTrace.layout part34 = part34Layout := by
  rfl

theorem part34_ordered [Bindings] : InstructionTrace.ordered 0x10cf48 part34 = true := by
  rw [InstructionTrace.ordered_eq_layout, part34_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part34_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xcf48 201 = part34Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
