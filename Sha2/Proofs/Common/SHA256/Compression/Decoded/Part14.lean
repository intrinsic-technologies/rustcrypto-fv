import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part14 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (store32_legacy_effect_step 0x10bffc 0 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c003 0x41 0xeb 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_effect_step 0x10c007 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d32 156)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c00f 0 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c013 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10c016 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c01a 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_legacy_effect_step 0x10c01d 0 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c024 2 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c028 0xd0 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c02a 0 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c02e 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c030 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_legacy_effect_step 0x10c033 0 (.sib 4 none 0 (.d32 164)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c03a 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c03d 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c042 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c044 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c047 0xfe rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c049 0xc6 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c04c 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c04e 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c050 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c053 0xf0 rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10c055 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c05a 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10c05d 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c062 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c065 0 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c069 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c06c 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_legacy_effect_step 0x10c06f 2 (.sib 4 none 0 (.d32 180)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c076 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c07b 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c07e 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c081 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10c084 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c08c 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c08f 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c092 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c095 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c098 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c09b 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c09d 0xc2 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c09f 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 224)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c0a7 0xd8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c0a9 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c0b1 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c0b3 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c0b6 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c0b8 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c0bb 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10c0be 0x42 (by simp [RexNoWPrefix]) 0 (.sib 2 (some 15) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10c0c2 0xfc19dc6) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c0c7 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c0cf 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c0d2 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c0d5 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c0d8 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c0db 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c0dd 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c0e0 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c0e3 0xf2 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c0e5 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part14Bytes : List UInt8 :=
  [0x89,0x84,0x24,0x88,0x0,0x0,0x0,0x41,0xc1,0xeb,0x3,0x44,0x33,0x9c,0x24,0x9c,0x0,0x0,0x0,0x8b,0x44,0x24,0x8,0x41,0x1,0xc3,0x44,0x89,0x1c,0x24,0xc1,0xe8,0x3,0x33,0x84,0x24,0xa0,0x0,0x0,0x0,0x8b,0x54,0x24,0x60,0x1,0xd0,0x89,0x44,0x24,0x34,0x89,0xd0,0xc1,0xe8,0x3,0x33,0x84,0x24,0xa4,0x0,0x0,0x0,0x41,0x89,0xc1,0x48,0x8b,0x7c,0x24,0x38,0x89,0xfa,0xc1,0xc2,0x19,0x89,0xfe,0xc1,0xc6,0xe,0x31,0xd6,0x89,0xf8,0xc1,0xe8,0x3,0x31,0xf0,0x44,0x3,0x4c,0x24,0x14,0x45,0x1,0xc1,0x44,0x89,0x4c,0x24,0x60,0x44,0x1,0xc0,0x89,0x44,0x24,0xc,0x44,0x89,0xc2,0xc1,0xea,0xa,0x33,0x94,0x24,0xb4,0x0,0x0,0x0,0x4c,0x8b,0x5c,0x24,0x58,0x44,0x89,0xde,0xc1,0xc6,0x1a,0x49,0x89,0xd8,0x44,0x3,0x84,0x24,0xb8,0x0,0x0,0x0,0x44,0x89,0xd8,0xc1,0xc0,0x15,0x41,0x1,0xd0,0x44,0x89,0xda,0xc1,0xc2,0x7,0x31,0xf0,0x31,0xc2,0x48,0x8b,0x9c,0x24,0xe0,0x0,0x0,0x0,0x89,0xd8,0x48,0x8b,0xb4,0x24,0x80,0x0,0x0,0x0,0x31,0xf0,0x44,0x21,0xd8,0x31,0xf0,0x45,0x1,0xc7,0x41,0x1,0xc7,0x42,0x8d,0x4,0x3a,0x5,0xc6,0x9d,0xc1,0xf,0x4c,0x8b,0x8c,0x24,0xd0,0x0,0x0,0x0,0x44,0x89,0xca,0xc1,0xc2,0x1e,0x44,0x89,0xce,0xc1,0xc6,0x13,0x31,0xd6,0x44,0x89,0xca,0xc1,0xc2,0xa,0x31,0xf2,0x48,0x8b,0x74,0x24,0x70]

set_option maxRecDepth 4096 in
theorem part14_bytes [Bindings] : part14.flatMap CheckedInstruction.bytes = part14Bytes  := by
  rfl

def part14Layout : List (BitVec 64 × Nat) :=
  [(0x10bffc, 7), (0x10c003, 4), (0x10c007, 8), (0x10c00f, 4), (0x10c013, 3), (0x10c016, 4), (0x10c01a, 3), (0x10c01d, 7), (0x10c024, 4), (0x10c028, 2), (0x10c02a, 4), (0x10c02e, 2), (0x10c030, 3), (0x10c033, 7), (0x10c03a, 3), (0x10c03d, 5), (0x10c042, 2), (0x10c044, 3), (0x10c047, 2), (0x10c049, 3), (0x10c04c, 2), (0x10c04e, 2), (0x10c050, 3), (0x10c053, 2), (0x10c055, 5), (0x10c05a, 3), (0x10c05d, 5), (0x10c062, 3), (0x10c065, 4), (0x10c069, 3), (0x10c06c, 3), (0x10c06f, 7), (0x10c076, 5), (0x10c07b, 3), (0x10c07e, 3), (0x10c081, 3), (0x10c084, 8), (0x10c08c, 3), (0x10c08f, 3), (0x10c092, 3), (0x10c095, 3), (0x10c098, 3), (0x10c09b, 2), (0x10c09d, 2), (0x10c09f, 8), (0x10c0a7, 2), (0x10c0a9, 8), (0x10c0b1, 2), (0x10c0b3, 3), (0x10c0b6, 2), (0x10c0b8, 3), (0x10c0bb, 3), (0x10c0be, 4), (0x10c0c2, 5), (0x10c0c7, 8), (0x10c0cf, 3), (0x10c0d2, 3), (0x10c0d5, 3), (0x10c0d8, 3), (0x10c0db, 2), (0x10c0dd, 3), (0x10c0e0, 3), (0x10c0e3, 2), (0x10c0e5, 5)]

theorem part14_layout [Bindings] : InstructionTrace.layout part14 = part14Layout := by
  rfl

theorem part14_ordered [Bindings] : InstructionTrace.ordered 0x10bffc part14 = true := by
  rw [InstructionTrace.ordered_eq_layout, part14_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part14_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xbffc 238 = part14Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
