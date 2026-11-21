import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part12 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109f14 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109f17 0x41 0xc3 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x109f1b 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109f20 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109f23 0x45 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109f26 0x41 0xc4 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109f2a 0xcd rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109f2c 1 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109f30 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109f33 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109f37 0xf5 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109f39 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109f3c 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109f3f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109f44 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109f46 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109f4b 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109f4f 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109f51 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109f54 0xd5 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109f56 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109f5e 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109f60 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109f63 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109f65 0xc7 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109f67 2 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109f6b 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109f6e 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109f72 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109f75 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x109f77 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109f7a 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x109f7d 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109f82 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109f85 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109f88 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x109f8b 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d32 184)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109f93 0x41 0xc3 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r32_m32_effect_step 0x109f97 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x109f9c 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d32 180)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109fa4 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109fa7 0xfe rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109fa9 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109fac 0x45 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x109faf 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d32 164)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109fb7 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x109fba 0x41 0xc6 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109fbe 0xcd rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109fc0 5 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109fc7 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109fcb 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109fcd 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109fd0 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x109fd3 2 (.sib 4 none 0 (.d32 156)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109fda 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109fdc 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109fdf 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x109fe2 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109fe7 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109fea 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109fed 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ff0 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ff3 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109ff6 0xca rfl) (by x86_local)]

def part12Bytes : List UInt8 :=
  [0x45,0x89,0xd3,0x41,0xc1,0xc3,0xf,0x44,0x89,0x5c,0x24,0x4,0x44,0x21,0xcd,0x45,0x89,0xd4,0x41,0xc1,0xc4,0xd,0x31,0xcd,0x8b,0x4c,0x24,0x60,0x41,0x89,0xca,0x41,0xc1,0xc2,0x19,0x1,0xf5,0xc1,0xc1,0xe,0x41,0x89,0xce,0x48,0x8b,0x4c,0x24,0x58,0x1,0xd1,0x48,0x89,0x4c,0x24,0x58,0x8b,0x74,0x24,0x8,0x89,0xf1,0xc1,0xc1,0x19,0x1,0xd5,0x48,0x89,0xac,0x24,0xd0,0x0,0x0,0x0,0x89,0xf2,0xc1,0xc2,0xe,0x89,0xd5,0x31,0xc7,0x8b,0x54,0x24,0xc,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x19,0xc1,0xc2,0xe,0x89,0xd8,0xc1,0xe8,0x3,0x41,0x89,0xc0,0x44,0x8b,0x5c,0x24,0x34,0x44,0x89,0xd8,0xc1,0xc0,0x19,0x41,0x31,0xf8,0x44,0x89,0x84,0x24,0xb8,0x0,0x0,0x0,0x41,0xc1,0xc3,0xe,0x44,0x33,0x64,0x24,0x4,0x44,0x89,0xa4,0x24,0xb4,0x0,0x0,0x0,0x8b,0x3c,0x24,0x89,0xfe,0xc1,0xc6,0x19,0x45,0x31,0xd6,0x44,0x89,0xb4,0x24,0xa4,0x0,0x0,0x0,0x41,0x89,0xfe,0x41,0xc1,0xc6,0xe,0x31,0xcd,0x89,0xac,0x24,0xa0,0x0,0x0,0x0,0x8b,0x6c,0x24,0x10,0x89,0xe9,0xc1,0xc1,0x19,0x44,0x31,0xca,0x89,0x94,0x24,0x9c,0x0,0x0,0x0,0x89,0xea,0xc1,0xc2,0xe,0x41,0x31,0xc3,0x44,0x8b,0x54,0x24,0x64,0x44,0x89,0xd7,0xc1,0xc7,0x19,0x41,0x31,0xf6,0x44,0x89,0xd0,0xc1,0xc0,0xe,0x31,0xca]

set_option maxRecDepth 4096 in
theorem part12_bytes [Bindings] : part12.flatMap CheckedInstruction.bytes = part12Bytes  := by
  rfl

def part12Layout : List (BitVec 64 × Nat) :=
  [(0x109f14, 3), (0x109f17, 4), (0x109f1b, 5), (0x109f20, 3), (0x109f23, 3), (0x109f26, 4), (0x109f2a, 2), (0x109f2c, 4), (0x109f30, 3), (0x109f33, 4), (0x109f37, 2), (0x109f39, 3), (0x109f3c, 3), (0x109f3f, 5), (0x109f44, 2), (0x109f46, 5), (0x109f4b, 4), (0x109f4f, 2), (0x109f51, 3), (0x109f54, 2), (0x109f56, 8), (0x109f5e, 2), (0x109f60, 3), (0x109f63, 2), (0x109f65, 2), (0x109f67, 4), (0x109f6b, 3), (0x109f6e, 4), (0x109f72, 3), (0x109f75, 2), (0x109f77, 3), (0x109f7a, 3), (0x109f7d, 5), (0x109f82, 3), (0x109f85, 3), (0x109f88, 3), (0x109f8b, 8), (0x109f93, 4), (0x109f97, 5), (0x109f9c, 8), (0x109fa4, 3), (0x109fa7, 2), (0x109fa9, 3), (0x109fac, 3), (0x109faf, 8), (0x109fb7, 3), (0x109fba, 4), (0x109fbe, 2), (0x109fc0, 7), (0x109fc7, 4), (0x109fcb, 2), (0x109fcd, 3), (0x109fd0, 3), (0x109fd3, 7), (0x109fda, 2), (0x109fdc, 3), (0x109fdf, 3), (0x109fe2, 5), (0x109fe7, 3), (0x109fea, 3), (0x109fed, 3), (0x109ff0, 3), (0x109ff3, 3), (0x109ff6, 2)]

theorem part12_layout [Bindings] : InstructionTrace.layout part12 = part12Layout := by
  rfl

theorem part12_ordered [Bindings] : InstructionTrace.ordered 0x109f14 part12 = true := by
  rw [InstructionTrace.ordered_eq_layout, part12_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part12_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9f14 228 = part12Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
