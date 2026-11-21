import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part13 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ff8 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ffb 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109ffe 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a000 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a003 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a006 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a008 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a00d 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a010 0xc6 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a013 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a016 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a019 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a01b 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a01e 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a021 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a023 0xf7 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a025 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a029 6 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a030 6 (.sib 4 none 0 (.d32 172)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a037 6 (.sib 4 none 0 (.d32 176)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a03e 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a041 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a045 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a048 7 (.sib 4 none 0 (.d32 140)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a04f 0x41 0xed 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a053 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a056 1 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a05a 1 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a061 1 (.sib 4 none 0 (.d32 148)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a068 1 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a06f 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a072 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a075 1 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a079 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10a07c 0x44 (by simp [RexNoWPrefix]) 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a081 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a084 0xc6 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10a086 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a08b 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a08e 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a091 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a094 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a096 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a099 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a09c 0xc6 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a09e 6 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a0a2 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a0a5 0xd0 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a0a7 2 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a0aa 0xd3 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10a0ac 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a0b1 0xd0 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a0b3 0 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a0b7 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a0ba 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a0bd 0 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a0c1 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a0c6 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a0c8 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a0ca 2 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a0ce 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a0d1 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10a0d4 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a0d9 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part13Bytes : List UInt8 :=
  [0x44,0x89,0xee,0xc1,0xc6,0x19,0x31,0xf8,0x44,0x89,0xe9,0xc1,0xc1,0xe,0x31,0xf1,0x4c,0x8b,0x44,0x24,0x50,0x44,0x89,0xc6,0xc1,0xc6,0x19,0x44,0x89,0xc7,0xc1,0xc7,0xe,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xee,0x3,0x31,0xfe,0x89,0xf7,0x8b,0x74,0x24,0x28,0x89,0xb4,0x24,0xa8,0x0,0x0,0x0,0x89,0xb4,0x24,0xac,0x0,0x0,0x0,0x89,0xb4,0x24,0xb0,0x0,0x0,0x0,0x44,0x1,0xee,0x89,0x74,0x24,0x28,0x44,0x1,0xef,0x89,0xbc,0x24,0x8c,0x0,0x0,0x0,0x41,0xc1,0xed,0x3,0x41,0x31,0xcd,0x8b,0x4c,0x24,0x40,0x89,0x8c,0x24,0x90,0x0,0x0,0x0,0x89,0x8c,0x24,0x94,0x0,0x0,0x0,0x89,0x8c,0x24,0x98,0x0,0x0,0x0,0x44,0x89,0xd6,0x44,0x1,0xd1,0x89,0x4c,0x24,0x40,0x45,0x1,0xd5,0x44,0x89,0x6c,0x24,0x4,0xc1,0xee,0x3,0x31,0xc6,0x44,0x8b,0x4c,0x24,0x24,0x44,0x89,0xc9,0x45,0x89,0xcc,0x45,0x89,0xca,0x89,0xe8,0x41,0x1,0xe9,0x44,0x89,0xcd,0x1,0xc6,0x89,0x74,0x24,0x24,0xc1,0xe8,0x3,0x31,0xd0,0x8b,0x14,0x24,0x1,0xd3,0x48,0x89,0x5c,0x24,0x48,0x1,0xd0,0x89,0x44,0x24,0x10,0xc1,0xea,0x3,0x44,0x31,0xf2,0x8b,0x44,0x24,0x34,0x48,0x8b,0x5c,0x24,0x68,0x1,0xc3,0x1,0xc2,0x89,0x54,0x24,0x64,0xc1,0xe8,0x3,0x44,0x31,0xd8,0x44,0x8b,0x5c,0x24,0xc,0x44,0x1,0xd8]

set_option maxRecDepth 4096 in
theorem part13_bytes [Bindings] : part13.flatMap CheckedInstruction.bytes = part13Bytes  := by
  rfl

def part13Layout : List (BitVec 64 × Nat) :=
  [(0x109ff8, 3), (0x109ffb, 3), (0x109ffe, 2), (0x10a000, 3), (0x10a003, 3), (0x10a006, 2), (0x10a008, 5), (0x10a00d, 3), (0x10a010, 3), (0x10a013, 3), (0x10a016, 3), (0x10a019, 2), (0x10a01b, 3), (0x10a01e, 3), (0x10a021, 2), (0x10a023, 2), (0x10a025, 4), (0x10a029, 7), (0x10a030, 7), (0x10a037, 7), (0x10a03e, 3), (0x10a041, 4), (0x10a045, 3), (0x10a048, 7), (0x10a04f, 4), (0x10a053, 3), (0x10a056, 4), (0x10a05a, 7), (0x10a061, 7), (0x10a068, 7), (0x10a06f, 3), (0x10a072, 3), (0x10a075, 4), (0x10a079, 3), (0x10a07c, 5), (0x10a081, 3), (0x10a084, 2), (0x10a086, 5), (0x10a08b, 3), (0x10a08e, 3), (0x10a091, 3), (0x10a094, 2), (0x10a096, 3), (0x10a099, 3), (0x10a09c, 2), (0x10a09e, 4), (0x10a0a2, 3), (0x10a0a5, 2), (0x10a0a7, 3), (0x10a0aa, 2), (0x10a0ac, 5), (0x10a0b1, 2), (0x10a0b3, 4), (0x10a0b7, 3), (0x10a0ba, 3), (0x10a0bd, 4), (0x10a0c1, 5), (0x10a0c6, 2), (0x10a0c8, 2), (0x10a0ca, 4), (0x10a0ce, 3), (0x10a0d1, 3), (0x10a0d4, 5), (0x10a0d9, 3)]

theorem part13_layout [Bindings] : InstructionTrace.layout part13 = part13Layout := by
  rfl

theorem part13_ordered [Bindings] : InstructionTrace.ordered 0x109ff8 part13 = true := by
  rw [InstructionTrace.ordered_eq_layout, part13_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part13_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9ff8 228 = part13Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
