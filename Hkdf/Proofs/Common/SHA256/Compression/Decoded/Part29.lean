import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part29 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ac5d 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ac60 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ac63 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10ac65 2 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10ac68 0xc2 0x4d2c6dfc rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac6e 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac71 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac74 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac77 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ac7a 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac7c 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac7f 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ac82 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ac84 0xce rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ac86 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac89 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ac8c 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ac8f 0x45 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ac92 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ac95 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac97 0xc6 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ac9a 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ac9d 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac9f 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aca2 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aca5 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aca8 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10acab 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10acae 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10acb1 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10acb4 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10acb6 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10acb8 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10acbb 0xee 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10acbe 0xd6 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10acc0 5 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10acc4 0xee rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10acc6 6 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10acca 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10accc 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10accf 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10acd2 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10acd5 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10acd7 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10acda 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10acdd 5 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ace1 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ace3 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ace6 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ace9 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aceb 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aced 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10acf0 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10acf3 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10acf6 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10acf9 0x41 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10acfc 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10acff 0x42 (by simp [RexNoWPrefix]) 0 (.sib 2 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10ad03 0x53380d13) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad08 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad0b 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad0e 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad11 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad14 0xd6 rfl) (by x86_local)]

def part29Bytes : List UInt8 :=
  [0x44,0x31,0xe2,0x44,0x1,0xfe,0x1,0xd6,0x8d,0x14,0x30,0x81,0xc2,0xfc,0x6d,0x2c,0x4d,0x44,0x89,0xd0,0xc1,0xc0,0x1e,0x44,0x89,0xd6,0xc1,0xc6,0x13,0x31,0xc6,0x44,0x89,0xd0,0xc1,0xc0,0xa,0x31,0xf0,0x89,0xce,0x44,0x21,0xc6,0x41,0x89,0xce,0x45,0x31,0xc6,0x45,0x21,0xd6,0x41,0x31,0xf6,0x89,0xee,0xc1,0xc6,0xf,0x41,0x1,0xc6,0x89,0xe8,0xc1,0xc0,0xd,0x41,0x1,0xd5,0x44,0x89,0xff,0xc1,0xc7,0x19,0x41,0x1,0xd6,0x44,0x89,0xfa,0xc1,0xc2,0xe,0x31,0xf0,0x31,0xfa,0x44,0x89,0xfe,0xc1,0xee,0x3,0x31,0xd6,0x1,0x6c,0x24,0x70,0x1,0xee,0x89,0x74,0x24,0xc,0x89,0xea,0xc1,0xea,0xa,0x44,0x89,0xee,0xc1,0xc6,0x1a,0x31,0xc2,0x44,0x89,0xe8,0xc1,0xc0,0x15,0x8b,0x6c,0x24,0x50,0x1,0xd5,0x44,0x89,0xea,0xc1,0xc2,0x7,0x31,0xf0,0x31,0xc2,0x44,0x89,0xd8,0x44,0x31,0xc8,0x44,0x21,0xe8,0x44,0x31,0xc8,0x41,0x1,0xec,0x41,0x1,0xc4,0x42,0x8d,0x4,0x22,0x5,0x13,0xd,0x38,0x53,0x44,0x89,0xf2,0xc1,0xc2,0x1e,0x44,0x89,0xf6,0xc1,0xc6,0x13,0x31,0xd6]

set_option maxRecDepth 4096 in
theorem part29_bytes [Bindings] : part29.flatMap CheckedInstruction.bytes = part29Bytes  := by
  rfl

def part29Layout : List (BitVec 64 × Nat) :=
  [(0x10ac5d, 3), (0x10ac60, 3), (0x10ac63, 2), (0x10ac65, 3), (0x10ac68, 6), (0x10ac6e, 3), (0x10ac71, 3), (0x10ac74, 3), (0x10ac77, 3), (0x10ac7a, 2), (0x10ac7c, 3), (0x10ac7f, 3), (0x10ac82, 2), (0x10ac84, 2), (0x10ac86, 3), (0x10ac89, 3), (0x10ac8c, 3), (0x10ac8f, 3), (0x10ac92, 3), (0x10ac95, 2), (0x10ac97, 3), (0x10ac9a, 3), (0x10ac9d, 2), (0x10ac9f, 3), (0x10aca2, 3), (0x10aca5, 3), (0x10aca8, 3), (0x10acab, 3), (0x10acae, 3), (0x10acb1, 3), (0x10acb4, 2), (0x10acb6, 2), (0x10acb8, 3), (0x10acbb, 3), (0x10acbe, 2), (0x10acc0, 4), (0x10acc4, 2), (0x10acc6, 4), (0x10acca, 2), (0x10accc, 3), (0x10accf, 3), (0x10acd2, 3), (0x10acd5, 2), (0x10acd7, 3), (0x10acda, 3), (0x10acdd, 4), (0x10ace1, 2), (0x10ace3, 3), (0x10ace6, 3), (0x10ace9, 2), (0x10aceb, 2), (0x10aced, 3), (0x10acf0, 3), (0x10acf3, 3), (0x10acf6, 3), (0x10acf9, 3), (0x10acfc, 3), (0x10acff, 4), (0x10ad03, 5), (0x10ad08, 3), (0x10ad0b, 3), (0x10ad0e, 3), (0x10ad11, 3), (0x10ad14, 2)]

theorem part29_layout [Bindings] : InstructionTrace.layout part29 = part29Layout := by
  rfl

theorem part29_ordered [Bindings] : InstructionTrace.ordered 0x10ac5d part29 = true := by
  rw [InstructionTrace.ordered_eq_layout, part29_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part29_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xac5d 185 = part29Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
