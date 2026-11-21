import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part46 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117cd9 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117cdc 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117cde 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117ce1 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117ce4 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117ce6 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117ce9 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117cec 0xc1 0x682e6ff3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117cf2 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117cf4 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117cf7 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117cf9 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117cfb 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117cfe 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117d00 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117d02 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d05 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117d08 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117d0b 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117d0e 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117d11 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117d14 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117d17 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d19 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117d1c 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117d1f 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d21 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d24 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x117d26 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117d2a 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x117d2c 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d2f 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d31 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d34 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x117d37 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117d3b 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d3d 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d40 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d43 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d45 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d48 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d4b 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d4d 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117d50 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117d53 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117d56 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117d59 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117d5b 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x117d5d 2 (.sib 1 (some 3) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x117d60 0xc2 0x748f82ee rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d66 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d69 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d6c 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d6f 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d72 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117d74 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117d77 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d7a 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117d7c 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x117d7e 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117d80 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d82 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117d84 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117d87 0xf9 rfl) (by x86_local)]

def part46Bytes : List UInt8 :=
  [0x44,0x21,0xd2,0x31,0xda,0x45,0x1,0xf0,0x41,0x1,0xd0,0x89,0xf2,0xc1,0xc2,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xf3,0x6f,0x2e,0x68,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xd7,0x89,0xf2,0xc1,0xc2,0xa,0x31,0xfa,0x89,0xc7,0x44,0x21,0xef,0x41,0x89,0xc0,0x45,0x31,0xe8,0x41,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xd0,0x41,0x1,0xc9,0x89,0xea,0xc1,0xc2,0xf,0x41,0x1,0xc8,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xd1,0x1,0x6c,0x24,0x4,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0x1a,0x8b,0x6c,0x24,0x68,0x1,0xd5,0x44,0x89,0xca,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xd2,0x44,0x31,0xda,0x44,0x21,0xca,0x44,0x31,0xda,0x1,0xeb,0x1,0xd3,0x8d,0x14,0x19,0x81,0xc2,0xee,0x82,0x8f,0x74,0x44,0x89,0xc1,0xc1,0xc1,0x1e,0x44,0x89,0xc7,0xc1,0xc7,0x13,0x31,0xcf,0x44,0x89,0xc3,0xc1,0xc3,0xa,0x31,0xfb,0x89,0xf7,0x21,0xc7,0x89,0xf1,0x31,0xc1,0x44,0x21,0xc1,0x31,0xf9]

set_option maxRecDepth 4096 in
theorem part46_bytes [Bindings] : part46.flatMap CheckedInstruction.bytes = part46Bytes  := by
  rfl

def part46Layout : List (BitVec 64 × Nat) :=
  [(0x117cd9, 3), (0x117cdc, 2), (0x117cde, 3), (0x117ce1, 3), (0x117ce4, 2), (0x117ce6, 3), (0x117ce9, 3), (0x117cec, 6), (0x117cf2, 2), (0x117cf4, 3), (0x117cf7, 2), (0x117cf9, 2), (0x117cfb, 3), (0x117cfe, 2), (0x117d00, 2), (0x117d02, 3), (0x117d05, 3), (0x117d08, 3), (0x117d0b, 3), (0x117d0e, 3), (0x117d11, 3), (0x117d14, 3), (0x117d17, 2), (0x117d19, 3), (0x117d1c, 3), (0x117d1f, 2), (0x117d21, 3), (0x117d24, 2), (0x117d26, 4), (0x117d2a, 2), (0x117d2c, 3), (0x117d2f, 2), (0x117d31, 3), (0x117d34, 3), (0x117d37, 4), (0x117d3b, 2), (0x117d3d, 3), (0x117d40, 3), (0x117d43, 2), (0x117d45, 3), (0x117d48, 3), (0x117d4b, 2), (0x117d4d, 3), (0x117d50, 3), (0x117d53, 3), (0x117d56, 3), (0x117d59, 2), (0x117d5b, 2), (0x117d5d, 3), (0x117d60, 6), (0x117d66, 3), (0x117d69, 3), (0x117d6c, 3), (0x117d6f, 3), (0x117d72, 2), (0x117d74, 3), (0x117d77, 3), (0x117d7a, 2), (0x117d7c, 2), (0x117d7e, 2), (0x117d80, 2), (0x117d82, 2), (0x117d84, 3), (0x117d87, 2)]

theorem part46_layout [Bindings] : InstructionTrace.layout part46 = part46Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part46_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x17cd9 176 = part46Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
