import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part26 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_effect_step 0x116e05 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116e07 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116e0a 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116e0e 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116e11 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116e13 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116e16 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116e18 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116e1b 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116e1d 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116e20 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x116e22 0 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116e26 0xc7 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116e28 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116e2c 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116e2f 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116e31 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116e34 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116e36 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116e38 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x116e3b 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 140)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116e43 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116e46 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116e48 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116e4b 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116e4d 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116e4f 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116e52 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x116e55 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116e57 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x116e5a 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116e5d 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116e60 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x116e63 0x42 (by simp [RexNoWPrefix]) 1 (.sib 2 (some 8) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116e67 0xc1 0x14292967 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116e6d 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116e70 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116e73 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116e76 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116e79 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116e7b 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116e7e 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116e81 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116e83 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116e86 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116e89 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116e8c 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116e8f 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116e92 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116e95 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116e98 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116e9b 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116e9e 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116ea0 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116ea3 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116ea5 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116ea8 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116eaa 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116ead 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116eb0 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116eb3 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116eb6 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116eb8 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116ebb 0xea 0x3 rfl rfl) (by x86_local)]

def part26Bytes : List UInt8 :=
  [0x1,0xd6,0x41,0x89,0xea,0x41,0xc1,0xc2,0x19,0x41,0x1,0xd5,0x89,0xea,0xc1,0xc2,0xe,0x31,0xf9,0x44,0x31,0xd2,0x89,0xef,0xc1,0xef,0x3,0x31,0xd7,0x1,0x44,0x24,0x78,0x1,0xc7,0x89,0x7c,0x24,0x24,0xc1,0xe8,0xa,0x89,0xf7,0xc1,0xc7,0x1a,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x15,0x44,0x8b,0x94,0x24,0x8c,0x0,0x0,0x0,0x41,0x1,0xc2,0x89,0xf2,0xc1,0xc2,0x7,0x31,0xf9,0x31,0xca,0x44,0x89,0xf1,0x44,0x31,0xf9,0x21,0xf1,0x44,0x31,0xf9,0x4c,0x89,0xf8,0x45,0x1,0xd0,0x41,0x1,0xc8,0x42,0x8d,0xc,0x2,0x81,0xc1,0x67,0x29,0x29,0x14,0x44,0x89,0xea,0xc1,0xc2,0x1e,0x44,0x89,0xef,0xc1,0xc7,0x13,0x31,0xd7,0x44,0x89,0xea,0xc1,0xc2,0xa,0x31,0xfa,0x44,0x89,0xdf,0x44,0x21,0xcf,0x45,0x89,0xd8,0x45,0x31,0xc8,0x45,0x21,0xe8,0x41,0x31,0xf8,0x41,0x1,0xd0,0x41,0x1,0xcc,0x41,0x1,0xc8,0x89,0xea,0xc1,0xc2,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xd7,0x44,0x89,0xd2,0xc1,0xea,0x3]

set_option maxRecDepth 4096 in
theorem part26_bytes [Bindings] : part26.flatMap CheckedInstruction.bytes = part26Bytes  := by
  rfl

def part26Layout : List (BitVec 64 × Nat) :=
  [(0x116e05, 2), (0x116e07, 3), (0x116e0a, 4), (0x116e0e, 3), (0x116e11, 2), (0x116e13, 3), (0x116e16, 2), (0x116e18, 3), (0x116e1b, 2), (0x116e1d, 3), (0x116e20, 2), (0x116e22, 4), (0x116e26, 2), (0x116e28, 4), (0x116e2c, 3), (0x116e2f, 2), (0x116e31, 3), (0x116e34, 2), (0x116e36, 2), (0x116e38, 3), (0x116e3b, 8), (0x116e43, 3), (0x116e46, 2), (0x116e48, 3), (0x116e4b, 2), (0x116e4d, 2), (0x116e4f, 3), (0x116e52, 3), (0x116e55, 2), (0x116e57, 3), (0x116e5a, 3), (0x116e5d, 3), (0x116e60, 3), (0x116e63, 4), (0x116e67, 6), (0x116e6d, 3), (0x116e70, 3), (0x116e73, 3), (0x116e76, 3), (0x116e79, 2), (0x116e7b, 3), (0x116e7e, 3), (0x116e81, 2), (0x116e83, 3), (0x116e86, 3), (0x116e89, 3), (0x116e8c, 3), (0x116e8f, 3), (0x116e92, 3), (0x116e95, 3), (0x116e98, 3), (0x116e9b, 3), (0x116e9e, 2), (0x116ea0, 3), (0x116ea3, 2), (0x116ea5, 3), (0x116ea8, 2), (0x116eaa, 3), (0x116ead, 3), (0x116eb0, 3), (0x116eb3, 3), (0x116eb6, 2), (0x116eb8, 3), (0x116ebb, 3)]

theorem part26_layout [Bindings] : InstructionTrace.layout part26 = part26Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part26_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16e05 185 = part26Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
