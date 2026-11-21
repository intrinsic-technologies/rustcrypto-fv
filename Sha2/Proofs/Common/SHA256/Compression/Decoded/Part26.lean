import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part26 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c955 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c957 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c95a 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c95e 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c961 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c963 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c966 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c968 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c96b 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c96d 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c970 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c972 0 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c976 0xc7 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c978 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c97c 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c97f 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c981 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c984 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c986 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c988 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10c98b 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 140)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c993 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c996 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c998 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c99b 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c99d 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c99f 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c9a2 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10c9a5 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c9a7 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c9aa 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c9ad 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c9b0 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10c9b3 0x42 (by simp [RexNoWPrefix]) 1 (.sib 2 (some 8) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10c9b7 0xc1 0x14292967 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c9bd 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c9c0 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c9c3 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c9c6 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c9c9 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c9cb 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c9ce 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c9d1 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c9d3 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c9d6 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c9d9 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c9dc 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c9df 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c9e2 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c9e5 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c9e8 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c9eb 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c9ee 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c9f0 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c9f3 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c9f5 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c9f8 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c9fa 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c9fd 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca00 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca03 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca06 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca08 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ca0b 0xea 0x3 rfl rfl) (by x86_local)]

def part26Bytes : List UInt8 :=
  [0x1,0xd6,0x41,0x89,0xea,0x41,0xc1,0xc2,0x19,0x41,0x1,0xd5,0x89,0xea,0xc1,0xc2,0xe,0x31,0xf9,0x44,0x31,0xd2,0x89,0xef,0xc1,0xef,0x3,0x31,0xd7,0x1,0x44,0x24,0x78,0x1,0xc7,0x89,0x7c,0x24,0x24,0xc1,0xe8,0xa,0x89,0xf7,0xc1,0xc7,0x1a,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x15,0x44,0x8b,0x94,0x24,0x8c,0x0,0x0,0x0,0x41,0x1,0xc2,0x89,0xf2,0xc1,0xc2,0x7,0x31,0xf9,0x31,0xca,0x44,0x89,0xf1,0x44,0x31,0xf9,0x21,0xf1,0x44,0x31,0xf9,0x4c,0x89,0xf8,0x45,0x1,0xd0,0x41,0x1,0xc8,0x42,0x8d,0xc,0x2,0x81,0xc1,0x67,0x29,0x29,0x14,0x44,0x89,0xea,0xc1,0xc2,0x1e,0x44,0x89,0xef,0xc1,0xc7,0x13,0x31,0xd7,0x44,0x89,0xea,0xc1,0xc2,0xa,0x31,0xfa,0x44,0x89,0xdf,0x44,0x21,0xcf,0x45,0x89,0xd8,0x45,0x31,0xc8,0x45,0x21,0xe8,0x41,0x31,0xf8,0x41,0x1,0xd0,0x41,0x1,0xcc,0x41,0x1,0xc8,0x89,0xea,0xc1,0xc2,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xd7,0x44,0x89,0xd2,0xc1,0xea,0x3]

set_option maxRecDepth 4096 in
theorem part26_bytes [Bindings] : part26.flatMap CheckedInstruction.bytes = part26Bytes  := by
  rfl

def part26Layout : List (BitVec 64 × Nat) :=
  [(0x10c955, 2), (0x10c957, 3), (0x10c95a, 4), (0x10c95e, 3), (0x10c961, 2), (0x10c963, 3), (0x10c966, 2), (0x10c968, 3), (0x10c96b, 2), (0x10c96d, 3), (0x10c970, 2), (0x10c972, 4), (0x10c976, 2), (0x10c978, 4), (0x10c97c, 3), (0x10c97f, 2), (0x10c981, 3), (0x10c984, 2), (0x10c986, 2), (0x10c988, 3), (0x10c98b, 8), (0x10c993, 3), (0x10c996, 2), (0x10c998, 3), (0x10c99b, 2), (0x10c99d, 2), (0x10c99f, 3), (0x10c9a2, 3), (0x10c9a5, 2), (0x10c9a7, 3), (0x10c9aa, 3), (0x10c9ad, 3), (0x10c9b0, 3), (0x10c9b3, 4), (0x10c9b7, 6), (0x10c9bd, 3), (0x10c9c0, 3), (0x10c9c3, 3), (0x10c9c6, 3), (0x10c9c9, 2), (0x10c9cb, 3), (0x10c9ce, 3), (0x10c9d1, 2), (0x10c9d3, 3), (0x10c9d6, 3), (0x10c9d9, 3), (0x10c9dc, 3), (0x10c9df, 3), (0x10c9e2, 3), (0x10c9e5, 3), (0x10c9e8, 3), (0x10c9eb, 3), (0x10c9ee, 2), (0x10c9f0, 3), (0x10c9f3, 2), (0x10c9f5, 3), (0x10c9f8, 2), (0x10c9fa, 3), (0x10c9fd, 3), (0x10ca00, 3), (0x10ca03, 3), (0x10ca06, 2), (0x10ca08, 3), (0x10ca0b, 3)]

theorem part26_layout [Bindings] : InstructionTrace.layout part26 = part26Layout := by
  rfl

theorem part26_ordered [Bindings] : InstructionTrace.ordered 0x10c955 part26 = true := by
  rw [InstructionTrace.ordered_eq_layout, part26_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part26_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc955 185 = part26Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
