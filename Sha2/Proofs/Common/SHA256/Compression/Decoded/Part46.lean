import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part46 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d829 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d82c 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d82e 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d831 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d834 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d836 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d839 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10d83c 0xc1 0x682e6ff3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d842 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d844 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d847 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d849 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d84b 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d84e 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d850 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d852 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d855 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d858 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d85b 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d85e 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d861 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d864 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d867 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d869 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d86c 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d86f 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d871 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d874 0xd1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10d876 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d87a 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d87c 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d87f 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d881 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d884 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d887 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d88b 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d88d 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d890 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d893 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d895 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d898 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d89b 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d89d 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d8a0 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d8a3 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d8a6 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d8a9 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d8ab 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10d8ad 2 (.sib 1 (some 3) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10d8b0 0xc2 0x748f82ee rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d8b6 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d8b9 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d8bc 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d8bf 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d8c2 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d8c4 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d8c7 0xc3 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d8ca 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d8cc 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d8ce 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d8d0 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d8d2 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d8d4 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d8d7 0xf9 rfl) (by x86_local)]

def part46Bytes : List UInt8 :=
  [0x44,0x21,0xd2,0x31,0xda,0x45,0x1,0xf0,0x41,0x1,0xd0,0x89,0xf2,0xc1,0xc2,0x1e,0x44,0x1,0xc1,0x81,0xc1,0xf3,0x6f,0x2e,0x68,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xd7,0x89,0xf2,0xc1,0xc2,0xa,0x31,0xfa,0x89,0xc7,0x44,0x21,0xef,0x41,0x89,0xc0,0x45,0x31,0xe8,0x41,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xd0,0x41,0x1,0xc9,0x89,0xea,0xc1,0xc2,0xf,0x41,0x1,0xc8,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xd1,0x1,0x6c,0x24,0x4,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0x1a,0x8b,0x6c,0x24,0x68,0x1,0xd5,0x44,0x89,0xca,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xd2,0x44,0x31,0xda,0x44,0x21,0xca,0x44,0x31,0xda,0x1,0xeb,0x1,0xd3,0x8d,0x14,0x19,0x81,0xc2,0xee,0x82,0x8f,0x74,0x44,0x89,0xc1,0xc1,0xc1,0x1e,0x44,0x89,0xc7,0xc1,0xc7,0x13,0x31,0xcf,0x44,0x89,0xc3,0xc1,0xc3,0xa,0x31,0xfb,0x89,0xf7,0x21,0xc7,0x89,0xf1,0x31,0xc1,0x44,0x21,0xc1,0x31,0xf9]

set_option maxRecDepth 4096 in
theorem part46_bytes [Bindings] : part46.flatMap CheckedInstruction.bytes = part46Bytes  := by
  rfl

def part46Layout : List (BitVec 64 × Nat) :=
  [(0x10d829, 3), (0x10d82c, 2), (0x10d82e, 3), (0x10d831, 3), (0x10d834, 2), (0x10d836, 3), (0x10d839, 3), (0x10d83c, 6), (0x10d842, 2), (0x10d844, 3), (0x10d847, 2), (0x10d849, 2), (0x10d84b, 3), (0x10d84e, 2), (0x10d850, 2), (0x10d852, 3), (0x10d855, 3), (0x10d858, 3), (0x10d85b, 3), (0x10d85e, 3), (0x10d861, 3), (0x10d864, 3), (0x10d867, 2), (0x10d869, 3), (0x10d86c, 3), (0x10d86f, 2), (0x10d871, 3), (0x10d874, 2), (0x10d876, 4), (0x10d87a, 2), (0x10d87c, 3), (0x10d87f, 2), (0x10d881, 3), (0x10d884, 3), (0x10d887, 4), (0x10d88b, 2), (0x10d88d, 3), (0x10d890, 3), (0x10d893, 2), (0x10d895, 3), (0x10d898, 3), (0x10d89b, 2), (0x10d89d, 3), (0x10d8a0, 3), (0x10d8a3, 3), (0x10d8a6, 3), (0x10d8a9, 2), (0x10d8ab, 2), (0x10d8ad, 3), (0x10d8b0, 6), (0x10d8b6, 3), (0x10d8b9, 3), (0x10d8bc, 3), (0x10d8bf, 3), (0x10d8c2, 2), (0x10d8c4, 3), (0x10d8c7, 3), (0x10d8ca, 2), (0x10d8cc, 2), (0x10d8ce, 2), (0x10d8d0, 2), (0x10d8d2, 2), (0x10d8d4, 3), (0x10d8d7, 2)]

theorem part46_layout [Bindings] : InstructionTrace.layout part46 = part46Layout := by
  rfl

theorem part46_ordered [Bindings] : InstructionTrace.ordered 0x10d829 part46 = true := by
  rw [InstructionTrace.ordered_eq_layout, part46_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part46_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd829 176 = part46Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
