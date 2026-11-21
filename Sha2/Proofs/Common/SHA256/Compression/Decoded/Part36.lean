import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part36 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d0e8 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d0eb 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d0ee 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d0f1 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d0f4 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d0f7 0x45 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d0fa 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d0fd 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d100 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d104 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10d107 0x4d 0xf4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d10a 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d10d 0x41 0xc0 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d111 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d113 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d116 0x41 0xc6 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d11a 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d11d 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d11f 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d122 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d125 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d128 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10d12b 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d12f 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10d132 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d137 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10d13a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d13f 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10d142 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d14a 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d14d 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d150 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d153 0x41 0xc1 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d157 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d15a 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d15d 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10d161 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d166 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d169 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d16b 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d16e 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d171 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d174 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d177 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d17a 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d17d 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d180 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d183 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d186 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10d188 0xc1 0xc76c51a3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d18e 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d191 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d194 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d197 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d19b 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d19e 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d1a1 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d1a4 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d1a7 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d1aa 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d1ad 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d1b0 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d1b3 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d1b6 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part36Bytes : List UInt8 :=
  [0x45,0x31,0xc8,0x41,0x89,0xd9,0x45,0x21,0xd9,0x41,0x89,0xde,0x45,0x31,0xde,0x45,0x21,0xfe,0x45,0x31,0xce,0x45,0x89,0xd1,0x41,0xc1,0xc1,0xf,0x45,0x1,0xc6,0x4d,0x89,0xf4,0x45,0x89,0xd0,0x41,0xc1,0xc0,0xd,0x1,0xca,0x41,0x89,0xee,0x41,0xc1,0xc6,0x19,0x41,0x1,0xcc,0x89,0xe9,0xc1,0xc1,0xe,0x45,0x31,0xc8,0x44,0x31,0xf1,0x41,0x89,0xe9,0x41,0xc1,0xe9,0x3,0x41,0x31,0xc9,0x48,0x8b,0x4c,0x24,0x28,0x44,0x1,0xd1,0x48,0x89,0x4c,0x24,0x28,0x45,0x1,0xd1,0x44,0x89,0x8c,0x24,0x80,0x0,0x0,0x0,0x44,0x89,0xd1,0xc1,0xe9,0xa,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x1a,0x44,0x31,0xc1,0x41,0x89,0xd0,0x41,0xc1,0xc0,0x15,0x44,0x8b,0x74,0x24,0x58,0x41,0x1,0xce,0x89,0xd1,0xc1,0xc1,0x7,0x45,0x31,0xc8,0x44,0x31,0xc1,0x41,0x89,0xf0,0x41,0x31,0xc0,0x41,0x21,0xd0,0x41,0x31,0xc0,0x44,0x1,0xf7,0x44,0x1,0xc7,0x1,0xf9,0x81,0xc1,0xa3,0x51,0x6c,0xc7,0x44,0x89,0xe7,0xc1,0xc7,0x1e,0x45,0x89,0xe0,0x41,0xc1,0xc0,0x13,0x41,0x31,0xf8,0x44,0x89,0xe7,0xc1,0xc7,0xa,0x44,0x31,0xc7,0x45,0x89,0xf8,0x41,0x21,0xd8,0x45,0x89,0xf9,0x41,0x31,0xd9,0x45,0x21,0xe1,0x45,0x31,0xc1]

set_option maxRecDepth 4096 in
theorem part36_bytes [Bindings] : part36.flatMap CheckedInstruction.bytes = part36Bytes  := by
  rfl

def part36Layout : List (BitVec 64 × Nat) :=
  [(0x10d0e8, 3), (0x10d0eb, 3), (0x10d0ee, 3), (0x10d0f1, 3), (0x10d0f4, 3), (0x10d0f7, 3), (0x10d0fa, 3), (0x10d0fd, 3), (0x10d100, 4), (0x10d104, 3), (0x10d107, 3), (0x10d10a, 3), (0x10d10d, 4), (0x10d111, 2), (0x10d113, 3), (0x10d116, 4), (0x10d11a, 3), (0x10d11d, 2), (0x10d11f, 3), (0x10d122, 3), (0x10d125, 3), (0x10d128, 3), (0x10d12b, 4), (0x10d12f, 3), (0x10d132, 5), (0x10d137, 3), (0x10d13a, 5), (0x10d13f, 3), (0x10d142, 8), (0x10d14a, 3), (0x10d14d, 3), (0x10d150, 3), (0x10d153, 4), (0x10d157, 3), (0x10d15a, 3), (0x10d15d, 4), (0x10d161, 5), (0x10d166, 3), (0x10d169, 2), (0x10d16b, 3), (0x10d16e, 3), (0x10d171, 3), (0x10d174, 3), (0x10d177, 3), (0x10d17a, 3), (0x10d17d, 3), (0x10d180, 3), (0x10d183, 3), (0x10d186, 2), (0x10d188, 6), (0x10d18e, 3), (0x10d191, 3), (0x10d194, 3), (0x10d197, 4), (0x10d19b, 3), (0x10d19e, 3), (0x10d1a1, 3), (0x10d1a4, 3), (0x10d1a7, 3), (0x10d1aa, 3), (0x10d1ad, 3), (0x10d1b0, 3), (0x10d1b3, 3), (0x10d1b6, 3)]

theorem part36_layout [Bindings] : InstructionTrace.layout part36 = part36Layout := by
  rfl

theorem part36_ordered [Bindings] : InstructionTrace.ordered 0x10d0e8 part36 = true := by
  rw [InstructionTrace.ordered_eq_layout, part36_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part36_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd0e8 209 = part36Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
