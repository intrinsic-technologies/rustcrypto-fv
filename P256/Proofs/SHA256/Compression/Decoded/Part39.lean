import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu
import P256.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part39 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1177d1 0xc7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x1177d3 1 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1177d7 0xcf rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x1177d9 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1177dc 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x1177de 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1177e1 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1177e3 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1177e6 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x1177e9 1 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1177ed 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1177ef 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1177f2 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1177f5 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1177f7 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1177fa 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1177fd 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1177ff 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117801 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117804 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117807 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11780a 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x11780c 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x11780e 0 (.sib 6 (some 2) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x117811 0xf40e3585) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117816 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117819 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11781c 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11781f 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117822 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117824 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117827 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11782b 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11782e 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x117831 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117834 0x45 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117837 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x11783a 0x45 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x11783d 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117840 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117842 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117845 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117848 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x11784a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11784d 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x117852 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x117854 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x117857 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x11785b 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x11785e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117860 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x117863 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x117865 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117868 0xca rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11786a 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x11786d 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x11786f 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x117874 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x117877 2 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x11787b 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x11787e 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x117881 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x117884 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x117886 0xc7 0x1a rfl rfl) (by x86_local)]

def part39Bytes : List UInt8 :=
  [0x31,0xc7,0x1,0x4c,0x24,0x50,0x1,0xcf,0x89,0x3c,0x24,0x89,0xc8,0xc1,0xe8,0xa,0x31,0xf0,0x44,0x89,0xfe,0xc1,0xc6,0x1a,0x8b,0x4c,0x24,0x4,0x1,0xc1,0x44,0x89,0xf8,0xc1,0xc0,0x15,0x31,0xf0,0x44,0x89,0xfe,0xc1,0xc6,0x7,0x31,0xc6,0x89,0xd8,0x44,0x31,0xd8,0x44,0x21,0xf8,0x44,0x31,0xd8,0x1,0xca,0x1,0xc2,0x8d,0x4,0x16,0x5,0x85,0x35,0xe,0xf4,0x44,0x89,0xe2,0xc1,0xc2,0x1e,0x44,0x89,0xe6,0xc1,0xc6,0x13,0x31,0xd6,0x45,0x89,0xe0,0x41,0xc1,0xc0,0xa,0x41,0x31,0xf0,0x44,0x89,0xee,0x44,0x21,0xce,0x45,0x89,0xee,0x45,0x31,0xce,0x45,0x21,0xe6,0x41,0x31,0xf6,0x89,0xef,0xc1,0xc7,0xf,0x45,0x1,0xc6,0x89,0xee,0xc1,0xc6,0xd,0x48,0x8b,0x6c,0x24,0x38,0x1,0xc5,0x41,0x89,0xc8,0x41,0xc1,0xc0,0x19,0x41,0x1,0xc6,0x89,0xc8,0xc1,0xc0,0xe,0x31,0xfe,0x44,0x31,0xc0,0x89,0xca,0xc1,0xea,0x3,0x31,0xc2,0x44,0x1,0x54,0x24,0x78,0x44,0x1,0xd2,0x89,0x54,0x24,0x4,0x44,0x89,0xd0,0xc1,0xe8,0xa,0x48,0x89,0xea,0x89,0xef,0xc1,0xc7,0x1a]

set_option maxRecDepth 4096 in
theorem part39_bytes [Bindings] : part39.flatMap CheckedInstruction.bytes = part39Bytes  := by
  rfl

def part39Layout : List (BitVec 64 × Nat) :=
  [(0x1177d1, 2), (0x1177d3, 4), (0x1177d7, 2), (0x1177d9, 3), (0x1177dc, 2), (0x1177de, 3), (0x1177e1, 2), (0x1177e3, 3), (0x1177e6, 3), (0x1177e9, 4), (0x1177ed, 2), (0x1177ef, 3), (0x1177f2, 3), (0x1177f5, 2), (0x1177f7, 3), (0x1177fa, 3), (0x1177fd, 2), (0x1177ff, 2), (0x117801, 3), (0x117804, 3), (0x117807, 3), (0x11780a, 2), (0x11780c, 2), (0x11780e, 3), (0x117811, 5), (0x117816, 3), (0x117819, 3), (0x11781c, 3), (0x11781f, 3), (0x117822, 2), (0x117824, 3), (0x117827, 4), (0x11782b, 3), (0x11782e, 3), (0x117831, 3), (0x117834, 3), (0x117837, 3), (0x11783a, 3), (0x11783d, 3), (0x117840, 2), (0x117842, 3), (0x117845, 3), (0x117848, 2), (0x11784a, 3), (0x11784d, 5), (0x117852, 2), (0x117854, 3), (0x117857, 4), (0x11785b, 3), (0x11785e, 2), (0x117860, 3), (0x117863, 2), (0x117865, 3), (0x117868, 2), (0x11786a, 3), (0x11786d, 2), (0x11786f, 5), (0x117874, 3), (0x117877, 4), (0x11787b, 3), (0x11787e, 3), (0x117881, 3), (0x117884, 2), (0x117886, 3)]

theorem part39_layout [Bindings] : InstructionTrace.layout part39 = part39Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part39_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x177d1 184 = part39Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
