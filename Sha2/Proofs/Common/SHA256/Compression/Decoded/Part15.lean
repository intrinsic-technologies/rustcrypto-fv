import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part15 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c0ea 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c0ed 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c0f2 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c0f5 0x41 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c0f8 0x45 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c0fb 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c0fe 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c101 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c104 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c10c 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c10f 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c112 0x41 0xc4 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c116 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c119 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c11b 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c11e 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c121 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c123 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c126 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c12a 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c12d 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c130 0x45 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c133 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c136 0x41 0xc7 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c13a 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c13c 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c13f 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c142 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c145 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c148 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c14b 7 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c14f 0xf8 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c151 0 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c155 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c157 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c15a 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c15c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c161 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c164 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c166 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c169 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c16c 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c16f 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c172 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c175 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c177 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c17a 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c17d 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c17f 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c182 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c184 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c187 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c189 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c18c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c194 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c197 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c199 0x4d 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c19c 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c19f 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c1a2 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10c1a4 0x240ca1cc) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c1a9 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c1ac 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c1af 0xca rfl) (by x86_local)]

def part15Bytes : List UInt8 :=
  [0x41,0x89,0xf7,0x4c,0x8b,0x74,0x24,0x78,0x45,0x21,0xf7,0x41,0x89,0xf5,0x45,0x31,0xf5,0x45,0x21,0xcd,0x45,0x31,0xfd,0x41,0x1,0xd5,0x4c,0x8b,0xb4,0x24,0xd8,0x0,0x0,0x0,0x41,0x1,0xc6,0xc1,0xc1,0x19,0x41,0xc1,0xc4,0xe,0x41,0x1,0xc5,0x89,0xfa,0xc1,0xc2,0xf,0x41,0x31,0xcc,0x89,0xf9,0xc1,0xc1,0xd,0x41,0xc1,0xea,0x3,0x44,0x89,0xc0,0xc1,0xc0,0x19,0x45,0x31,0xe2,0x45,0x89,0xc7,0x41,0xc1,0xc7,0xe,0x31,0xd1,0x41,0x31,0xc7,0x44,0x89,0xc0,0x4c,0x89,0xc6,0xc1,0xe8,0x3,0x44,0x31,0xf8,0x1,0x7c,0x24,0x34,0x1,0xf8,0x89,0x44,0x24,0x8,0x89,0xf8,0xc1,0xe8,0xa,0x31,0xc8,0x48,0x8b,0x4c,0x24,0x48,0x44,0x1,0xd1,0x1,0xc1,0x49,0x89,0xc8,0x44,0x89,0xf0,0xc1,0xc0,0x1a,0x44,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd9,0x31,0xd9,0x44,0x21,0xf1,0x31,0xd9,0x48,0x89,0xdf,0x48,0x8b,0x94,0x24,0x80,0x0,0x0,0x0,0x44,0x1,0xc2,0x1,0xca,0x4d,0x89,0xef,0x44,0x89,0xf9,0xc1,0xc1,0x1e,0x1,0xd0,0x5,0xcc,0xa1,0xc,0x24,0x44,0x89,0xfa,0xc1,0xc2,0x13,0x31,0xca]

set_option maxRecDepth 4096 in
theorem part15_bytes [Bindings] : part15.flatMap CheckedInstruction.bytes = part15Bytes  := by
  rfl

def part15Layout : List (BitVec 64 × Nat) :=
  [(0x10c0ea, 3), (0x10c0ed, 5), (0x10c0f2, 3), (0x10c0f5, 3), (0x10c0f8, 3), (0x10c0fb, 3), (0x10c0fe, 3), (0x10c101, 3), (0x10c104, 8), (0x10c10c, 3), (0x10c10f, 3), (0x10c112, 4), (0x10c116, 3), (0x10c119, 2), (0x10c11b, 3), (0x10c11e, 3), (0x10c121, 2), (0x10c123, 3), (0x10c126, 4), (0x10c12a, 3), (0x10c12d, 3), (0x10c130, 3), (0x10c133, 3), (0x10c136, 4), (0x10c13a, 2), (0x10c13c, 3), (0x10c13f, 3), (0x10c142, 3), (0x10c145, 3), (0x10c148, 3), (0x10c14b, 4), (0x10c14f, 2), (0x10c151, 4), (0x10c155, 2), (0x10c157, 3), (0x10c15a, 2), (0x10c15c, 5), (0x10c161, 3), (0x10c164, 2), (0x10c166, 3), (0x10c169, 3), (0x10c16c, 3), (0x10c16f, 3), (0x10c172, 3), (0x10c175, 2), (0x10c177, 3), (0x10c17a, 3), (0x10c17d, 2), (0x10c17f, 3), (0x10c182, 2), (0x10c184, 3), (0x10c187, 2), (0x10c189, 3), (0x10c18c, 8), (0x10c194, 3), (0x10c197, 2), (0x10c199, 3), (0x10c19c, 3), (0x10c19f, 3), (0x10c1a2, 2), (0x10c1a4, 5), (0x10c1a9, 3), (0x10c1ac, 3), (0x10c1af, 2)]

theorem part15_layout [Bindings] : InstructionTrace.layout part15 = part15Layout := by
  rfl

theorem part15_ordered [Bindings] : InstructionTrace.ordered 0x10c0ea part15 = true := by
  rw [InstructionTrace.ordered_eq_layout, part15_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part15_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc0ea 199 = part15Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
