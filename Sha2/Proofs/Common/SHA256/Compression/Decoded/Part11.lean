import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part11 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd6c 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bd6e 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10bd70 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bd73 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd78 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd7a 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd7d 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd80 0xfe rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd82 0xc6 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bd85 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd88 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bd8a 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bd8c 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd8f 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd91 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd94 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd97 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bd9a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bd9d 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bd9f 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10bda2 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bda5 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10bda7 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bdac 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10bdaf 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 224)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bdb7 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bdba 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bdbd 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10bdc0 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bdc5 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bdc8 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bdcb 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bdcd 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bdd0 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bdd3 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bdd5 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bdd7 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bdda 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10bddd 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bde0 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bde3 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bde5 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10bde7 0xc2 0xefbe4786 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bded 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bdf0 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bdf3 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bdf6 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bdf9 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bdfb 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10bdfe 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10be01 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10be06 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10be09 0xce rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10be0b 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10be10 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10be12 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10be1a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10be1d 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10be22 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10be24 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10be27 0xdf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10be29 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10be2c 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10be2f 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part11Bytes : List UInt8 :=
  [0x31,0xf7,0x1,0xcf,0x49,0x89,0xf8,0x48,0x8b,0x7c,0x24,0x68,0x89,0xf9,0xc1,0xc1,0x19,0x41,0x1,0xc1,0x89,0xfe,0xc1,0xc6,0xe,0x41,0x1,0xc0,0x31,0xce,0x89,0xf8,0xc1,0xe8,0x3,0x31,0xf0,0x44,0x89,0xe9,0xc1,0xc1,0xf,0x44,0x89,0xee,0xc1,0xc6,0xd,0x31,0xce,0x44,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xf1,0x44,0x3,0x64,0x24,0xc,0x41,0x1,0xc4,0x4c,0x89,0x8c,0x24,0xe0,0x0,0x0,0x0,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x41,0x1,0xcc,0x4c,0x89,0x64,0x24,0x38,0x44,0x89,0xc9,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xc8,0x89,0xd9,0x44,0x31,0xf9,0x44,0x21,0xc9,0x44,0x31,0xf9,0x44,0x1,0xe2,0x1,0xca,0x1,0xc2,0x81,0xc2,0x86,0x47,0xbe,0xef,0x44,0x89,0xc0,0xc1,0xc0,0x1e,0x44,0x89,0xc1,0xc1,0xc1,0x13,0x31,0xc1,0x44,0x89,0xc6,0x4d,0x89,0xc1,0x4c,0x89,0x44,0x24,0x70,0xc1,0xc6,0xa,0x31,0xce,0x48,0x89,0x6c,0x24,0x78,0x89,0xe9,0x4c,0x89,0x9c,0x24,0xd8,0x0,0x0,0x0,0x44,0x21,0xd9,0x48,0x8b,0x5c,0x24,0x48,0x89,0xd8,0xc1,0xc0,0x19,0x89,0xdf,0xc1,0xc7,0xe,0x44,0x31,0xdd,0x4c,0x89,0x54,0x24,0x50]

set_option maxRecDepth 4096 in
theorem part11_bytes [Bindings] : part11.flatMap CheckedInstruction.bytes = part11Bytes  := by
  rfl

def part11Layout : List (BitVec 64 × Nat) :=
  [(0x10bd6c, 2), (0x10bd6e, 2), (0x10bd70, 3), (0x10bd73, 5), (0x10bd78, 2), (0x10bd7a, 3), (0x10bd7d, 3), (0x10bd80, 2), (0x10bd82, 3), (0x10bd85, 3), (0x10bd88, 2), (0x10bd8a, 2), (0x10bd8c, 3), (0x10bd8f, 2), (0x10bd91, 3), (0x10bd94, 3), (0x10bd97, 3), (0x10bd9a, 3), (0x10bd9d, 2), (0x10bd9f, 3), (0x10bda2, 3), (0x10bda5, 2), (0x10bda7, 5), (0x10bdac, 3), (0x10bdaf, 8), (0x10bdb7, 3), (0x10bdba, 3), (0x10bdbd, 3), (0x10bdc0, 5), (0x10bdc5, 3), (0x10bdc8, 3), (0x10bdcb, 2), (0x10bdcd, 3), (0x10bdd0, 3), (0x10bdd3, 2), (0x10bdd5, 2), (0x10bdd7, 3), (0x10bdda, 3), (0x10bddd, 3), (0x10bde0, 3), (0x10bde3, 2), (0x10bde5, 2), (0x10bde7, 6), (0x10bded, 3), (0x10bdf0, 3), (0x10bdf3, 3), (0x10bdf6, 3), (0x10bdf9, 2), (0x10bdfb, 3), (0x10bdfe, 3), (0x10be01, 5), (0x10be06, 3), (0x10be09, 2), (0x10be0b, 5), (0x10be10, 2), (0x10be12, 8), (0x10be1a, 3), (0x10be1d, 5), (0x10be22, 2), (0x10be24, 3), (0x10be27, 2), (0x10be29, 3), (0x10be2c, 3), (0x10be2f, 5)]

theorem part11_layout [Bindings] : InstructionTrace.layout part11 = part11Layout := by
  rfl

theorem part11_ordered [Bindings] : InstructionTrace.ordered 0x10bd6c part11 = true := by
  rw [InstructionTrace.ordered_eq_layout, part11_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part11_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xbd6c 200 = part11Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
