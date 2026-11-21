import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part11 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e4c 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109e4e 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x109e50 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109e53 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109e58 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109e5a 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109e5d 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109e60 0xfe rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109e62 0xc6 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109e65 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e68 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109e6a 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x109e6c 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e6f 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e71 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109e74 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e77 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109e7a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e7d 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e7f 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x109e82 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109e85 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x109e87 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109e8c 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109e8f 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 224)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109e97 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109e9a 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109e9d 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109ea0 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ea5 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ea8 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109eab 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ead 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109eb0 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109eb3 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109eb5 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109eb7 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109eba 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109ebd 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109ec0 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109ec3 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109ec5 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109ec7 0xc2 0xefbe4786 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ecd 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ed0 0xc0 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109ed3 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ed6 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109ed9 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109edb 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x109ede 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109ee1 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ee6 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109ee9 0xce rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109eeb 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109ef0 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109ef2 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109efa 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109efd 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109f02 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109f04 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109f07 0xdf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109f09 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109f0c 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109f0f 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part11Bytes : List UInt8 :=
  [0x31,0xf7,0x1,0xcf,0x49,0x89,0xf8,0x48,0x8b,0x7c,0x24,0x68,0x89,0xf9,0xc1,0xc1,0x19,0x41,0x1,0xc1,0x89,0xfe,0xc1,0xc6,0xe,0x41,0x1,0xc0,0x31,0xce,0x89,0xf8,0xc1,0xe8,0x3,0x31,0xf0,0x44,0x89,0xe9,0xc1,0xc1,0xf,0x44,0x89,0xee,0xc1,0xc6,0xd,0x31,0xce,0x44,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xf1,0x44,0x3,0x64,0x24,0xc,0x41,0x1,0xc4,0x4c,0x89,0x8c,0x24,0xe0,0x0,0x0,0x0,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x41,0x1,0xcc,0x4c,0x89,0x64,0x24,0x38,0x44,0x89,0xc9,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xc8,0x89,0xd9,0x44,0x31,0xf9,0x44,0x21,0xc9,0x44,0x31,0xf9,0x44,0x1,0xe2,0x1,0xca,0x1,0xc2,0x81,0xc2,0x86,0x47,0xbe,0xef,0x44,0x89,0xc0,0xc1,0xc0,0x1e,0x44,0x89,0xc1,0xc1,0xc1,0x13,0x31,0xc1,0x44,0x89,0xc6,0x4d,0x89,0xc1,0x4c,0x89,0x44,0x24,0x70,0xc1,0xc6,0xa,0x31,0xce,0x48,0x89,0x6c,0x24,0x78,0x89,0xe9,0x4c,0x89,0x9c,0x24,0xd8,0x0,0x0,0x0,0x44,0x21,0xd9,0x48,0x8b,0x5c,0x24,0x48,0x89,0xd8,0xc1,0xc0,0x19,0x89,0xdf,0xc1,0xc7,0xe,0x44,0x31,0xdd,0x4c,0x89,0x54,0x24,0x50]

set_option maxRecDepth 4096 in
theorem part11_bytes [Bindings] : part11.flatMap CheckedInstruction.bytes = part11Bytes  := by
  rfl

def part11Layout : List (BitVec 64 × Nat) :=
  [(0x109e4c, 2), (0x109e4e, 2), (0x109e50, 3), (0x109e53, 5), (0x109e58, 2), (0x109e5a, 3), (0x109e5d, 3), (0x109e60, 2), (0x109e62, 3), (0x109e65, 3), (0x109e68, 2), (0x109e6a, 2), (0x109e6c, 3), (0x109e6f, 2), (0x109e71, 3), (0x109e74, 3), (0x109e77, 3), (0x109e7a, 3), (0x109e7d, 2), (0x109e7f, 3), (0x109e82, 3), (0x109e85, 2), (0x109e87, 5), (0x109e8c, 3), (0x109e8f, 8), (0x109e97, 3), (0x109e9a, 3), (0x109e9d, 3), (0x109ea0, 5), (0x109ea5, 3), (0x109ea8, 3), (0x109eab, 2), (0x109ead, 3), (0x109eb0, 3), (0x109eb3, 2), (0x109eb5, 2), (0x109eb7, 3), (0x109eba, 3), (0x109ebd, 3), (0x109ec0, 3), (0x109ec3, 2), (0x109ec5, 2), (0x109ec7, 6), (0x109ecd, 3), (0x109ed0, 3), (0x109ed3, 3), (0x109ed6, 3), (0x109ed9, 2), (0x109edb, 3), (0x109ede, 3), (0x109ee1, 5), (0x109ee6, 3), (0x109ee9, 2), (0x109eeb, 5), (0x109ef0, 2), (0x109ef2, 8), (0x109efa, 3), (0x109efd, 5), (0x109f02, 2), (0x109f04, 3), (0x109f07, 2), (0x109f09, 3), (0x109f0c, 3), (0x109f0f, 5)]

theorem part11_layout [Bindings] : InstructionTrace.layout part11 = part11Layout := by
  rfl

theorem part11_ordered [Bindings] : InstructionTrace.ordered 0x109e4c part11 = true := by
  rw [InstructionTrace.ordered_eq_layout, part11_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part11_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9e4c 200 = part11Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
