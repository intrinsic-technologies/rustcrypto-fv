import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part20 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c4b9 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c4bc 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c4bf 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c4c1 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c4c4 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c4c6 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c4c9 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c4cb 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c4ce 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c4d1 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c4d4 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c4d8 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c4db 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c4de 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c4e1 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c4e4 5 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c4e8 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c4ea 1 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c4ee 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c4f0 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c4f3 0xc1 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c4f5 2 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c4f9 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c4fb 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c4fe 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c501 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c504 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c507 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c509 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c50c 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c50f 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c511 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c514 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c517 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c51a 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c51d 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c51f 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c521 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c524 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10c527 0x44 (by simp [RexNoWPrefix]) 2 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10c52b 0x41 0xc2 0x983e5152 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c532 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c535 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c538 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c53a 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c53d 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c540 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c542 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c545 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c548 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c54a 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c54c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c54f 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c552 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c554 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c557 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c55a 0x41 0xc3 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c55e 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10c561 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c564 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c567 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c56a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c56d 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c570 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part20Bytes : List UInt8 :=
  [0x41,0x1,0xc4,0x41,0x1,0xc0,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xe8,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xf1,0xc1,0xc1,0x19,0x45,0x89,0xf2,0x41,0xc1,0xc2,0xe,0x41,0x31,0xca,0x44,0x89,0xf1,0xc1,0xe9,0x3,0x44,0x31,0xd1,0x1,0x6c,0x24,0x24,0x1,0xe9,0x89,0x4c,0x24,0x14,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xc1,0x8b,0x54,0x24,0x34,0x1,0xca,0x44,0x89,0xe0,0xc1,0xc0,0x1a,0x44,0x89,0xe1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xe0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf9,0x44,0x31,0xc9,0x44,0x21,0xe1,0x44,0x31,0xc9,0x1,0xd6,0x1,0xce,0x44,0x89,0xc1,0xc1,0xc1,0x1e,0x44,0x8d,0x14,0x30,0x41,0x81,0xc2,0x52,0x51,0x3e,0x98,0x44,0x89,0xc0,0xc1,0xc0,0x13,0x31,0xc8,0x44,0x89,0xc1,0xc1,0xc1,0xa,0x31,0xc1,0x41,0x89,0xdb,0x41,0x21,0xfb,0x89,0xd8,0x31,0xf8,0x44,0x21,0xc0,0x44,0x31,0xd8,0x1,0xc8,0x45,0x1,0xd5,0x45,0x89,0xf3,0x41,0xc1,0xc3,0xf,0x44,0x1,0xd0,0x48,0x89,0xc6,0x44,0x89,0xf1,0xc1,0xc1,0xd,0x44,0x31,0xd9,0x41,0x89,0xd2,0x41,0xc1,0xc2,0x19]

set_option maxRecDepth 4096 in
theorem part20_bytes [Bindings] : part20.flatMap CheckedInstruction.bytes = part20Bytes  := by
  rfl

def part20Layout : List (BitVec 64 × Nat) :=
  [(0x10c4b9, 3), (0x10c4bc, 3), (0x10c4bf, 2), (0x10c4c1, 3), (0x10c4c4, 2), (0x10c4c6, 3), (0x10c4c9, 2), (0x10c4cb, 3), (0x10c4ce, 3), (0x10c4d1, 3), (0x10c4d4, 4), (0x10c4d8, 3), (0x10c4db, 3), (0x10c4de, 3), (0x10c4e1, 3), (0x10c4e4, 4), (0x10c4e8, 2), (0x10c4ea, 4), (0x10c4ee, 2), (0x10c4f0, 3), (0x10c4f3, 2), (0x10c4f5, 4), (0x10c4f9, 2), (0x10c4fb, 3), (0x10c4fe, 3), (0x10c501, 3), (0x10c504, 3), (0x10c507, 2), (0x10c509, 3), (0x10c50c, 3), (0x10c50f, 2), (0x10c511, 3), (0x10c514, 3), (0x10c517, 3), (0x10c51a, 3), (0x10c51d, 2), (0x10c51f, 2), (0x10c521, 3), (0x10c524, 3), (0x10c527, 4), (0x10c52b, 7), (0x10c532, 3), (0x10c535, 3), (0x10c538, 2), (0x10c53a, 3), (0x10c53d, 3), (0x10c540, 2), (0x10c542, 3), (0x10c545, 3), (0x10c548, 2), (0x10c54a, 2), (0x10c54c, 3), (0x10c54f, 3), (0x10c552, 2), (0x10c554, 3), (0x10c557, 3), (0x10c55a, 4), (0x10c55e, 3), (0x10c561, 3), (0x10c564, 3), (0x10c567, 3), (0x10c56a, 3), (0x10c56d, 3), (0x10c570, 4)]

theorem part20_layout [Bindings] : InstructionTrace.layout part20 = part20Layout := by
  rfl

theorem part20_ordered [Bindings] : InstructionTrace.ordered 0x10c4b9 part20 = true := by
  rw [InstructionTrace.ordered_eq_layout, part20_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part20_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc4b9 187 = part20Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
