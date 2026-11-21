import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part39 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b401 0xc7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b403 1 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b407 0xcf rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b409 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b40c 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b40e 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b411 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b413 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b416 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b419 1 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b41d 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b41f 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b422 0xc0 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b425 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b427 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b42a 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b42d 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b42f 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b431 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b434 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b437 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b43a 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b43c 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10b43e 0 (.sib 6 (some 2) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10b441 0xf40e3585) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b446 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b449 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b44c 0x44 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b44f 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b452 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b454 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b457 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b45b 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b45e 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b461 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b464 0x45 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b467 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b46a 0x45 0xe6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b46d 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b470 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b472 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b475 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b478 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b47a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b47d 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b482 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b484 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b487 0x41 0xc0 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b48b 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b48e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b490 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b493 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b495 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b498 0xca rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b49a 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b49d 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10b49f 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b4a4 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b4a7 2 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b4ab 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b4ae 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b4b1 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b4b4 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b4b6 0xc7 0x1a rfl rfl) (by x86_local)]

def part39Bytes : List UInt8 :=
  [0x31,0xc7,0x1,0x4c,0x24,0x50,0x1,0xcf,0x89,0x3c,0x24,0x89,0xc8,0xc1,0xe8,0xa,0x31,0xf0,0x44,0x89,0xfe,0xc1,0xc6,0x1a,0x8b,0x4c,0x24,0x4,0x1,0xc1,0x44,0x89,0xf8,0xc1,0xc0,0x15,0x31,0xf0,0x44,0x89,0xfe,0xc1,0xc6,0x7,0x31,0xc6,0x89,0xd8,0x44,0x31,0xd8,0x44,0x21,0xf8,0x44,0x31,0xd8,0x1,0xca,0x1,0xc2,0x8d,0x4,0x16,0x5,0x85,0x35,0xe,0xf4,0x44,0x89,0xe2,0xc1,0xc2,0x1e,0x44,0x89,0xe6,0xc1,0xc6,0x13,0x31,0xd6,0x45,0x89,0xe0,0x41,0xc1,0xc0,0xa,0x41,0x31,0xf0,0x44,0x89,0xee,0x44,0x21,0xce,0x45,0x89,0xee,0x45,0x31,0xce,0x45,0x21,0xe6,0x41,0x31,0xf6,0x89,0xef,0xc1,0xc7,0xf,0x45,0x1,0xc6,0x89,0xee,0xc1,0xc6,0xd,0x48,0x8b,0x6c,0x24,0x38,0x1,0xc5,0x41,0x89,0xc8,0x41,0xc1,0xc0,0x19,0x41,0x1,0xc6,0x89,0xc8,0xc1,0xc0,0xe,0x31,0xfe,0x44,0x31,0xc0,0x89,0xca,0xc1,0xea,0x3,0x31,0xc2,0x44,0x1,0x54,0x24,0x78,0x44,0x1,0xd2,0x89,0x54,0x24,0x4,0x44,0x89,0xd0,0xc1,0xe8,0xa,0x48,0x89,0xea,0x89,0xef,0xc1,0xc7,0x1a]

set_option maxRecDepth 4096 in
theorem part39_bytes [Bindings] : part39.flatMap CheckedInstruction.bytes = part39Bytes  := by
  rfl

def part39Layout : List (BitVec 64 × Nat) :=
  [(0x10b401, 2), (0x10b403, 4), (0x10b407, 2), (0x10b409, 3), (0x10b40c, 2), (0x10b40e, 3), (0x10b411, 2), (0x10b413, 3), (0x10b416, 3), (0x10b419, 4), (0x10b41d, 2), (0x10b41f, 3), (0x10b422, 3), (0x10b425, 2), (0x10b427, 3), (0x10b42a, 3), (0x10b42d, 2), (0x10b42f, 2), (0x10b431, 3), (0x10b434, 3), (0x10b437, 3), (0x10b43a, 2), (0x10b43c, 2), (0x10b43e, 3), (0x10b441, 5), (0x10b446, 3), (0x10b449, 3), (0x10b44c, 3), (0x10b44f, 3), (0x10b452, 2), (0x10b454, 3), (0x10b457, 4), (0x10b45b, 3), (0x10b45e, 3), (0x10b461, 3), (0x10b464, 3), (0x10b467, 3), (0x10b46a, 3), (0x10b46d, 3), (0x10b470, 2), (0x10b472, 3), (0x10b475, 3), (0x10b478, 2), (0x10b47a, 3), (0x10b47d, 5), (0x10b482, 2), (0x10b484, 3), (0x10b487, 4), (0x10b48b, 3), (0x10b48e, 2), (0x10b490, 3), (0x10b493, 2), (0x10b495, 3), (0x10b498, 2), (0x10b49a, 3), (0x10b49d, 2), (0x10b49f, 5), (0x10b4a4, 3), (0x10b4a7, 4), (0x10b4ab, 3), (0x10b4ae, 3), (0x10b4b1, 3), (0x10b4b4, 2), (0x10b4b6, 3)]

theorem part39_layout [Bindings] : InstructionTrace.layout part39 = part39Layout := by
  rfl

theorem part39_ordered [Bindings] : InstructionTrace.ordered 0x10b401 part39 = true := by
  rw [InstructionTrace.ordered_eq_layout, part39_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part39_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb401 184 = part39Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
