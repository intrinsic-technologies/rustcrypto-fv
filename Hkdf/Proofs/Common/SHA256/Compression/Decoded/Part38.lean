import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part38 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b34d 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b350 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b353 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b356 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b358 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b35b 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b35e 0xf9 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10b360 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b365 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b368 1 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b36c 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b36f 0xc5 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b371 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b375 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b377 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b379 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b37c 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b37e 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b381 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b383 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b385 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b388 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b38a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b38d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b38f 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b391 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b393 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b395 0xfd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b397 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b39a 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b39d 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b39f 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b3a2 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b3a5 0x44 (by simp [RexNoWPrefix]) 0 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10b3a9 0x41 0xc0 0xd6990624 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b3b0 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b3b3 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b3b6 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b3b8 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b3ba 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b3bd 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b3c0 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b3c5 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b3c7 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b3ca 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b3cd 0x45 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b3d0 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b3d3 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b3d6 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b3d9 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b3dc 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b3df 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b3e2 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b3e5 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b3e8 0x45 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b3eb 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b3ee 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b3f0 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b3f3 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b3f5 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b3f7 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b3fa 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b3fc 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b3fe 0xef 0x3 rfl rfl) (by x86_local)]

def part38Bytes : List UInt8 :=
  [0xc1,0xc1,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xcf,0x44,0x89,0xd1,0xc1,0xe9,0x3,0x31,0xf9,0x44,0x1,0x74,0x24,0x8,0x44,0x1,0xf1,0x89,0x4c,0x24,0x10,0xc1,0xed,0xa,0x31,0xc5,0x8b,0x7c,0x24,0x24,0x1,0xef,0x89,0xd8,0xc1,0xc0,0x1a,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd9,0x31,0xd1,0x21,0xd9,0x31,0xd1,0x1,0xfe,0x89,0xfd,0x44,0x89,0xef,0xc1,0xc7,0x1e,0x1,0xce,0x44,0x89,0xe9,0xc1,0xc1,0x13,0x44,0x8d,0x4,0x30,0x41,0x81,0xc0,0x24,0x6,0x99,0xd6,0x44,0x89,0xe8,0xc1,0xc0,0xa,0x31,0xf9,0x31,0xc8,0x44,0x89,0xce,0x4c,0x89,0xe1,0x4c,0x89,0x64,0x24,0x38,0x21,0xce,0x45,0x89,0xcc,0x41,0x31,0xcc,0x45,0x21,0xec,0x41,0x31,0xf4,0x41,0x1,0xc4,0x44,0x89,0xd1,0x44,0x89,0xd0,0xc1,0xc0,0xf,0x45,0x1,0xc7,0x44,0x89,0xd6,0xc1,0xc6,0xd,0x45,0x1,0xc4,0x41,0x89,0xea,0x89,0xef,0xc1,0xc7,0x19,0x31,0xc6,0x89,0xe8,0xc1,0xc0,0xe,0x31,0xf8,0x89,0xef,0xc1,0xef,0x3]

set_option maxRecDepth 4096 in
theorem part38_bytes [Bindings] : part38.flatMap CheckedInstruction.bytes = part38Bytes  := by
  rfl

def part38Layout : List (BitVec 64 × Nat) :=
  [(0x10b34d, 3), (0x10b350, 3), (0x10b353, 3), (0x10b356, 2), (0x10b358, 3), (0x10b35b, 3), (0x10b35e, 2), (0x10b360, 5), (0x10b365, 3), (0x10b368, 4), (0x10b36c, 3), (0x10b36f, 2), (0x10b371, 4), (0x10b375, 2), (0x10b377, 2), (0x10b379, 3), (0x10b37c, 2), (0x10b37e, 3), (0x10b381, 2), (0x10b383, 2), (0x10b385, 3), (0x10b388, 2), (0x10b38a, 3), (0x10b38d, 2), (0x10b38f, 2), (0x10b391, 2), (0x10b393, 2), (0x10b395, 2), (0x10b397, 3), (0x10b39a, 3), (0x10b39d, 2), (0x10b39f, 3), (0x10b3a2, 3), (0x10b3a5, 4), (0x10b3a9, 7), (0x10b3b0, 3), (0x10b3b3, 3), (0x10b3b6, 2), (0x10b3b8, 2), (0x10b3ba, 3), (0x10b3bd, 3), (0x10b3c0, 5), (0x10b3c5, 2), (0x10b3c7, 3), (0x10b3ca, 3), (0x10b3cd, 3), (0x10b3d0, 3), (0x10b3d3, 3), (0x10b3d6, 3), (0x10b3d9, 3), (0x10b3dc, 3), (0x10b3df, 3), (0x10b3e2, 3), (0x10b3e5, 3), (0x10b3e8, 3), (0x10b3eb, 3), (0x10b3ee, 2), (0x10b3f0, 3), (0x10b3f3, 2), (0x10b3f5, 2), (0x10b3f7, 3), (0x10b3fa, 2), (0x10b3fc, 2), (0x10b3fe, 3)]

theorem part38_layout [Bindings] : InstructionTrace.layout part38 = part38Layout := by
  rfl

theorem part38_ordered [Bindings] : InstructionTrace.ordered 0x10b34d part38 = true := by
  rw [InstructionTrace.ordered_eq_layout, part38_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part38_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb34d 180 = part38Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
