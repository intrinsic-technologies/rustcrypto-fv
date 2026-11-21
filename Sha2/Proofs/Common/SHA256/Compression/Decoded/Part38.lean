import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part38 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d26d 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d270 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d273 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d276 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d278 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d27b 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d27e 0xf9 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10d280 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d285 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10d288 1 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d28c 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d28f 0xc5 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d291 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d295 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d297 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d299 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d29c 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d29e 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d2a1 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d2a3 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d2a5 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d2a8 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d2aa 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d2ad 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d2af 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d2b1 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d2b3 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d2b5 0xfd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d2b7 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d2ba 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d2bd 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d2bf 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d2c2 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10d2c5 0x44 (by simp [RexNoWPrefix]) 0 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10d2c9 0x41 0xc0 0xd6990624 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d2d0 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d2d3 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d2d6 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d2d8 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d2da 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10d2dd 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10d2e0 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d2e5 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d2e7 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d2ea 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d2ed 0x45 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d2f0 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d2f3 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d2f6 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d2f9 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d2fc 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d2ff 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d302 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d305 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d308 0x45 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d30b 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d30e 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d310 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d313 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d315 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d317 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d31a 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d31c 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d31e 0xef 0x3 rfl rfl) (by x86_local)]

def part38Bytes : List UInt8 :=
  [0xc1,0xc1,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xcf,0x44,0x89,0xd1,0xc1,0xe9,0x3,0x31,0xf9,0x44,0x1,0x74,0x24,0x8,0x44,0x1,0xf1,0x89,0x4c,0x24,0x10,0xc1,0xed,0xa,0x31,0xc5,0x8b,0x7c,0x24,0x24,0x1,0xef,0x89,0xd8,0xc1,0xc0,0x1a,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd9,0x31,0xd1,0x21,0xd9,0x31,0xd1,0x1,0xfe,0x89,0xfd,0x44,0x89,0xef,0xc1,0xc7,0x1e,0x1,0xce,0x44,0x89,0xe9,0xc1,0xc1,0x13,0x44,0x8d,0x4,0x30,0x41,0x81,0xc0,0x24,0x6,0x99,0xd6,0x44,0x89,0xe8,0xc1,0xc0,0xa,0x31,0xf9,0x31,0xc8,0x44,0x89,0xce,0x4c,0x89,0xe1,0x4c,0x89,0x64,0x24,0x38,0x21,0xce,0x45,0x89,0xcc,0x41,0x31,0xcc,0x45,0x21,0xec,0x41,0x31,0xf4,0x41,0x1,0xc4,0x44,0x89,0xd1,0x44,0x89,0xd0,0xc1,0xc0,0xf,0x45,0x1,0xc7,0x44,0x89,0xd6,0xc1,0xc6,0xd,0x45,0x1,0xc4,0x41,0x89,0xea,0x89,0xef,0xc1,0xc7,0x19,0x31,0xc6,0x89,0xe8,0xc1,0xc0,0xe,0x31,0xf8,0x89,0xef,0xc1,0xef,0x3]

set_option maxRecDepth 4096 in
theorem part38_bytes [Bindings] : part38.flatMap CheckedInstruction.bytes = part38Bytes  := by
  rfl

def part38Layout : List (BitVec 64 × Nat) :=
  [(0x10d26d, 3), (0x10d270, 3), (0x10d273, 3), (0x10d276, 2), (0x10d278, 3), (0x10d27b, 3), (0x10d27e, 2), (0x10d280, 5), (0x10d285, 3), (0x10d288, 4), (0x10d28c, 3), (0x10d28f, 2), (0x10d291, 4), (0x10d295, 2), (0x10d297, 2), (0x10d299, 3), (0x10d29c, 2), (0x10d29e, 3), (0x10d2a1, 2), (0x10d2a3, 2), (0x10d2a5, 3), (0x10d2a8, 2), (0x10d2aa, 3), (0x10d2ad, 2), (0x10d2af, 2), (0x10d2b1, 2), (0x10d2b3, 2), (0x10d2b5, 2), (0x10d2b7, 3), (0x10d2ba, 3), (0x10d2bd, 2), (0x10d2bf, 3), (0x10d2c2, 3), (0x10d2c5, 4), (0x10d2c9, 7), (0x10d2d0, 3), (0x10d2d3, 3), (0x10d2d6, 2), (0x10d2d8, 2), (0x10d2da, 3), (0x10d2dd, 3), (0x10d2e0, 5), (0x10d2e5, 2), (0x10d2e7, 3), (0x10d2ea, 3), (0x10d2ed, 3), (0x10d2f0, 3), (0x10d2f3, 3), (0x10d2f6, 3), (0x10d2f9, 3), (0x10d2fc, 3), (0x10d2ff, 3), (0x10d302, 3), (0x10d305, 3), (0x10d308, 3), (0x10d30b, 3), (0x10d30e, 2), (0x10d310, 3), (0x10d313, 2), (0x10d315, 2), (0x10d317, 3), (0x10d31a, 2), (0x10d31c, 2), (0x10d31e, 3)]

theorem part38_layout [Bindings] : InstructionTrace.layout part38 = part38Layout := by
  rfl

theorem part38_ordered [Bindings] : InstructionTrace.ordered 0x10d26d part38 = true := by
  rw [InstructionTrace.ordered_eq_layout, part38_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part38_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd26d 180 = part38Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
