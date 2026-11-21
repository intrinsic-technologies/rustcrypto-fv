import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part36 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b1c8 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b1cb 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b1ce 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b1d1 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b1d4 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b1d7 0x45 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b1da 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b1dd 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b1e0 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b1e4 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b1e7 0x4d 0xf4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b1ea 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b1ed 0x41 0xc0 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b1f1 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b1f3 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b1f6 0x41 0xc6 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b1fa 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b1fd 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b1ff 0xc1 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b202 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b205 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b208 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10b20b 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b20f 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b212 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b217 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b21a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b21f 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10b222 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b22a 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b22d 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b230 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b233 0x41 0xc1 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b237 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b23a 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b23d 0x41 0xc0 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b241 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b246 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b249 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b24b 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b24e 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b251 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b254 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b257 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b25a 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b25d 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b260 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b263 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b266 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b268 0xc1 0xc76c51a3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b26e 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b271 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b274 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b277 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b27b 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b27e 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b281 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b284 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b287 0x45 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b28a 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b28d 0x45 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b290 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b293 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b296 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part36Bytes : List UInt8 :=
  [0x45,0x31,0xc8,0x41,0x89,0xd9,0x45,0x21,0xd9,0x41,0x89,0xde,0x45,0x31,0xde,0x45,0x21,0xfe,0x45,0x31,0xce,0x45,0x89,0xd1,0x41,0xc1,0xc1,0xf,0x45,0x1,0xc6,0x4d,0x89,0xf4,0x45,0x89,0xd0,0x41,0xc1,0xc0,0xd,0x1,0xca,0x41,0x89,0xee,0x41,0xc1,0xc6,0x19,0x41,0x1,0xcc,0x89,0xe9,0xc1,0xc1,0xe,0x45,0x31,0xc8,0x44,0x31,0xf1,0x41,0x89,0xe9,0x41,0xc1,0xe9,0x3,0x41,0x31,0xc9,0x48,0x8b,0x4c,0x24,0x28,0x44,0x1,0xd1,0x48,0x89,0x4c,0x24,0x28,0x45,0x1,0xd1,0x44,0x89,0x8c,0x24,0x80,0x0,0x0,0x0,0x44,0x89,0xd1,0xc1,0xe9,0xa,0x41,0x89,0xd1,0x41,0xc1,0xc1,0x1a,0x44,0x31,0xc1,0x41,0x89,0xd0,0x41,0xc1,0xc0,0x15,0x44,0x8b,0x74,0x24,0x58,0x41,0x1,0xce,0x89,0xd1,0xc1,0xc1,0x7,0x45,0x31,0xc8,0x44,0x31,0xc1,0x41,0x89,0xf0,0x41,0x31,0xc0,0x41,0x21,0xd0,0x41,0x31,0xc0,0x44,0x1,0xf7,0x44,0x1,0xc7,0x1,0xf9,0x81,0xc1,0xa3,0x51,0x6c,0xc7,0x44,0x89,0xe7,0xc1,0xc7,0x1e,0x45,0x89,0xe0,0x41,0xc1,0xc0,0x13,0x41,0x31,0xf8,0x44,0x89,0xe7,0xc1,0xc7,0xa,0x44,0x31,0xc7,0x45,0x89,0xf8,0x41,0x21,0xd8,0x45,0x89,0xf9,0x41,0x31,0xd9,0x45,0x21,0xe1,0x45,0x31,0xc1]

set_option maxRecDepth 4096 in
theorem part36_bytes [Bindings] : part36.flatMap CheckedInstruction.bytes = part36Bytes  := by
  rfl

def part36Layout : List (BitVec 64 × Nat) :=
  [(0x10b1c8, 3), (0x10b1cb, 3), (0x10b1ce, 3), (0x10b1d1, 3), (0x10b1d4, 3), (0x10b1d7, 3), (0x10b1da, 3), (0x10b1dd, 3), (0x10b1e0, 4), (0x10b1e4, 3), (0x10b1e7, 3), (0x10b1ea, 3), (0x10b1ed, 4), (0x10b1f1, 2), (0x10b1f3, 3), (0x10b1f6, 4), (0x10b1fa, 3), (0x10b1fd, 2), (0x10b1ff, 3), (0x10b202, 3), (0x10b205, 3), (0x10b208, 3), (0x10b20b, 4), (0x10b20f, 3), (0x10b212, 5), (0x10b217, 3), (0x10b21a, 5), (0x10b21f, 3), (0x10b222, 8), (0x10b22a, 3), (0x10b22d, 3), (0x10b230, 3), (0x10b233, 4), (0x10b237, 3), (0x10b23a, 3), (0x10b23d, 4), (0x10b241, 5), (0x10b246, 3), (0x10b249, 2), (0x10b24b, 3), (0x10b24e, 3), (0x10b251, 3), (0x10b254, 3), (0x10b257, 3), (0x10b25a, 3), (0x10b25d, 3), (0x10b260, 3), (0x10b263, 3), (0x10b266, 2), (0x10b268, 6), (0x10b26e, 3), (0x10b271, 3), (0x10b274, 3), (0x10b277, 4), (0x10b27b, 3), (0x10b27e, 3), (0x10b281, 3), (0x10b284, 3), (0x10b287, 3), (0x10b28a, 3), (0x10b28d, 3), (0x10b290, 3), (0x10b293, 3), (0x10b296, 3)]

theorem part36_layout [Bindings] : InstructionTrace.layout part36 = part36Layout := by
  rfl

theorem part36_ordered [Bindings] : InstructionTrace.ordered 0x10b1c8 part36 = true := by
  rw [InstructionTrace.ordered_eq_layout, part36_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part36_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb1c8 209 = part36Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
