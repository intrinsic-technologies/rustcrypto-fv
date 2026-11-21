import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part15 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a1ca 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a1cd 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a1d2 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a1d5 0x41 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a1d8 0x45 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a1db 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a1de 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a1e1 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a1e4 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a1ec 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a1ef 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a1f2 0x41 0xc4 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a1f6 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a1f9 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a1fb 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a1fe 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a201 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a203 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a206 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a20a 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a20d 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a210 0x45 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a213 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a216 0x41 0xc7 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a21a 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a21c 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a21f 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10a222 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a225 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a228 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a22b 7 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a22f 0xf8 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a231 0 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a235 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a237 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a23a 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a23c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a241 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a244 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10a246 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a249 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a24c 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a24f 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a252 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a255 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a257 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a25a 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a25d 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a25f 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a262 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a264 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a267 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10a269 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a26c 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a274 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a277 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10a279 0x4d 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a27c 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a27f 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a282 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10a284 0x240ca1cc) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a289 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a28c 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a28f 0xca rfl) (by x86_local)]

def part15Bytes : List UInt8 :=
  [0x41,0x89,0xf7,0x4c,0x8b,0x74,0x24,0x78,0x45,0x21,0xf7,0x41,0x89,0xf5,0x45,0x31,0xf5,0x45,0x21,0xcd,0x45,0x31,0xfd,0x41,0x1,0xd5,0x4c,0x8b,0xb4,0x24,0xd8,0x0,0x0,0x0,0x41,0x1,0xc6,0xc1,0xc1,0x19,0x41,0xc1,0xc4,0xe,0x41,0x1,0xc5,0x89,0xfa,0xc1,0xc2,0xf,0x41,0x31,0xcc,0x89,0xf9,0xc1,0xc1,0xd,0x41,0xc1,0xea,0x3,0x44,0x89,0xc0,0xc1,0xc0,0x19,0x45,0x31,0xe2,0x45,0x89,0xc7,0x41,0xc1,0xc7,0xe,0x31,0xd1,0x41,0x31,0xc7,0x44,0x89,0xc0,0x4c,0x89,0xc6,0xc1,0xe8,0x3,0x44,0x31,0xf8,0x1,0x7c,0x24,0x34,0x1,0xf8,0x89,0x44,0x24,0x8,0x89,0xf8,0xc1,0xe8,0xa,0x31,0xc8,0x48,0x8b,0x4c,0x24,0x48,0x44,0x1,0xd1,0x1,0xc1,0x49,0x89,0xc8,0x44,0x89,0xf0,0xc1,0xc0,0x1a,0x44,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xd9,0x31,0xd9,0x44,0x21,0xf1,0x31,0xd9,0x48,0x89,0xdf,0x48,0x8b,0x94,0x24,0x80,0x0,0x0,0x0,0x44,0x1,0xc2,0x1,0xca,0x4d,0x89,0xef,0x44,0x89,0xf9,0xc1,0xc1,0x1e,0x1,0xd0,0x5,0xcc,0xa1,0xc,0x24,0x44,0x89,0xfa,0xc1,0xc2,0x13,0x31,0xca]

set_option maxRecDepth 4096 in
theorem part15_bytes [Bindings] : part15.flatMap CheckedInstruction.bytes = part15Bytes  := by
  rfl

def part15Layout : List (BitVec 64 × Nat) :=
  [(0x10a1ca, 3), (0x10a1cd, 5), (0x10a1d2, 3), (0x10a1d5, 3), (0x10a1d8, 3), (0x10a1db, 3), (0x10a1de, 3), (0x10a1e1, 3), (0x10a1e4, 8), (0x10a1ec, 3), (0x10a1ef, 3), (0x10a1f2, 4), (0x10a1f6, 3), (0x10a1f9, 2), (0x10a1fb, 3), (0x10a1fe, 3), (0x10a201, 2), (0x10a203, 3), (0x10a206, 4), (0x10a20a, 3), (0x10a20d, 3), (0x10a210, 3), (0x10a213, 3), (0x10a216, 4), (0x10a21a, 2), (0x10a21c, 3), (0x10a21f, 3), (0x10a222, 3), (0x10a225, 3), (0x10a228, 3), (0x10a22b, 4), (0x10a22f, 2), (0x10a231, 4), (0x10a235, 2), (0x10a237, 3), (0x10a23a, 2), (0x10a23c, 5), (0x10a241, 3), (0x10a244, 2), (0x10a246, 3), (0x10a249, 3), (0x10a24c, 3), (0x10a24f, 3), (0x10a252, 3), (0x10a255, 2), (0x10a257, 3), (0x10a25a, 3), (0x10a25d, 2), (0x10a25f, 3), (0x10a262, 2), (0x10a264, 3), (0x10a267, 2), (0x10a269, 3), (0x10a26c, 8), (0x10a274, 3), (0x10a277, 2), (0x10a279, 3), (0x10a27c, 3), (0x10a27f, 3), (0x10a282, 2), (0x10a284, 5), (0x10a289, 3), (0x10a28c, 3), (0x10a28f, 2)]

theorem part15_layout [Bindings] : InstructionTrace.layout part15 = part15Layout := by
  rfl

theorem part15_ordered [Bindings] : InstructionTrace.ordered 0x10a1ca part15 = true := by
  rw [InstructionTrace.ordered_eq_layout, part15_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part15_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa1ca 199 = part15Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
