import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part37 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b299 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b29c 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b29f 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b2a2 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b2a4 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b2a7 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b2a9 0xc7 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b2ac 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b2ae 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b2b1 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b2b4 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b2b7 0x41 0xc0 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b2bb 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b2be 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b2c1 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b2c4 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b2c7 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b2cb 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b2cd 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b2d1 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b2d3 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b2d6 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b2d8 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b2db 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b2de 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b2e1 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b2e4 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b2e7 0xc7 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b2ea 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b2ec 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b2ef 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b2f2 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b2f4 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b2f6 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b2f8 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b2fb 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b2fd 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b300 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b302 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b305 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b308 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10b30a 0xd192e819) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b30f 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b312 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b315 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b317 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b31a 0xc7 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b31d 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b31f 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b322 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b325 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b328 0x45 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b32b 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b32e 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b331 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b334 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b336 0x44 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b339 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b33c 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b33f 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b342 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b345 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b348 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b34a 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part37Bytes : List UInt8 :=
  [0x41,0x1,0xf9,0x41,0x1,0xcb,0x41,0x1,0xc9,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xef,0xc1,0xc7,0xd,0x31,0xcf,0x44,0x89,0xf1,0xc1,0xc1,0x19,0x45,0x89,0xf0,0x41,0xc1,0xc0,0xe,0x41,0x31,0xc8,0x44,0x89,0xf1,0xc1,0xe9,0x3,0x44,0x31,0xc1,0x1,0x6c,0x24,0xc,0x1,0xe9,0x89,0x4c,0x24,0x58,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xf9,0x45,0x89,0xea,0x41,0x1,0xca,0x44,0x89,0xd9,0xc1,0xc1,0x1a,0x44,0x89,0xdf,0xc1,0xc7,0x15,0x31,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf9,0x89,0xd7,0x31,0xf7,0x44,0x21,0xdf,0x31,0xf7,0x44,0x1,0xd0,0x1,0xf8,0x44,0x89,0xcf,0xc1,0xc7,0x1e,0x1,0xc8,0x5,0x19,0xe8,0x92,0xd1,0x44,0x89,0xc9,0xc1,0xc1,0x13,0x31,0xf9,0x44,0x89,0xcf,0xc1,0xc7,0xa,0x31,0xcf,0x44,0x89,0xe1,0x44,0x21,0xf9,0x45,0x89,0xe5,0x45,0x31,0xfd,0x45,0x21,0xcd,0x41,0x31,0xcd,0x41,0x1,0xfd,0x1,0xc3,0x44,0x89,0xf5,0x44,0x89,0xf1,0xc1,0xc1,0xf,0x41,0x1,0xc5,0x44,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xd1]

set_option maxRecDepth 4096 in
theorem part37_bytes [Bindings] : part37.flatMap CheckedInstruction.bytes = part37Bytes  := by
  rfl

def part37Layout : List (BitVec 64 × Nat) :=
  [(0x10b299, 3), (0x10b29c, 3), (0x10b29f, 3), (0x10b2a2, 2), (0x10b2a4, 3), (0x10b2a7, 2), (0x10b2a9, 3), (0x10b2ac, 2), (0x10b2ae, 3), (0x10b2b1, 3), (0x10b2b4, 3), (0x10b2b7, 4), (0x10b2bb, 3), (0x10b2be, 3), (0x10b2c1, 3), (0x10b2c4, 3), (0x10b2c7, 4), (0x10b2cb, 2), (0x10b2cd, 4), (0x10b2d1, 2), (0x10b2d3, 3), (0x10b2d6, 2), (0x10b2d8, 3), (0x10b2db, 3), (0x10b2de, 3), (0x10b2e1, 3), (0x10b2e4, 3), (0x10b2e7, 3), (0x10b2ea, 2), (0x10b2ec, 3), (0x10b2ef, 3), (0x10b2f2, 2), (0x10b2f4, 2), (0x10b2f6, 2), (0x10b2f8, 3), (0x10b2fb, 2), (0x10b2fd, 3), (0x10b300, 2), (0x10b302, 3), (0x10b305, 3), (0x10b308, 2), (0x10b30a, 5), (0x10b30f, 3), (0x10b312, 3), (0x10b315, 2), (0x10b317, 3), (0x10b31a, 3), (0x10b31d, 2), (0x10b31f, 3), (0x10b322, 3), (0x10b325, 3), (0x10b328, 3), (0x10b32b, 3), (0x10b32e, 3), (0x10b331, 3), (0x10b334, 2), (0x10b336, 3), (0x10b339, 3), (0x10b33c, 3), (0x10b33f, 3), (0x10b342, 3), (0x10b345, 3), (0x10b348, 2), (0x10b34a, 3)]

theorem part37_layout [Bindings] : InstructionTrace.layout part37 = part37Layout := by
  rfl

theorem part37_ordered [Bindings] : InstructionTrace.ordered 0x10b299 part37 = true := by
  rw [InstructionTrace.ordered_eq_layout, part37_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part37_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb299 180 = part37Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
