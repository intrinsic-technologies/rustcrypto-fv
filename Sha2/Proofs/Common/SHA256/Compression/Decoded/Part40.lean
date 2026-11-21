import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part40 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d3d9 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d3db 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d3dd 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10d3e0 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d3e5 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d3e8 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d3ea 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d3ed 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d3ef 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d3f1 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d3f4 0xde rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d3f6 0xd6 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10d3f8 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d3fd 0xde rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d3ff 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d402 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d405 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10d408 0x106aa070) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d40d 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d410 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d413 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d416 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d419 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d41b 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d41e 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d421 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d423 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d426 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d429 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d42c 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d42f 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d432 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d435 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d438 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d43b 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d43e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d440 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d443 0xce rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d445 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d448 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d44a 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d44d 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d450 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d453 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d456 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d458 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d45b 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d45e 0xf8 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10d460 1 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d464 0xc8 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10d466 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d46b 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d46d 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d470 0xf0 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10d472 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d477 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d479 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d47c 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d47f 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d482 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d485 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d487 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d48a 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d48d 0xf0 rfl) (by x86_local)]

def part40Bytes : List UInt8 :=
  [0x31,0xf0,0x89,0xee,0xc1,0xc6,0x15,0x44,0x8b,0x54,0x24,0x40,0x41,0x1,0xc2,0x89,0xe8,0xc1,0xc0,0x7,0x31,0xfe,0x31,0xf0,0x44,0x89,0xfe,0x31,0xde,0x21,0xd6,0x48,0x89,0x6c,0x24,0x38,0x31,0xde,0x45,0x1,0xd3,0x41,0x1,0xf3,0x44,0x1,0xd8,0x5,0x70,0xa0,0x6a,0x10,0x44,0x89,0xf6,0xc1,0xc6,0x1e,0x44,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xf6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xe7,0x44,0x21,0xef,0x45,0x89,0xe0,0x45,0x31,0xe8,0x45,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xf0,0x41,0x1,0xc1,0x41,0x1,0xc0,0x89,0xc8,0xc1,0xc0,0xf,0x89,0xce,0xc1,0xc6,0xd,0x31,0xc6,0x44,0x89,0xd0,0xc1,0xc0,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xc7,0x44,0x89,0xd0,0xc1,0xe8,0x3,0x31,0xf8,0x1,0x4c,0x24,0x14,0x1,0xc8,0x48,0x89,0x44,0x24,0x40,0x89,0xc8,0xc1,0xe8,0xa,0x31,0xf0,0x48,0x8b,0x4c,0x24,0x28,0x1,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x44,0x89,0xce,0xc1,0xc6,0x15,0x31,0xc6,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xf0]

set_option maxRecDepth 4096 in
theorem part40_bytes [Bindings] : part40.flatMap CheckedInstruction.bytes = part40Bytes  := by
  rfl

def part40Layout : List (BitVec 64 × Nat) :=
  [(0x10d3d9, 2), (0x10d3db, 2), (0x10d3dd, 3), (0x10d3e0, 5), (0x10d3e5, 3), (0x10d3e8, 2), (0x10d3ea, 3), (0x10d3ed, 2), (0x10d3ef, 2), (0x10d3f1, 3), (0x10d3f4, 2), (0x10d3f6, 2), (0x10d3f8, 5), (0x10d3fd, 2), (0x10d3ff, 3), (0x10d402, 3), (0x10d405, 3), (0x10d408, 5), (0x10d40d, 3), (0x10d410, 3), (0x10d413, 3), (0x10d416, 3), (0x10d419, 2), (0x10d41b, 3), (0x10d41e, 3), (0x10d421, 2), (0x10d423, 3), (0x10d426, 3), (0x10d429, 3), (0x10d42c, 3), (0x10d42f, 3), (0x10d432, 3), (0x10d435, 3), (0x10d438, 3), (0x10d43b, 3), (0x10d43e, 2), (0x10d440, 3), (0x10d443, 2), (0x10d445, 3), (0x10d448, 2), (0x10d44a, 3), (0x10d44d, 3), (0x10d450, 3), (0x10d453, 3), (0x10d456, 2), (0x10d458, 3), (0x10d45b, 3), (0x10d45e, 2), (0x10d460, 4), (0x10d464, 2), (0x10d466, 5), (0x10d46b, 2), (0x10d46d, 3), (0x10d470, 2), (0x10d472, 5), (0x10d477, 2), (0x10d479, 3), (0x10d47c, 3), (0x10d47f, 3), (0x10d482, 3), (0x10d485, 2), (0x10d487, 3), (0x10d48a, 3), (0x10d48d, 2)]

theorem part40_layout [Bindings] : InstructionTrace.layout part40 = part40Layout := by
  rfl

theorem part40_ordered [Bindings] : InstructionTrace.ordered 0x10d3d9 part40 = true := by
  rw [InstructionTrace.ordered_eq_layout, part40_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part40_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd3d9 182 = part40Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
