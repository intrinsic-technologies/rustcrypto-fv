import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part40 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b4b9 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b4bb 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b4bd 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b4c0 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b4c5 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b4c8 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b4ca 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b4cd 0xfe rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b4cf 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b4d1 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b4d4 0xde rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b4d6 0xd6 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b4d8 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b4dd 0xde rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b4df 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b4e2 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b4e5 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10b4e8 0x106aa070) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b4ed 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b4f0 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b4f3 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b4f6 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b4f9 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b4fb 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b4fe 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b501 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b503 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b506 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b509 0x45 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b50c 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b50f 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b512 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b515 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b518 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b51b 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b51e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b520 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b523 0xce rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b525 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b528 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b52a 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b52d 0xc0 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b530 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b533 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b536 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b538 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b53b 0xe8 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b53e 0xf8 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b540 1 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b544 0xc8 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b546 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b54b 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b54d 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b550 0xf0 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b552 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b557 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b559 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b55c 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b55f 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b562 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b565 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b567 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b56a 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b56d 0xf0 rfl) (by x86_local)]

def part40Bytes : List UInt8 :=
  [0x31,0xf0,0x89,0xee,0xc1,0xc6,0x15,0x44,0x8b,0x54,0x24,0x40,0x41,0x1,0xc2,0x89,0xe8,0xc1,0xc0,0x7,0x31,0xfe,0x31,0xf0,0x44,0x89,0xfe,0x31,0xde,0x21,0xd6,0x48,0x89,0x6c,0x24,0x38,0x31,0xde,0x45,0x1,0xd3,0x41,0x1,0xf3,0x44,0x1,0xd8,0x5,0x70,0xa0,0x6a,0x10,0x44,0x89,0xf6,0xc1,0xc6,0x1e,0x44,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xf6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xe7,0x44,0x21,0xef,0x45,0x89,0xe0,0x45,0x31,0xe8,0x45,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xf0,0x41,0x1,0xc1,0x41,0x1,0xc0,0x89,0xc8,0xc1,0xc0,0xf,0x89,0xce,0xc1,0xc6,0xd,0x31,0xc6,0x44,0x89,0xd0,0xc1,0xc0,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xc7,0x44,0x89,0xd0,0xc1,0xe8,0x3,0x31,0xf8,0x1,0x4c,0x24,0x14,0x1,0xc8,0x48,0x89,0x44,0x24,0x40,0x89,0xc8,0xc1,0xe8,0xa,0x31,0xf0,0x48,0x8b,0x4c,0x24,0x28,0x1,0xc1,0x44,0x89,0xc8,0xc1,0xc0,0x1a,0x44,0x89,0xce,0xc1,0xc6,0x15,0x31,0xc6,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xf0]

set_option maxRecDepth 4096 in
theorem part40_bytes [Bindings] : part40.flatMap CheckedInstruction.bytes = part40Bytes  := by
  rfl

def part40Layout : List (BitVec 64 × Nat) :=
  [(0x10b4b9, 2), (0x10b4bb, 2), (0x10b4bd, 3), (0x10b4c0, 5), (0x10b4c5, 3), (0x10b4c8, 2), (0x10b4ca, 3), (0x10b4cd, 2), (0x10b4cf, 2), (0x10b4d1, 3), (0x10b4d4, 2), (0x10b4d6, 2), (0x10b4d8, 5), (0x10b4dd, 2), (0x10b4df, 3), (0x10b4e2, 3), (0x10b4e5, 3), (0x10b4e8, 5), (0x10b4ed, 3), (0x10b4f0, 3), (0x10b4f3, 3), (0x10b4f6, 3), (0x10b4f9, 2), (0x10b4fb, 3), (0x10b4fe, 3), (0x10b501, 2), (0x10b503, 3), (0x10b506, 3), (0x10b509, 3), (0x10b50c, 3), (0x10b50f, 3), (0x10b512, 3), (0x10b515, 3), (0x10b518, 3), (0x10b51b, 3), (0x10b51e, 2), (0x10b520, 3), (0x10b523, 2), (0x10b525, 3), (0x10b528, 2), (0x10b52a, 3), (0x10b52d, 3), (0x10b530, 3), (0x10b533, 3), (0x10b536, 2), (0x10b538, 3), (0x10b53b, 3), (0x10b53e, 2), (0x10b540, 4), (0x10b544, 2), (0x10b546, 5), (0x10b54b, 2), (0x10b54d, 3), (0x10b550, 2), (0x10b552, 5), (0x10b557, 2), (0x10b559, 3), (0x10b55c, 3), (0x10b55f, 3), (0x10b562, 3), (0x10b565, 2), (0x10b567, 3), (0x10b56a, 3), (0x10b56d, 2)]

theorem part40_layout [Bindings] : InstructionTrace.layout part40 = part40Layout := by
  rfl

theorem part40_ordered [Bindings] : InstructionTrace.ordered 0x10b4b9 part40 = true := by
  rw [InstructionTrace.ordered_eq_layout, part40_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part40_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb4b9 182 = part40Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
