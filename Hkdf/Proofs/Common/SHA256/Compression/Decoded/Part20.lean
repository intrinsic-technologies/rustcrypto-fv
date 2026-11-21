import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part20 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a599 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a59c 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a59f 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a5a1 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a5a4 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a5a6 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a5a9 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a5ab 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a5ae 0xc1 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a5b1 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a5b4 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a5b8 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a5bb 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a5be 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a5c1 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a5c4 5 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a5c8 0xe9 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a5ca 1 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a5ce 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a5d0 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a5d3 0xc1 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a5d5 2 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a5d9 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a5db 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a5de 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a5e1 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a5e4 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a5e7 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a5e9 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a5ec 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a5ef 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a5f1 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a5f4 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a5f7 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a5fa 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a5fd 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a5ff 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a601 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a604 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10a607 0x44 (by simp [RexNoWPrefix]) 2 (.sib 0 (some 6) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10a60b 0x41 0xc2 0x983e5152 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a612 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a615 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a618 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a61a 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a61d 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a620 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a622 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a625 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a628 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a62a 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a62c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a62f 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a632 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a634 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a637 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a63a 0x41 0xc3 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a63e 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10a641 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a644 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a647 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a64a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a64d 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a650 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part20Bytes : List UInt8 :=
  [0x41,0x1,0xc4,0x41,0x1,0xc0,0x89,0xe9,0xc1,0xc1,0xf,0x89,0xe8,0xc1,0xc0,0xd,0x31,0xc8,0x44,0x89,0xf1,0xc1,0xc1,0x19,0x45,0x89,0xf2,0x41,0xc1,0xc2,0xe,0x41,0x31,0xca,0x44,0x89,0xf1,0xc1,0xe9,0x3,0x44,0x31,0xd1,0x1,0x6c,0x24,0x24,0x1,0xe9,0x89,0x4c,0x24,0x14,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xc1,0x8b,0x54,0x24,0x34,0x1,0xca,0x44,0x89,0xe0,0xc1,0xc0,0x1a,0x44,0x89,0xe1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xe0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf9,0x44,0x31,0xc9,0x44,0x21,0xe1,0x44,0x31,0xc9,0x1,0xd6,0x1,0xce,0x44,0x89,0xc1,0xc1,0xc1,0x1e,0x44,0x8d,0x14,0x30,0x41,0x81,0xc2,0x52,0x51,0x3e,0x98,0x44,0x89,0xc0,0xc1,0xc0,0x13,0x31,0xc8,0x44,0x89,0xc1,0xc1,0xc1,0xa,0x31,0xc1,0x41,0x89,0xdb,0x41,0x21,0xfb,0x89,0xd8,0x31,0xf8,0x44,0x21,0xc0,0x44,0x31,0xd8,0x1,0xc8,0x45,0x1,0xd5,0x45,0x89,0xf3,0x41,0xc1,0xc3,0xf,0x44,0x1,0xd0,0x48,0x89,0xc6,0x44,0x89,0xf1,0xc1,0xc1,0xd,0x44,0x31,0xd9,0x41,0x89,0xd2,0x41,0xc1,0xc2,0x19]

set_option maxRecDepth 4096 in
theorem part20_bytes [Bindings] : part20.flatMap CheckedInstruction.bytes = part20Bytes  := by
  rfl

def part20Layout : List (BitVec 64 × Nat) :=
  [(0x10a599, 3), (0x10a59c, 3), (0x10a59f, 2), (0x10a5a1, 3), (0x10a5a4, 2), (0x10a5a6, 3), (0x10a5a9, 2), (0x10a5ab, 3), (0x10a5ae, 3), (0x10a5b1, 3), (0x10a5b4, 4), (0x10a5b8, 3), (0x10a5bb, 3), (0x10a5be, 3), (0x10a5c1, 3), (0x10a5c4, 4), (0x10a5c8, 2), (0x10a5ca, 4), (0x10a5ce, 2), (0x10a5d0, 3), (0x10a5d3, 2), (0x10a5d5, 4), (0x10a5d9, 2), (0x10a5db, 3), (0x10a5de, 3), (0x10a5e1, 3), (0x10a5e4, 3), (0x10a5e7, 2), (0x10a5e9, 3), (0x10a5ec, 3), (0x10a5ef, 2), (0x10a5f1, 3), (0x10a5f4, 3), (0x10a5f7, 3), (0x10a5fa, 3), (0x10a5fd, 2), (0x10a5ff, 2), (0x10a601, 3), (0x10a604, 3), (0x10a607, 4), (0x10a60b, 7), (0x10a612, 3), (0x10a615, 3), (0x10a618, 2), (0x10a61a, 3), (0x10a61d, 3), (0x10a620, 2), (0x10a622, 3), (0x10a625, 3), (0x10a628, 2), (0x10a62a, 2), (0x10a62c, 3), (0x10a62f, 3), (0x10a632, 2), (0x10a634, 3), (0x10a637, 3), (0x10a63a, 4), (0x10a63e, 3), (0x10a641, 3), (0x10a644, 3), (0x10a647, 3), (0x10a64a, 3), (0x10a64d, 3), (0x10a650, 4)]

theorem part20_layout [Bindings] : InstructionTrace.layout part20 = part20Layout := by
  rfl

theorem part20_ordered [Bindings] : InstructionTrace.ordered 0x10a599 part20 = true := by
  rw [InstructionTrace.ordered_eq_layout, part20_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part20_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa599 187 = part20Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
