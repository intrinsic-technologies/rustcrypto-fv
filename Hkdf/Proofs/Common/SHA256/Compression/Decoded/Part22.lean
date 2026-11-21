import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part22 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a72b 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a72d 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a72f 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a732 5 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a739 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a73b 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a73e 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a742 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a745 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a747 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a74a 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a74d 0x45 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a750 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a753 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a756 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a759 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a75c 0x45 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10a75f 0x46 (by simp [RexNoWPrefix]) 1 (.sib 1 (some 15) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10a763 0x41 0xc1 0xb00327c8 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a76a 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a76d 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a770 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a773 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a776 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a778 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a77b 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a77e 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10a780 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a785 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a788 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a78b 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a78e 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a791 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a794 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a797 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a79a 0x41 0xc2 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a79e 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a7a0 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a7a2 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a7a5 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a7a8 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a7ab 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a7af 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a7b2 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a7b5 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a7b9 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a7bc 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a7bf 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a7c2 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a7c6 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a7c9 0 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a7cd 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10a7d0 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a7d4 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a7d7 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a7db 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a7de 0x41 0xc2 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a7e2 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a7e5 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a7e7 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a7ea 0 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a7ee 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a7f1 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a7f4 0x41 0xc1 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part22Bytes : List UInt8 :=
  [0x31,0xca,0x89,0xf9,0xc1,0xc1,0x1a,0x8b,0xac,0x24,0x88,0x0,0x0,0x0,0x1,0xd5,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x15,0x41,0x31,0xc9,0x89,0xf9,0xc1,0xc1,0x7,0x44,0x31,0xc9,0x45,0x89,0xe9,0x45,0x31,0xe1,0x41,0x21,0xf9,0x45,0x31,0xe1,0x41,0x1,0xef,0x45,0x1,0xcf,0x46,0x8d,0xc,0x39,0x41,0x81,0xc1,0xc8,0x27,0x3,0xb0,0x44,0x89,0xf1,0xc1,0xc1,0x1e,0x44,0x89,0xf6,0xc1,0xc6,0x13,0x31,0xce,0x44,0x89,0xf1,0xc1,0xc1,0xa,0x31,0xf1,0x4c,0x8b,0x7c,0x24,0x28,0x45,0x89,0xfa,0x45,0x21,0xc2,0x44,0x89,0xfe,0x44,0x31,0xc6,0x44,0x21,0xf6,0x44,0x31,0xd6,0x41,0x89,0xc2,0x41,0xc1,0xc2,0xf,0x1,0xce,0x89,0xc1,0xc1,0xc1,0xd,0x44,0x1,0xcb,0x41,0x89,0xeb,0x41,0xc1,0xc3,0x19,0x44,0x1,0xce,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xe,0x44,0x31,0xd1,0x45,0x31,0xd9,0x41,0x89,0xea,0x41,0xc1,0xea,0x3,0x45,0x31,0xca,0x1,0x44,0x24,0xc,0x41,0x1,0xc2,0x44,0x89,0x14,0x24,0x41,0x89,0xc1,0x41,0xc1,0xe9,0xa,0x41,0x89,0xda,0x41,0xc1,0xc2,0x1a,0x41,0x31,0xc9,0x89,0xd9,0xc1,0xc1,0x15,0x8b,0x44,0x24,0x64,0x44,0x1,0xc8,0x41,0x89,0xd9,0x41,0xc1,0xc1,0x7]

set_option maxRecDepth 4096 in
theorem part22_bytes [Bindings] : part22.flatMap CheckedInstruction.bytes = part22Bytes  := by
  rfl

def part22Layout : List (BitVec 64 × Nat) :=
  [(0x10a72b, 2), (0x10a72d, 2), (0x10a72f, 3), (0x10a732, 7), (0x10a739, 2), (0x10a73b, 3), (0x10a73e, 4), (0x10a742, 3), (0x10a745, 2), (0x10a747, 3), (0x10a74a, 3), (0x10a74d, 3), (0x10a750, 3), (0x10a753, 3), (0x10a756, 3), (0x10a759, 3), (0x10a75c, 3), (0x10a75f, 4), (0x10a763, 7), (0x10a76a, 3), (0x10a76d, 3), (0x10a770, 3), (0x10a773, 3), (0x10a776, 2), (0x10a778, 3), (0x10a77b, 3), (0x10a77e, 2), (0x10a780, 5), (0x10a785, 3), (0x10a788, 3), (0x10a78b, 3), (0x10a78e, 3), (0x10a791, 3), (0x10a794, 3), (0x10a797, 3), (0x10a79a, 4), (0x10a79e, 2), (0x10a7a0, 2), (0x10a7a2, 3), (0x10a7a5, 3), (0x10a7a8, 3), (0x10a7ab, 4), (0x10a7af, 3), (0x10a7b2, 3), (0x10a7b5, 4), (0x10a7b9, 3), (0x10a7bc, 3), (0x10a7bf, 3), (0x10a7c2, 4), (0x10a7c6, 3), (0x10a7c9, 4), (0x10a7cd, 3), (0x10a7d0, 4), (0x10a7d4, 3), (0x10a7d7, 4), (0x10a7db, 3), (0x10a7de, 4), (0x10a7e2, 3), (0x10a7e5, 2), (0x10a7e7, 3), (0x10a7ea, 4), (0x10a7ee, 3), (0x10a7f1, 3), (0x10a7f4, 4)]

theorem part22_layout [Bindings] : InstructionTrace.layout part22 = part22Layout := by
  rfl

theorem part22_ordered [Bindings] : InstructionTrace.ordered 0x10a72b part22 = true := by
  rw [InstructionTrace.ordered_eq_layout, part22_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part22_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa72b 205 = part22Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
