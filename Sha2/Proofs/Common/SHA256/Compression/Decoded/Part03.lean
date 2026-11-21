import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part03 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b7a2 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b7a7 0x41 (by simp [RexNoWPrefix]) 5 (.base 9 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b7ab 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b7ad 5 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7b1 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b7b4 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b7b7 0xea rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b7b9 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7bc 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x10b7bf 0x41 0xd1 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b7c2 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b7c5 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b7c8 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b7cb 0xc2 0x3956c25b rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7d1 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b7d4 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7d8 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b7db 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b7df 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b7e2 0xfd rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b7e4 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b7e7 0x44 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7ea 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b7ed 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7f0 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b7f3 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b7f6 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b7f9 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b7fc 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b7ff 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b801 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b804 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b806 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b809 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b80c 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b810 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b813 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b815 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b818 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b81b 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b820 0x41 (by simp [RexNoWPrefix]) 5 (.base 11 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b824 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b826 5 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b82a 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b82d 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b830 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b833 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b836 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x10b839 0x41 0xd3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b83c 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b83f 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b842 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b845 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b849 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b84c 0xc2 0x59f111f1 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b852 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b855 0x41 0xc0 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b859 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b85c 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b85f 0x41 0xc3 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b863 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b866 0xfd rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b868 0xf5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b86a 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part03Bytes : List UInt8 :=
  [0x4c,0x8b,0x4c,0x24,0x18,0x41,0x8b,0x69,0x10,0xf,0xcd,0x89,0x6c,0x24,0x24,0x41,0x89,0xd9,0x45,0x21,0xd1,0x1,0xea,0x44,0x1,0xca,0x41,0x89,0xd9,0x41,0xf7,0xd1,0x45,0x21,0xc1,0x44,0x1,0xca,0x44,0x1,0xda,0x81,0xc2,0x5b,0xc2,0x56,0x39,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xfb,0x41,0xc1,0xc3,0x13,0x45,0x31,0xcb,0x89,0xfd,0xc1,0xc5,0xa,0x44,0x31,0xdd,0x41,0x89,0xf3,0x41,0x21,0xcb,0x41,0x89,0xf1,0x41,0x31,0xc9,0x41,0x21,0xf9,0x45,0x31,0xd9,0x41,0x1,0xe9,0x1,0xd0,0x41,0x1,0xd1,0x89,0xc2,0xc1,0xc2,0x1a,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x15,0x41,0x31,0xd3,0x89,0xc2,0xc1,0xc2,0x7,0x44,0x31,0xda,0x4c,0x8b,0x5c,0x24,0x18,0x41,0x8b,0x6b,0x14,0xf,0xcd,0x89,0x6c,0x24,0x40,0x41,0x89,0xc3,0x41,0x21,0xdb,0x41,0x1,0xe8,0x45,0x1,0xd8,0x41,0x89,0xc3,0x41,0xf7,0xd3,0x45,0x21,0xd3,0x45,0x1,0xd8,0x45,0x89,0xcb,0x41,0xc1,0xc3,0x1e,0x44,0x1,0xc2,0x81,0xc2,0xf1,0x11,0xf1,0x59,0x45,0x89,0xc8,0x41,0xc1,0xc0,0x13,0x45,0x31,0xd8,0x45,0x89,0xcb,0x41,0xc1,0xc3,0xa,0x45,0x31,0xc3,0x89,0xfd,0x21,0xf5,0x41,0x89,0xf8]

set_option maxRecDepth 4096 in
theorem part03_bytes [Bindings] : part03.flatMap CheckedInstruction.bytes = part03Bytes  := by
  rfl

def part03Layout : List (BitVec 64 × Nat) :=
  [(0x10b7a2, 5), (0x10b7a7, 4), (0x10b7ab, 2), (0x10b7ad, 4), (0x10b7b1, 3), (0x10b7b4, 3), (0x10b7b7, 2), (0x10b7b9, 3), (0x10b7bc, 3), (0x10b7bf, 3), (0x10b7c2, 3), (0x10b7c5, 3), (0x10b7c8, 3), (0x10b7cb, 6), (0x10b7d1, 3), (0x10b7d4, 4), (0x10b7d8, 3), (0x10b7db, 4), (0x10b7df, 3), (0x10b7e2, 2), (0x10b7e4, 3), (0x10b7e7, 3), (0x10b7ea, 3), (0x10b7ed, 3), (0x10b7f0, 3), (0x10b7f3, 3), (0x10b7f6, 3), (0x10b7f9, 3), (0x10b7fc, 3), (0x10b7ff, 2), (0x10b801, 3), (0x10b804, 2), (0x10b806, 3), (0x10b809, 3), (0x10b80c, 4), (0x10b810, 3), (0x10b813, 2), (0x10b815, 3), (0x10b818, 3), (0x10b81b, 5), (0x10b820, 4), (0x10b824, 2), (0x10b826, 4), (0x10b82a, 3), (0x10b82d, 3), (0x10b830, 3), (0x10b833, 3), (0x10b836, 3), (0x10b839, 3), (0x10b83c, 3), (0x10b83f, 3), (0x10b842, 3), (0x10b845, 4), (0x10b849, 3), (0x10b84c, 6), (0x10b852, 3), (0x10b855, 4), (0x10b859, 3), (0x10b85c, 3), (0x10b85f, 4), (0x10b863, 3), (0x10b866, 2), (0x10b868, 2), (0x10b86a, 3)]

theorem part03_layout [Bindings] : InstructionTrace.layout part03 = part03Layout := by
  rfl

theorem part03_ordered [Bindings] : InstructionTrace.ordered 0x10b7a2 part03 = true := by
  rw [InstructionTrace.ordered_eq_layout, part03_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part03_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xb7a2 203 = part03Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
