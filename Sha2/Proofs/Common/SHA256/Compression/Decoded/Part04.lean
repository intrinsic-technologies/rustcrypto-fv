import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part04 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b86d 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b870 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b873 0x41 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b876 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b879 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b87b 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b87e 0x41 0xc3 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b882 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b885 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b887 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b88a 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b88d 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b890 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b894 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b897 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b89c 5 (.base 2 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b89f 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b8a1 5 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b8a5 0xca rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b8a7 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b8a9 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b8ac 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b8af 0xca rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10b8b1 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b8b3 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b8b5 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b8b8 0x43 (by simp [RexNoWPrefix]) 2 (.sib 11 (some 10) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b8bc 0xc2 0x923f82a4 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8c2 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b8c5 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8c9 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b8cc 0x41 0xc3 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b8d0 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8d3 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b8d6 0x41 0xc2 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b8da 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8dd 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b8e0 0xfd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8e2 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b8e5 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b8e8 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b8eb 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b8ee 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b8f1 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b8f3 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b8f6 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8f8 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8fb 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b8fe 0x41 0xc2 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b902 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b905 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b907 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b90a 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b90d 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b912 0x41 (by simp [RexNoWPrefix]) 5 (.base 10 (.d8 28)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b916 5) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b918 5 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b91c 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b91f 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b922 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b924 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b927 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x10b92a 0x41 0xd2 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b92d 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part04Bytes : List UInt8 :=
  [0x41,0x31,0xf0,0x45,0x21,0xc8,0x41,0x31,0xe8,0x45,0x1,0xd8,0x1,0xd1,0x41,0x89,0xcb,0x41,0xc1,0xc3,0x1a,0x41,0x1,0xd0,0x89,0xca,0xc1,0xc2,0x15,0x44,0x31,0xda,0x41,0x89,0xcb,0x41,0xc1,0xc3,0x7,0x41,0x31,0xd3,0x48,0x8b,0x54,0x24,0x18,0x8b,0x6a,0x18,0xf,0xcd,0x89,0x6c,0x24,0x28,0x89,0xca,0x21,0xc2,0x41,0x1,0xea,0x41,0x1,0xd2,0x89,0xca,0xf7,0xd2,0x21,0xda,0x41,0x1,0xd2,0x43,0x8d,0x14,0x13,0x81,0xc2,0xa4,0x82,0x3f,0x92,0x45,0x89,0xc2,0x41,0xc1,0xc2,0x1e,0x45,0x89,0xc3,0x41,0xc1,0xc3,0x13,0x45,0x31,0xd3,0x45,0x89,0xc2,0x41,0xc1,0xc2,0xa,0x45,0x31,0xda,0x44,0x89,0xcd,0x21,0xfd,0x45,0x89,0xcb,0x41,0x31,0xfb,0x45,0x21,0xc3,0x41,0x31,0xeb,0x45,0x1,0xd3,0x1,0xd6,0x41,0x1,0xd3,0x89,0xf2,0xc1,0xc2,0x1a,0x41,0x89,0xf2,0x41,0xc1,0xc2,0x15,0x41,0x31,0xd2,0x89,0xf2,0xc1,0xc2,0x7,0x44,0x31,0xd2,0x4c,0x8b,0x54,0x24,0x18,0x41,0x8b,0x6a,0x1c,0xf,0xcd,0x89,0x6c,0x24,0x14,0x41,0x89,0xf2,0x41,0x21,0xca,0x1,0xeb,0x44,0x1,0xd3,0x41,0x89,0xf2,0x41,0xf7,0xd2,0x41,0x21,0xc2]

set_option maxRecDepth 4096 in
theorem part04_bytes [Bindings] : part04.flatMap CheckedInstruction.bytes = part04Bytes  := by
  rfl

def part04Layout : List (BitVec 64 × Nat) :=
  [(0x10b86d, 3), (0x10b870, 3), (0x10b873, 3), (0x10b876, 3), (0x10b879, 2), (0x10b87b, 3), (0x10b87e, 4), (0x10b882, 3), (0x10b885, 2), (0x10b887, 3), (0x10b88a, 3), (0x10b88d, 3), (0x10b890, 4), (0x10b894, 3), (0x10b897, 5), (0x10b89c, 3), (0x10b89f, 2), (0x10b8a1, 4), (0x10b8a5, 2), (0x10b8a7, 2), (0x10b8a9, 3), (0x10b8ac, 3), (0x10b8af, 2), (0x10b8b1, 2), (0x10b8b3, 2), (0x10b8b5, 3), (0x10b8b8, 4), (0x10b8bc, 6), (0x10b8c2, 3), (0x10b8c5, 4), (0x10b8c9, 3), (0x10b8cc, 4), (0x10b8d0, 3), (0x10b8d3, 3), (0x10b8d6, 4), (0x10b8da, 3), (0x10b8dd, 3), (0x10b8e0, 2), (0x10b8e2, 3), (0x10b8e5, 3), (0x10b8e8, 3), (0x10b8eb, 3), (0x10b8ee, 3), (0x10b8f1, 2), (0x10b8f3, 3), (0x10b8f6, 2), (0x10b8f8, 3), (0x10b8fb, 3), (0x10b8fe, 4), (0x10b902, 3), (0x10b905, 2), (0x10b907, 3), (0x10b90a, 3), (0x10b90d, 5), (0x10b912, 4), (0x10b916, 2), (0x10b918, 4), (0x10b91c, 3), (0x10b91f, 3), (0x10b922, 2), (0x10b924, 3), (0x10b927, 3), (0x10b92a, 3), (0x10b92d, 3)]

theorem part04_layout [Bindings] : InstructionTrace.layout part04 = part04Layout := by
  rfl

theorem part04_ordered [Bindings] : InstructionTrace.ordered 0x10b86d part04 = true := by
  rw [InstructionTrace.ordered_eq_layout, part04_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part04_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xb86d 195 = part04Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
