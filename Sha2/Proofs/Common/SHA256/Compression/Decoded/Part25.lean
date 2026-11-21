import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part25 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r32_r32_effect_step 0x10c8a4 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c8a6 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c8a9 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c8ac 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c8af 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c8b2 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c8b5 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c8b7 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c8ba 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c8bd 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c8bf 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c8c2 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c8c5 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c8c7 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c8ca 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c8cc 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c8ce 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c8d1 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c8d3 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c8d5 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c8d8 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c8da 5 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c8de 0xef rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10c8e0 7 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c8e4 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c8e6 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c8e9 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c8eb 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c8ee 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c8f1 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c8f5 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c8f7 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c8fa 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c8fd 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c8ff 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c902 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c905 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c907 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c90a 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c90d 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c910 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c913 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c915 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10c917 2 (.sib 1 (some 3) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10c91a 0xc2 0x6ca6351 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c920 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c923 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c926 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c929 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c92c 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c92e 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c931 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c934 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c936 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c939 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c93c 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c93f 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c942 0x45 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c945 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c948 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c94a 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c94d 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c950 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c952 0xc1 0xd rfl rfl) (by x86_local)]

def part25Bytes : List UInt8 :=
  [0x21,0xf2,0x45,0x89,0xe3,0x41,0x31,0xf3,0x45,0x21,0xcb,0x41,0x31,0xd3,0x41,0x1,0xcb,0x89,0xea,0xc1,0xc2,0xf,0x41,0x1,0xfe,0x89,0xe9,0xc1,0xc1,0xd,0x41,0x1,0xfb,0x89,0xc7,0xc1,0xc7,0x19,0x31,0xd1,0x89,0xc2,0xc1,0xc2,0xe,0x31,0xfa,0x89,0xc7,0xc1,0xef,0x3,0x31,0xd7,0x1,0x6c,0x24,0x50,0x1,0xef,0x89,0x7c,0x24,0x10,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x89,0xf1,0xc1,0xc1,0x1a,0x8b,0x6c,0x24,0x4,0x1,0xd5,0x44,0x89,0xf2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xf1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xfa,0x44,0x31,0xc2,0x44,0x21,0xf2,0x44,0x31,0xc2,0x1,0xeb,0x1,0xd3,0x8d,0x14,0x19,0x81,0xc2,0x51,0x63,0xca,0x6,0x44,0x89,0xd9,0xc1,0xc1,0x1e,0x44,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0xa,0x31,0xf9,0x44,0x89,0xcf,0x44,0x21,0xe7,0x45,0x89,0xcd,0x45,0x31,0xe5,0x45,0x21,0xdd,0x41,0x31,0xfd,0x89,0xc7,0xc1,0xc7,0xf,0x41,0x1,0xcd,0x89,0xc1,0xc1,0xc1,0xd]

set_option maxRecDepth 4096 in
theorem part25_bytes [Bindings] : part25.flatMap CheckedInstruction.bytes = part25Bytes  := by
  rfl

def part25Layout : List (BitVec 64 × Nat) :=
  [(0x10c8a4, 2), (0x10c8a6, 3), (0x10c8a9, 3), (0x10c8ac, 3), (0x10c8af, 3), (0x10c8b2, 3), (0x10c8b5, 2), (0x10c8b7, 3), (0x10c8ba, 3), (0x10c8bd, 2), (0x10c8bf, 3), (0x10c8c2, 3), (0x10c8c5, 2), (0x10c8c7, 3), (0x10c8ca, 2), (0x10c8cc, 2), (0x10c8ce, 3), (0x10c8d1, 2), (0x10c8d3, 2), (0x10c8d5, 3), (0x10c8d8, 2), (0x10c8da, 4), (0x10c8de, 2), (0x10c8e0, 4), (0x10c8e4, 2), (0x10c8e6, 3), (0x10c8e9, 2), (0x10c8eb, 3), (0x10c8ee, 3), (0x10c8f1, 4), (0x10c8f5, 2), (0x10c8f7, 3), (0x10c8fa, 3), (0x10c8fd, 2), (0x10c8ff, 3), (0x10c902, 3), (0x10c905, 2), (0x10c907, 3), (0x10c90a, 3), (0x10c90d, 3), (0x10c910, 3), (0x10c913, 2), (0x10c915, 2), (0x10c917, 3), (0x10c91a, 6), (0x10c920, 3), (0x10c923, 3), (0x10c926, 3), (0x10c929, 3), (0x10c92c, 2), (0x10c92e, 3), (0x10c931, 3), (0x10c934, 2), (0x10c936, 3), (0x10c939, 3), (0x10c93c, 3), (0x10c93f, 3), (0x10c942, 3), (0x10c945, 3), (0x10c948, 2), (0x10c94a, 3), (0x10c94d, 3), (0x10c950, 2), (0x10c952, 3)]

theorem part25_layout [Bindings] : InstructionTrace.layout part25 = part25Layout := by
  rfl

theorem part25_ordered [Bindings] : InstructionTrace.ordered 0x10c8a4 part25 = true := by
  rw [InstructionTrace.ordered_eq_layout, part25_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part25_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc8a4 177 = part25Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
