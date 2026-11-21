import P256.Proofs.Program.Code
import P256.Proofs.SHA256.Compression.Layout
import P256.Proofs.Common.SHA256.Compression.Bswap32
import P256.Proofs.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace P256.Proofs.SHA256.Compression.Decoded

open P256.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def part24 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116c9a 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116c9d 0xc1 0xc6e00bf3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116ca3 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116ca6 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116ca9 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116cac 0x45 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116caf 0x41 0xc2 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116cb3 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116cb6 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116cb8 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116cbb 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116cbe 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116cc1 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116cc4 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116cc7 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116cca 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116ccd 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116ccf 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x116cd2 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116cd5 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116cd7 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116cda 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116cdc 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116cde 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116ce1 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116ce4 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116ce8 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116ceb 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116ced 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116cf0 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x116cf3 0 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116cf7 0xc2 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x116cf9 2 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x116cfd 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x116cff 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d02 0xca rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x116d04 0 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116d08 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x116d0a 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d0d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d10 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d13 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d16 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d19 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d1b 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d1e 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d21 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d23 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d26 0xda rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x116d28 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d2b 0xda rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116d2d 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d2f 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x116d32 0x41 0xc2 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116d36 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d38 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d3b 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x116d3e 0xcf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x116d40 0xc7 0xd5a79147 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d46 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x116d49 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x116d4c 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x116d4f 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x116d51 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part24Bytes : List UInt8 :=
  [0x44,0x1,0xe9,0x81,0xc1,0xf3,0xb,0xe0,0xc6,0x44,0x89,0xe2,0xc1,0xc2,0x13,0x44,0x31,0xca,0x45,0x89,0xe2,0x41,0xc1,0xc2,0xa,0x41,0x31,0xd2,0x89,0xf2,0x44,0x21,0xf2,0x41,0x89,0xf1,0x45,0x31,0xf1,0x45,0x21,0xe1,0x41,0x31,0xd1,0x45,0x1,0xd1,0x41,0x1,0xcf,0x89,0xc2,0xc1,0xc2,0xf,0x41,0x1,0xc9,0x89,0xc1,0xc1,0xc1,0xd,0x31,0xd1,0x89,0xea,0xc1,0xc2,0x19,0x41,0x89,0xea,0x41,0xc1,0xc2,0xe,0x41,0x31,0xd2,0x89,0xea,0xc1,0xea,0x3,0x44,0x31,0xd2,0x1,0x44,0x24,0x38,0x1,0xc2,0x89,0x54,0x24,0x58,0x89,0xc2,0xc1,0xea,0xa,0x31,0xca,0x8b,0x44,0x24,0x24,0x1,0xd0,0x4d,0x89,0xfa,0x44,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x89,0xd2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xc2,0x31,0xda,0x44,0x21,0xd2,0x31,0xda,0x1,0xc7,0x45,0x89,0xca,0x41,0xc1,0xc2,0x1e,0x1,0xd7,0x44,0x89,0xca,0xc1,0xc2,0x13,0x1,0xcf,0x81,0xc7,0x47,0x91,0xa7,0xd5,0x44,0x89,0xc9,0xc1,0xc1,0xa,0x44,0x31,0xd2,0x31,0xd1,0x44,0x89,0xe2]

set_option maxRecDepth 4096 in
theorem part24_bytes [Bindings] : part24.flatMap CheckedInstruction.bytes = part24Bytes  := by
  rfl

def part24Layout : List (BitVec 64 × Nat) :=
  [(0x116c9a, 3), (0x116c9d, 6), (0x116ca3, 3), (0x116ca6, 3), (0x116ca9, 3), (0x116cac, 3), (0x116caf, 4), (0x116cb3, 3), (0x116cb6, 2), (0x116cb8, 3), (0x116cbb, 3), (0x116cbe, 3), (0x116cc1, 3), (0x116cc4, 3), (0x116cc7, 3), (0x116cca, 3), (0x116ccd, 2), (0x116ccf, 3), (0x116cd2, 3), (0x116cd5, 2), (0x116cd7, 3), (0x116cda, 2), (0x116cdc, 2), (0x116cde, 3), (0x116ce1, 3), (0x116ce4, 4), (0x116ce8, 3), (0x116ceb, 2), (0x116ced, 3), (0x116cf0, 3), (0x116cf3, 4), (0x116cf7, 2), (0x116cf9, 4), (0x116cfd, 2), (0x116cff, 3), (0x116d02, 2), (0x116d04, 4), (0x116d08, 2), (0x116d0a, 3), (0x116d0d, 3), (0x116d10, 3), (0x116d13, 3), (0x116d16, 3), (0x116d19, 2), (0x116d1b, 3), (0x116d1e, 3), (0x116d21, 2), (0x116d23, 3), (0x116d26, 2), (0x116d28, 3), (0x116d2b, 2), (0x116d2d, 2), (0x116d2f, 3), (0x116d32, 4), (0x116d36, 2), (0x116d38, 3), (0x116d3b, 3), (0x116d3e, 2), (0x116d40, 6), (0x116d46, 3), (0x116d49, 3), (0x116d4c, 3), (0x116d4f, 2), (0x116d51, 3)]

theorem part24_layout [Bindings] : InstructionTrace.layout part24 = part24Layout := by
  rfl

set_option maxRecDepth 4096 in
theorem part24_source : P256.Spec.Program.Extracted.textBytes.toListFrom 0x16c9a 186 = part24Bytes := by
  rfl

end P256.Proofs.SHA256.Compression.Decoded
