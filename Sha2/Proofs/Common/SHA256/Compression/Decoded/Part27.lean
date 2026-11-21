import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part27 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca0e 0xfa rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10ca10 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ca14 0xea rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10ca16 2 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ca1a 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ca1c 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca1f 0xca rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10ca21 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ca26 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca29 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca2c 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca2f 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca32 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca35 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca37 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca3a 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca3d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ca3f 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ca41 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ca44 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ca47 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ca4a 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ca4d 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca4f 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca52 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ca55 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10ca57 0x27b70a85) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca5c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca5f 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca62 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca64 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca67 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca6a 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca6c 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ca6f 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca72 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ca75 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ca78 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca7b 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ca7d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ca7f 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca82 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca85 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ca88 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca8a 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca8d 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca90 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca92 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca95 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ca98 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ca9b 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ca9e 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10caa0 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10caa3 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10caa6 0xfa rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10caa8 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10caad 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10cab0 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cab4 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cab7 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10caba 0xc2 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10cabc 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cac0 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cac2 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part27Bytes : List UInt8 :=
  [0x31,0xfa,0x1,0x6c,0x24,0x68,0x1,0xea,0x89,0x54,0x24,0x4,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x8b,0x7c,0x24,0xc,0x41,0x1,0xd7,0x44,0x89,0xe1,0xc1,0xc1,0x1a,0x44,0x89,0xe2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xe1,0xc1,0xc1,0x7,0x31,0xd1,0x89,0xf2,0x44,0x31,0xf2,0x44,0x21,0xe2,0x44,0x31,0xf2,0x44,0x1,0xf8,0x1,0xd0,0x44,0x89,0xc2,0xc1,0xc2,0x1e,0x1,0xc8,0x5,0x85,0xa,0xb7,0x27,0x44,0x89,0xc1,0xc1,0xc1,0x13,0x31,0xd1,0x44,0x89,0xc2,0xc1,0xc2,0xa,0x31,0xca,0x44,0x89,0xef,0x44,0x21,0xdf,0x44,0x89,0xe9,0x44,0x31,0xd9,0x44,0x21,0xc1,0x31,0xf9,0x1,0xd1,0x41,0x1,0xc1,0x44,0x89,0xd2,0xc1,0xc2,0xf,0x1,0xc1,0x44,0x89,0xd0,0xc1,0xc0,0xd,0x31,0xd0,0x44,0x89,0xfa,0xc1,0xc2,0x19,0x44,0x89,0xff,0xc1,0xc7,0xe,0x31,0xd7,0x44,0x89,0xfa,0xc1,0xea,0x3,0x31,0xfa,0x44,0x1,0x54,0x24,0x14,0x44,0x1,0xd2,0x89,0x54,0x24,0x40,0x44,0x89,0xd2,0xc1,0xea,0xa,0x31,0xc2,0x8b,0x6c,0x24,0x8,0x1,0xd5,0x44,0x89,0xc8]

set_option maxRecDepth 4096 in
theorem part27_bytes [Bindings] : part27.flatMap CheckedInstruction.bytes = part27Bytes  := by
  rfl

def part27Layout : List (BitVec 64 × Nat) :=
  [(0x10ca0e, 2), (0x10ca10, 4), (0x10ca14, 2), (0x10ca16, 4), (0x10ca1a, 2), (0x10ca1c, 3), (0x10ca1f, 2), (0x10ca21, 5), (0x10ca26, 3), (0x10ca29, 3), (0x10ca2c, 3), (0x10ca2f, 3), (0x10ca32, 3), (0x10ca35, 2), (0x10ca37, 3), (0x10ca3a, 3), (0x10ca3d, 2), (0x10ca3f, 2), (0x10ca41, 3), (0x10ca44, 3), (0x10ca47, 3), (0x10ca4a, 3), (0x10ca4d, 2), (0x10ca4f, 3), (0x10ca52, 3), (0x10ca55, 2), (0x10ca57, 5), (0x10ca5c, 3), (0x10ca5f, 3), (0x10ca62, 2), (0x10ca64, 3), (0x10ca67, 3), (0x10ca6a, 2), (0x10ca6c, 3), (0x10ca6f, 3), (0x10ca72, 3), (0x10ca75, 3), (0x10ca78, 3), (0x10ca7b, 2), (0x10ca7d, 2), (0x10ca7f, 3), (0x10ca82, 3), (0x10ca85, 3), (0x10ca88, 2), (0x10ca8a, 3), (0x10ca8d, 3), (0x10ca90, 2), (0x10ca92, 3), (0x10ca95, 3), (0x10ca98, 3), (0x10ca9b, 3), (0x10ca9e, 2), (0x10caa0, 3), (0x10caa3, 3), (0x10caa6, 2), (0x10caa8, 5), (0x10caad, 3), (0x10cab0, 4), (0x10cab4, 3), (0x10cab7, 3), (0x10caba, 2), (0x10cabc, 4), (0x10cac0, 2), (0x10cac2, 3)]

theorem part27_layout [Bindings] : InstructionTrace.layout part27 = part27Layout := by
  rfl

theorem part27_ordered [Bindings] : InstructionTrace.ordered 0x10ca0e part27 = true := by
  rw [InstructionTrace.ordered_eq_layout, part27_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part27_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xca0e 183 = part27Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
