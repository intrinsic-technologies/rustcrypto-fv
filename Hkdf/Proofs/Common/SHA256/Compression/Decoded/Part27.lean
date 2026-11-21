import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part27 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aaee 0xfa rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10aaf0 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10aaf4 0xea rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10aaf6 2 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aafa 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10aafc 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aaff 0xca rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10ab01 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ab06 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab09 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab0c 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab0f 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab12 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab15 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab17 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab1a 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab1d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ab1f 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ab21 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ab24 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ab27 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ab2a 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ab2d 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab2f 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab32 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ab35 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10ab37 0x27b70a85) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab3c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab3f 0xc1 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab42 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab44 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab47 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab4a 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab4c 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ab4f 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab52 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ab55 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ab58 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab5b 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ab5d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ab5f 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab62 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab65 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ab68 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab6a 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab6d 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab70 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab72 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab75 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab78 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ab7b 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab7e 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab80 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ab83 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab86 0xfa rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10ab88 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ab8d 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10ab90 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ab94 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ab97 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ab9a 0xc2 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10ab9c 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10aba0 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aba2 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part27Bytes : List UInt8 :=
  [0x31,0xfa,0x1,0x6c,0x24,0x68,0x1,0xea,0x89,0x54,0x24,0x4,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x8b,0x7c,0x24,0xc,0x41,0x1,0xd7,0x44,0x89,0xe1,0xc1,0xc1,0x1a,0x44,0x89,0xe2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xe1,0xc1,0xc1,0x7,0x31,0xd1,0x89,0xf2,0x44,0x31,0xf2,0x44,0x21,0xe2,0x44,0x31,0xf2,0x44,0x1,0xf8,0x1,0xd0,0x44,0x89,0xc2,0xc1,0xc2,0x1e,0x1,0xc8,0x5,0x85,0xa,0xb7,0x27,0x44,0x89,0xc1,0xc1,0xc1,0x13,0x31,0xd1,0x44,0x89,0xc2,0xc1,0xc2,0xa,0x31,0xca,0x44,0x89,0xef,0x44,0x21,0xdf,0x44,0x89,0xe9,0x44,0x31,0xd9,0x44,0x21,0xc1,0x31,0xf9,0x1,0xd1,0x41,0x1,0xc1,0x44,0x89,0xd2,0xc1,0xc2,0xf,0x1,0xc1,0x44,0x89,0xd0,0xc1,0xc0,0xd,0x31,0xd0,0x44,0x89,0xfa,0xc1,0xc2,0x19,0x44,0x89,0xff,0xc1,0xc7,0xe,0x31,0xd7,0x44,0x89,0xfa,0xc1,0xea,0x3,0x31,0xfa,0x44,0x1,0x54,0x24,0x14,0x44,0x1,0xd2,0x89,0x54,0x24,0x40,0x44,0x89,0xd2,0xc1,0xea,0xa,0x31,0xc2,0x8b,0x6c,0x24,0x8,0x1,0xd5,0x44,0x89,0xc8]

set_option maxRecDepth 4096 in
theorem part27_bytes [Bindings] : part27.flatMap CheckedInstruction.bytes = part27Bytes  := by
  rfl

def part27Layout : List (BitVec 64 × Nat) :=
  [(0x10aaee, 2), (0x10aaf0, 4), (0x10aaf4, 2), (0x10aaf6, 4), (0x10aafa, 2), (0x10aafc, 3), (0x10aaff, 2), (0x10ab01, 5), (0x10ab06, 3), (0x10ab09, 3), (0x10ab0c, 3), (0x10ab0f, 3), (0x10ab12, 3), (0x10ab15, 2), (0x10ab17, 3), (0x10ab1a, 3), (0x10ab1d, 2), (0x10ab1f, 2), (0x10ab21, 3), (0x10ab24, 3), (0x10ab27, 3), (0x10ab2a, 3), (0x10ab2d, 2), (0x10ab2f, 3), (0x10ab32, 3), (0x10ab35, 2), (0x10ab37, 5), (0x10ab3c, 3), (0x10ab3f, 3), (0x10ab42, 2), (0x10ab44, 3), (0x10ab47, 3), (0x10ab4a, 2), (0x10ab4c, 3), (0x10ab4f, 3), (0x10ab52, 3), (0x10ab55, 3), (0x10ab58, 3), (0x10ab5b, 2), (0x10ab5d, 2), (0x10ab5f, 3), (0x10ab62, 3), (0x10ab65, 3), (0x10ab68, 2), (0x10ab6a, 3), (0x10ab6d, 3), (0x10ab70, 2), (0x10ab72, 3), (0x10ab75, 3), (0x10ab78, 3), (0x10ab7b, 3), (0x10ab7e, 2), (0x10ab80, 3), (0x10ab83, 3), (0x10ab86, 2), (0x10ab88, 5), (0x10ab8d, 3), (0x10ab90, 4), (0x10ab94, 3), (0x10ab97, 3), (0x10ab9a, 2), (0x10ab9c, 4), (0x10aba0, 2), (0x10aba2, 3)]

theorem part27_layout [Bindings] : InstructionTrace.layout part27 = part27Layout := by
  rfl

theorem part27_ordered [Bindings] : InstructionTrace.ordered 0x10aaee part27 = true := by
  rw [InstructionTrace.ordered_eq_layout, part27_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part27_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xaaee 183 = part27Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
