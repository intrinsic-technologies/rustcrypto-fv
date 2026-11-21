import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part25 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r32_r32_effect_step 0x10a984 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a986 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a989 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a98c 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a98f 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a992 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a995 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a997 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a99a 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a99d 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a99f 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a9a2 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a9a5 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a9a7 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a9aa 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a9ac 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a9ae 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a9b1 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a9b3 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a9b5 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a9b8 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a9ba 5 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a9be 0xef rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10a9c0 7 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a9c4 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10a9c6 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a9c9 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a9cb 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a9ce 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a9d1 5 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a9d5 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a9d7 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a9da 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a9dd 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a9df 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a9e2 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10a9e5 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a9e7 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a9ea 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a9ed 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a9f0 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a9f3 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10a9f5 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_legacy_effect_step 0x10a9f7 2 (.sib 1 (some 3) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10a9fa 0xc2 0x6ca6351 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aa00 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa03 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aa06 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa09 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aa0c 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aa0e 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa11 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aa14 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aa16 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10aa19 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aa1c 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aa1f 0x45 0xe5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10aa22 0x45 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aa25 0x41 0xfd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aa28 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa2a 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aa2d 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aa30 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa32 0xc1 0xd rfl rfl) (by x86_local)]

def part25Bytes : List UInt8 :=
  [0x21,0xf2,0x45,0x89,0xe3,0x41,0x31,0xf3,0x45,0x21,0xcb,0x41,0x31,0xd3,0x41,0x1,0xcb,0x89,0xea,0xc1,0xc2,0xf,0x41,0x1,0xfe,0x89,0xe9,0xc1,0xc1,0xd,0x41,0x1,0xfb,0x89,0xc7,0xc1,0xc7,0x19,0x31,0xd1,0x89,0xc2,0xc1,0xc2,0xe,0x31,0xfa,0x89,0xc7,0xc1,0xef,0x3,0x31,0xd7,0x1,0x6c,0x24,0x50,0x1,0xef,0x89,0x7c,0x24,0x10,0x89,0xea,0xc1,0xea,0xa,0x31,0xca,0x44,0x89,0xf1,0xc1,0xc1,0x1a,0x8b,0x6c,0x24,0x4,0x1,0xd5,0x44,0x89,0xf2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xf1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xfa,0x44,0x31,0xc2,0x44,0x21,0xf2,0x44,0x31,0xc2,0x1,0xeb,0x1,0xd3,0x8d,0x14,0x19,0x81,0xc2,0x51,0x63,0xca,0x6,0x44,0x89,0xd9,0xc1,0xc1,0x1e,0x44,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0xa,0x31,0xf9,0x44,0x89,0xcf,0x44,0x21,0xe7,0x45,0x89,0xcd,0x45,0x31,0xe5,0x45,0x21,0xdd,0x41,0x31,0xfd,0x89,0xc7,0xc1,0xc7,0xf,0x41,0x1,0xcd,0x89,0xc1,0xc1,0xc1,0xd]

set_option maxRecDepth 4096 in
theorem part25_bytes [Bindings] : part25.flatMap CheckedInstruction.bytes = part25Bytes  := by
  rfl

def part25Layout : List (BitVec 64 × Nat) :=
  [(0x10a984, 2), (0x10a986, 3), (0x10a989, 3), (0x10a98c, 3), (0x10a98f, 3), (0x10a992, 3), (0x10a995, 2), (0x10a997, 3), (0x10a99a, 3), (0x10a99d, 2), (0x10a99f, 3), (0x10a9a2, 3), (0x10a9a5, 2), (0x10a9a7, 3), (0x10a9aa, 2), (0x10a9ac, 2), (0x10a9ae, 3), (0x10a9b1, 2), (0x10a9b3, 2), (0x10a9b5, 3), (0x10a9b8, 2), (0x10a9ba, 4), (0x10a9be, 2), (0x10a9c0, 4), (0x10a9c4, 2), (0x10a9c6, 3), (0x10a9c9, 2), (0x10a9cb, 3), (0x10a9ce, 3), (0x10a9d1, 4), (0x10a9d5, 2), (0x10a9d7, 3), (0x10a9da, 3), (0x10a9dd, 2), (0x10a9df, 3), (0x10a9e2, 3), (0x10a9e5, 2), (0x10a9e7, 3), (0x10a9ea, 3), (0x10a9ed, 3), (0x10a9f0, 3), (0x10a9f3, 2), (0x10a9f5, 2), (0x10a9f7, 3), (0x10a9fa, 6), (0x10aa00, 3), (0x10aa03, 3), (0x10aa06, 3), (0x10aa09, 3), (0x10aa0c, 2), (0x10aa0e, 3), (0x10aa11, 3), (0x10aa14, 2), (0x10aa16, 3), (0x10aa19, 3), (0x10aa1c, 3), (0x10aa1f, 3), (0x10aa22, 3), (0x10aa25, 3), (0x10aa28, 2), (0x10aa2a, 3), (0x10aa2d, 3), (0x10aa30, 2), (0x10aa32, 3)]

theorem part25_layout [Bindings] : InstructionTrace.layout part25 = part25Layout := by
  rfl

theorem part25_ordered [Bindings] : InstructionTrace.ordered 0x10a984 part25 = true := by
  rw [InstructionTrace.ordered_eq_layout, part25_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part25_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa984 177 = part25Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
