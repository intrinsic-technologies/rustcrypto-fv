import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part45 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b855 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b857 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b85a 0xca rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b85c 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b861 0x41 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b864 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b866 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b869 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b86b 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b86e 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b871 5 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b875 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b877 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b87a 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b87d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b87f 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b882 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b885 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b887 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b889 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b88c 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b88f 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b892 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b895 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b898 0x42 (by simp [RexNoWPrefix]) 1 (.sib 2 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b89c 0xc1 0x5b9cca4f rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b8a2 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8a4 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b8a7 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8a9 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b8ac 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b8ae 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8b0 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b8b3 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8b5 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b8b8 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8bb 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b8be 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b8c1 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b8c3 0xfe rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b8c5 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b8c7 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b8ca 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8cc 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8cf 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8d2 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8d5 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b8d8 0xca rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10b8da 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8de 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b8e1 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b8e4 0xd1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b8e6 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b8eb 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8ee 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8f1 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8f4 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8f7 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b8fa 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b8fc 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b8ff 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b902 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b904 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b907 0xda rfl) (by x86_local)]

def part45Bytes : List UInt8 :=
  [0x89,0xea,0xc1,0xc2,0xd,0x31,0xca,0x44,0x8b,0x64,0x24,0x10,0x41,0x1,0xec,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xd1,0x44,0x89,0xda,0xc1,0xc2,0x1a,0x8b,0x6c,0x24,0x48,0x1,0xcd,0x44,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xd1,0x44,0x89,0xda,0xc1,0xc2,0x7,0x31,0xca,0x89,0xd9,0x44,0x31,0xc1,0x44,0x21,0xd9,0x44,0x31,0xc1,0x41,0x1,0xee,0x41,0x1,0xce,0x42,0x8d,0xc,0x32,0x81,0xc1,0x4f,0xca,0x9c,0x5b,0x89,0xc2,0xc1,0xc2,0x1e,0x89,0xc6,0xc1,0xc6,0x13,0x31,0xd6,0x89,0xc2,0xc1,0xc2,0xa,0x31,0xf2,0x44,0x89,0xef,0x44,0x21,0xcf,0x44,0x89,0xee,0x44,0x31,0xce,0x21,0xc6,0x31,0xfe,0x1,0xd6,0x41,0x1,0xca,0x1,0xce,0x44,0x89,0xf9,0xc1,0xc1,0xf,0x44,0x89,0xfa,0xc1,0xc2,0xd,0x31,0xca,0x44,0x1,0x3c,0x24,0x44,0x89,0xf9,0xc1,0xe9,0xa,0x31,0xd1,0x44,0x8b,0x74,0x24,0x70,0x41,0x1,0xce,0x44,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x89,0xd2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xda,0x31,0xda]

set_option maxRecDepth 4096 in
theorem part45_bytes [Bindings] : part45.flatMap CheckedInstruction.bytes = part45Bytes  := by
  rfl

def part45Layout : List (BitVec 64 × Nat) :=
  [(0x10b855, 2), (0x10b857, 3), (0x10b85a, 2), (0x10b85c, 5), (0x10b861, 3), (0x10b864, 2), (0x10b866, 3), (0x10b869, 2), (0x10b86b, 3), (0x10b86e, 3), (0x10b871, 4), (0x10b875, 2), (0x10b877, 3), (0x10b87a, 3), (0x10b87d, 2), (0x10b87f, 3), (0x10b882, 3), (0x10b885, 2), (0x10b887, 2), (0x10b889, 3), (0x10b88c, 3), (0x10b88f, 3), (0x10b892, 3), (0x10b895, 3), (0x10b898, 4), (0x10b89c, 6), (0x10b8a2, 2), (0x10b8a4, 3), (0x10b8a7, 2), (0x10b8a9, 3), (0x10b8ac, 2), (0x10b8ae, 2), (0x10b8b0, 3), (0x10b8b3, 2), (0x10b8b5, 3), (0x10b8b8, 3), (0x10b8bb, 3), (0x10b8be, 3), (0x10b8c1, 2), (0x10b8c3, 2), (0x10b8c5, 2), (0x10b8c7, 3), (0x10b8ca, 2), (0x10b8cc, 3), (0x10b8cf, 3), (0x10b8d2, 3), (0x10b8d5, 3), (0x10b8d8, 2), (0x10b8da, 4), (0x10b8de, 3), (0x10b8e1, 3), (0x10b8e4, 2), (0x10b8e6, 5), (0x10b8eb, 3), (0x10b8ee, 3), (0x10b8f1, 3), (0x10b8f4, 3), (0x10b8f7, 3), (0x10b8fa, 2), (0x10b8fc, 3), (0x10b8ff, 3), (0x10b902, 2), (0x10b904, 3), (0x10b907, 2)]

theorem part45_layout [Bindings] : InstructionTrace.layout part45 = part45Layout := by
  rfl

theorem part45_ordered [Bindings] : InstructionTrace.ordered 0x10b855 part45 = true := by
  rw [InstructionTrace.ordered_eq_layout, part45_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part45_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb855 180 = part45Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
