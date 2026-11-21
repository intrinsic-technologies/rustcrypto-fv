import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part26 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r32_r32_effect_step 0x10aa35 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aa37 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10aa3a 0x41 0xc2 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aa3e 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aa41 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa43 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aa46 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aa48 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aa4b 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10aa4d 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aa50 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10aa52 0 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10aa56 0xc7 rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10aa58 7 (.sib 4 none 0 (.d8 36)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10aa5c 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aa5f 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa61 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aa64 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aa66 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa68 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10aa6b 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 140)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aa73 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aa76 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aa78 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aa7b 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aa7d 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aa7f 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aa82 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10aa85 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aa87 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10aa8a 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aa8d 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aa90 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10aa93 0x42 (by simp [RexNoWPrefix]) 1 (.sib 2 (some 8) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10aa97 0xc1 0x14292967 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aa9d 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aaa0 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aaa3 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aaa6 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aaa9 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aaab 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aaae 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aab1 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aab3 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10aab6 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aab9 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aabc 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10aabf 0x45 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10aac2 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aac5 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aac8 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10aacb 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aace 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aad0 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10aad3 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aad5 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aad8 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aada 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aadd 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aae0 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aae3 0xc7 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10aae6 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aae8 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10aaeb 0xea 0x3 rfl rfl) (by x86_local)]

def part26Bytes : List UInt8 :=
  [0x1,0xd6,0x41,0x89,0xea,0x41,0xc1,0xc2,0x19,0x41,0x1,0xd5,0x89,0xea,0xc1,0xc2,0xe,0x31,0xf9,0x44,0x31,0xd2,0x89,0xef,0xc1,0xef,0x3,0x31,0xd7,0x1,0x44,0x24,0x78,0x1,0xc7,0x89,0x7c,0x24,0x24,0xc1,0xe8,0xa,0x89,0xf7,0xc1,0xc7,0x1a,0x31,0xc8,0x89,0xf1,0xc1,0xc1,0x15,0x44,0x8b,0x94,0x24,0x8c,0x0,0x0,0x0,0x41,0x1,0xc2,0x89,0xf2,0xc1,0xc2,0x7,0x31,0xf9,0x31,0xca,0x44,0x89,0xf1,0x44,0x31,0xf9,0x21,0xf1,0x44,0x31,0xf9,0x4c,0x89,0xf8,0x45,0x1,0xd0,0x41,0x1,0xc8,0x42,0x8d,0xc,0x2,0x81,0xc1,0x67,0x29,0x29,0x14,0x44,0x89,0xea,0xc1,0xc2,0x1e,0x44,0x89,0xef,0xc1,0xc7,0x13,0x31,0xd7,0x44,0x89,0xea,0xc1,0xc2,0xa,0x31,0xfa,0x44,0x89,0xdf,0x44,0x21,0xcf,0x45,0x89,0xd8,0x45,0x31,0xc8,0x45,0x21,0xe8,0x41,0x31,0xf8,0x41,0x1,0xd0,0x41,0x1,0xcc,0x41,0x1,0xc8,0x89,0xea,0xc1,0xc2,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xd1,0x44,0x89,0xd2,0xc1,0xc2,0x19,0x44,0x89,0xd7,0xc1,0xc7,0xe,0x31,0xd7,0x44,0x89,0xd2,0xc1,0xea,0x3]

set_option maxRecDepth 4096 in
theorem part26_bytes [Bindings] : part26.flatMap CheckedInstruction.bytes = part26Bytes  := by
  rfl

def part26Layout : List (BitVec 64 × Nat) :=
  [(0x10aa35, 2), (0x10aa37, 3), (0x10aa3a, 4), (0x10aa3e, 3), (0x10aa41, 2), (0x10aa43, 3), (0x10aa46, 2), (0x10aa48, 3), (0x10aa4b, 2), (0x10aa4d, 3), (0x10aa50, 2), (0x10aa52, 4), (0x10aa56, 2), (0x10aa58, 4), (0x10aa5c, 3), (0x10aa5f, 2), (0x10aa61, 3), (0x10aa64, 2), (0x10aa66, 2), (0x10aa68, 3), (0x10aa6b, 8), (0x10aa73, 3), (0x10aa76, 2), (0x10aa78, 3), (0x10aa7b, 2), (0x10aa7d, 2), (0x10aa7f, 3), (0x10aa82, 3), (0x10aa85, 2), (0x10aa87, 3), (0x10aa8a, 3), (0x10aa8d, 3), (0x10aa90, 3), (0x10aa93, 4), (0x10aa97, 6), (0x10aa9d, 3), (0x10aaa0, 3), (0x10aaa3, 3), (0x10aaa6, 3), (0x10aaa9, 2), (0x10aaab, 3), (0x10aaae, 3), (0x10aab1, 2), (0x10aab3, 3), (0x10aab6, 3), (0x10aab9, 3), (0x10aabc, 3), (0x10aabf, 3), (0x10aac2, 3), (0x10aac5, 3), (0x10aac8, 3), (0x10aacb, 3), (0x10aace, 2), (0x10aad0, 3), (0x10aad3, 2), (0x10aad5, 3), (0x10aad8, 2), (0x10aada, 3), (0x10aadd, 3), (0x10aae0, 3), (0x10aae3, 3), (0x10aae6, 2), (0x10aae8, 3), (0x10aaeb, 3)]

theorem part26_layout [Bindings] : InstructionTrace.layout part26 = part26Layout := by
  rfl

theorem part26_ordered [Bindings] : InstructionTrace.ordered 0x10aa35 part26 = true := by
  rw [InstructionTrace.ordered_eq_layout, part26_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part26_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xaa35 185 = part26Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
