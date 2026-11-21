import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part09 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109cd7 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109cd9 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109cdc 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109cde 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109ce0 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109ce3 0xce rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109ce5 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109cea 5 (.base 1 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109ced 5) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109cef 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109cf1 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109cf3 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109cf6 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109cf9 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109cfb 0xd1 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109cfd 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109d00 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x109d03 0x42 (by simp [RexNoWPrefix]) 1 (.sib 6 (some 11) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109d07 0xc1 0x9bdc06a7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d0d 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d10 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d13 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d16 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109d19 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d1b 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d1e 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109d21 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d23 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109d26 0xdf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d28 0x45 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109d2b 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109d2e 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x109d31 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109d34 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109d37 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109d3a 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x109d3d 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d40 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d43 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d46 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d49 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109d4c 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d4e 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d51 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109d54 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x109d56 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x109d5b 0x44 (by simp [RexNoWPrefix]) 5 (.base 6 (.d8 60)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109d5f 13) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d62 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109d65 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109d67 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109d6a 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d6d 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109d70 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x109d72 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109d74 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d77 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d7a 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x109d7d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109d80 0xc1 0xc19bf174 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d86 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109d89 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109d8c 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109d8e 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part09Bytes : List UInt8 :=
  [0x89,0xd1,0xc1,0xc1,0x15,0x31,0xf1,0x89,0xd6,0xc1,0xc6,0x7,0x31,0xce,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x69,0x38,0xf,0xcd,0x89,0xd1,0x21,0xc1,0x41,0x1,0xeb,0x41,0x1,0xcb,0x89,0xd1,0xf7,0xd1,0x44,0x21,0xd1,0x41,0x1,0xcb,0x42,0x8d,0xc,0x1e,0x81,0xc1,0xa7,0x6,0xdc,0x9b,0x44,0x89,0xf6,0xc1,0xc6,0x1e,0x44,0x89,0xf7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xf6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xcf,0x21,0xdf,0x45,0x89,0xc8,0x41,0x31,0xd8,0x45,0x21,0xf0,0x41,0x31,0xf8,0x41,0x1,0xf0,0x41,0x1,0xcf,0x41,0x1,0xc8,0x4d,0x89,0xc3,0x44,0x89,0xf9,0xc1,0xc1,0x1a,0x44,0x89,0xfe,0xc1,0xc6,0x15,0x31,0xce,0x44,0x89,0xf9,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x44,0x8b,0x6e,0x3c,0x41,0xf,0xcd,0x44,0x89,0xfe,0x21,0xd6,0x45,0x1,0xea,0x41,0x1,0xf2,0x44,0x89,0xfe,0xf7,0xd6,0x21,0xc6,0x41,0x1,0xf2,0x44,0x89,0xde,0xc1,0xc6,0x1e,0x44,0x1,0xd1,0x81,0xc1,0x74,0xf1,0x9b,0xc1,0x44,0x89,0xdf,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xde]

set_option maxRecDepth 4096 in
theorem part09_bytes [Bindings] : part09.flatMap CheckedInstruction.bytes = part09Bytes  := by
  rfl

def part09Layout : List (BitVec 64 × Nat) :=
  [(0x109cd7, 2), (0x109cd9, 3), (0x109cdc, 2), (0x109cde, 2), (0x109ce0, 3), (0x109ce3, 2), (0x109ce5, 5), (0x109cea, 3), (0x109ced, 2), (0x109cef, 2), (0x109cf1, 2), (0x109cf3, 3), (0x109cf6, 3), (0x109cf9, 2), (0x109cfb, 2), (0x109cfd, 3), (0x109d00, 3), (0x109d03, 4), (0x109d07, 6), (0x109d0d, 3), (0x109d10, 3), (0x109d13, 3), (0x109d16, 3), (0x109d19, 2), (0x109d1b, 3), (0x109d1e, 3), (0x109d21, 2), (0x109d23, 3), (0x109d26, 2), (0x109d28, 3), (0x109d2b, 3), (0x109d2e, 3), (0x109d31, 3), (0x109d34, 3), (0x109d37, 3), (0x109d3a, 3), (0x109d3d, 3), (0x109d40, 3), (0x109d43, 3), (0x109d46, 3), (0x109d49, 3), (0x109d4c, 2), (0x109d4e, 3), (0x109d51, 3), (0x109d54, 2), (0x109d56, 5), (0x109d5b, 4), (0x109d5f, 3), (0x109d62, 3), (0x109d65, 2), (0x109d67, 3), (0x109d6a, 3), (0x109d6d, 3), (0x109d70, 2), (0x109d72, 2), (0x109d74, 3), (0x109d77, 3), (0x109d7a, 3), (0x109d7d, 3), (0x109d80, 6), (0x109d86, 3), (0x109d89, 3), (0x109d8c, 2), (0x109d8e, 3)]

theorem part09_layout [Bindings] : InstructionTrace.layout part09 = part09Layout := by
  rfl

theorem part09_ordered [Bindings] : InstructionTrace.ordered 0x109cd7 part09 = true := by
  rw [InstructionTrace.ordered_eq_layout, part09_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part09_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9cd7 186 = part09Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
