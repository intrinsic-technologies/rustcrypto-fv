import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part42 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b62c 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b630 0x42 (by simp [RexNoWPrefix]) 1 (.sib 0 (some 15) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b634 0xc1 0x1e376c08 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b63a 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b63d 0x41 0xc7 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b641 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b644 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b646 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b649 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b64c 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b64f 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b652 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b655 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b658 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b65b 0x45 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b65e 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b661 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b664 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b667 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b66a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b66d 0xfe rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b66f 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b672 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b674 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b677 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b67a 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b67e 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b680 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b683 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b686 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b688 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b68b 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b68e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b690 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b693 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b696 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b699 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b69c 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b69f 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b6a1 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b6a3 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10b6a5 0x2748774c) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6aa 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b6ad 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6b0 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b6b3 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b6b6 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6b8 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b6bb 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b6be 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b6c0 0xda rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b6c2 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6c5 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b6c8 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b6cb 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b6ce 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b6d1 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b6d4 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b6d7 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b6da 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b6dc 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b6df 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b6e1 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b6e4 0xc1 rfl) (by x86_local)]

def part42Bytes : List UInt8 :=
  [0x41,0xc1,0xc3,0x1e,0x42,0x8d,0xc,0x38,0x81,0xc1,0x8,0x6c,0x37,0x1e,0x41,0x89,0xdf,0x41,0xc1,0xc7,0x13,0x45,0x31,0xdf,0x89,0xd8,0xc1,0xc0,0xa,0x44,0x31,0xf8,0x45,0x89,0xc7,0x45,0x21,0xf7,0x45,0x89,0xc3,0x45,0x31,0xf3,0x41,0x21,0xdb,0x45,0x31,0xfb,0x41,0x1,0xc3,0x41,0x1,0xcc,0x41,0x1,0xcb,0xc1,0xc7,0xf,0xc1,0xc6,0xd,0x31,0xfe,0xc1,0xea,0xa,0x31,0xf2,0x44,0x89,0xe0,0xc1,0xc0,0x1a,0x8b,0x74,0x24,0x8,0x1,0xd6,0x44,0x89,0xe1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xe0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xe9,0x44,0x31,0xc9,0x44,0x21,0xe1,0x44,0x31,0xc9,0x4c,0x89,0xd2,0x1,0xf2,0x1,0xca,0x1,0xd0,0x5,0x4c,0x77,0x48,0x27,0x44,0x89,0xd9,0xc1,0xc1,0x1e,0x44,0x89,0xda,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xd9,0xc1,0xc1,0xa,0x31,0xd1,0x89,0xda,0x44,0x21,0xc2,0x41,0x89,0xda,0x45,0x31,0xc2,0x45,0x21,0xda,0x41,0x31,0xd2,0x41,0x1,0xca,0x41,0x1,0xc6,0x41,0x1,0xc2,0x89,0xe8,0xc1,0xc0,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xc1]

set_option maxRecDepth 4096 in
theorem part42_bytes [Bindings] : part42.flatMap CheckedInstruction.bytes = part42Bytes  := by
  rfl

def part42Layout : List (BitVec 64 × Nat) :=
  [(0x10b62c, 4), (0x10b630, 4), (0x10b634, 6), (0x10b63a, 3), (0x10b63d, 4), (0x10b641, 3), (0x10b644, 2), (0x10b646, 3), (0x10b649, 3), (0x10b64c, 3), (0x10b64f, 3), (0x10b652, 3), (0x10b655, 3), (0x10b658, 3), (0x10b65b, 3), (0x10b65e, 3), (0x10b661, 3), (0x10b664, 3), (0x10b667, 3), (0x10b66a, 3), (0x10b66d, 2), (0x10b66f, 3), (0x10b672, 2), (0x10b674, 3), (0x10b677, 3), (0x10b67a, 4), (0x10b67e, 2), (0x10b680, 3), (0x10b683, 3), (0x10b686, 2), (0x10b688, 3), (0x10b68b, 3), (0x10b68e, 2), (0x10b690, 3), (0x10b693, 3), (0x10b696, 3), (0x10b699, 3), (0x10b69c, 3), (0x10b69f, 2), (0x10b6a1, 2), (0x10b6a3, 2), (0x10b6a5, 5), (0x10b6aa, 3), (0x10b6ad, 3), (0x10b6b0, 3), (0x10b6b3, 3), (0x10b6b6, 2), (0x10b6b8, 3), (0x10b6bb, 3), (0x10b6be, 2), (0x10b6c0, 2), (0x10b6c2, 3), (0x10b6c5, 3), (0x10b6c8, 3), (0x10b6cb, 3), (0x10b6ce, 3), (0x10b6d1, 3), (0x10b6d4, 3), (0x10b6d7, 3), (0x10b6da, 2), (0x10b6dc, 3), (0x10b6df, 2), (0x10b6e1, 3), (0x10b6e4, 2)]

theorem part42_layout [Bindings] : InstructionTrace.layout part42 = part42Layout := by
  rfl

theorem part42_ordered [Bindings] : InstructionTrace.ordered 0x10b62c part42 = true := by
  rw [InstructionTrace.ordered_eq_layout, part42_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part42_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb62c 186 = part42Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
