import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part02 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b6cf 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b6d2 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6d5 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b6d8 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b6db 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b6de 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b6e0 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b6e3 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b6e6 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 232)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b6ee 0xce rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b6f0 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b6f3 0x47 (by simp [RexNoWPrefix]) 2 (.sib 15 (some 11) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10b6f7 0x41 0xc2 0xb5c0fbcf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6fe 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b701 0x41 0xc1 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b705 0xde rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b707 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b70a 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b70e 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b710 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b713 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b716 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b719 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b71c 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b721 0x45 (by simp [RexNoWPrefix]) 3 (.base 9 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b725 11) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b728 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b72d 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b730 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b733 0x45 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b736 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b739 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_rex_effect_step 0x10b73c 0x41 0xd3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b73f 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b742 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b745 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b748 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b74c 0x41 (by simp [RexNoWPrefix]) 3 (.sib 9 (some 7) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b750 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10b753 0x41 0xc1 0xe9b5dba5 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b75a 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b75c 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b75f 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b762 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b765 0x41 0xc3 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b769 0x41 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b76c 0xcd rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b76e 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b770 0xcf rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b772 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b774 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b776 0xef rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b778 0x44 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b77b 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b77e 0xc3 0xe9b5dba5 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b784 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b787 0x41 0xc3 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b78b 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b78e 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b791 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b795 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b798 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b79b 0x41 0xc3 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b79f 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part02Bytes : List UInt8 :=
  [0x45,0x31,0xca,0x44,0x31,0xd3,0x41,0x89,0xc1,0x49,0x89,0xf2,0x45,0x21,0xd1,0x89,0xc6,0x44,0x31,0xd6,0x4d,0x89,0xd6,0x4c,0x89,0x94,0x24,0xe8,0x0,0x0,0x0,0x21,0xce,0x44,0x31,0xce,0x47,0x8d,0x14,0x1f,0x41,0x81,0xc2,0xcf,0xfb,0xc0,0xb5,0x45,0x89,0xd1,0x41,0xc1,0xc1,0x1a,0x1,0xde,0x45,0x89,0xd3,0x41,0xc1,0xc3,0x15,0x1,0xfe,0x44,0x89,0xd7,0xc1,0xc7,0x7,0x45,0x31,0xcb,0x44,0x31,0xdf,0x4c,0x8b,0x4c,0x24,0x18,0x45,0x8b,0x59,0xc,0x41,0xf,0xcb,0x4c,0x89,0x5c,0x24,0x48,0x45,0x89,0xd1,0x45,0x21,0xc1,0x45,0x1,0xe3,0x45,0x1,0xd9,0x45,0x89,0xd3,0x41,0xf7,0xd3,0x41,0x21,0xd3,0x45,0x1,0xd9,0x41,0x89,0xf3,0x41,0xc1,0xc3,0x1e,0x41,0x8d,0x1c,0x39,0x41,0x1,0xf9,0x41,0x81,0xc1,0xa5,0xdb,0xb5,0xe9,0x89,0xf7,0xc1,0xc7,0x13,0x44,0x31,0xdf,0x41,0x89,0xf3,0x41,0xc1,0xc3,0xa,0x41,0x31,0xfb,0x89,0xcd,0x21,0xc5,0x89,0xcf,0x31,0xc7,0x21,0xf7,0x31,0xef,0x44,0x1,0xdf,0x44,0x1,0xf3,0x81,0xc3,0xa5,0xdb,0xb5,0xe9,0x41,0x89,0xdb,0x41,0xc1,0xc3,0x1a,0x44,0x1,0xcf,0x41,0x89,0xd9,0x41,0xc1,0xc1,0x15,0x45,0x31,0xd9,0x41,0x89,0xdb,0x41,0xc1,0xc3,0x7,0x45,0x31,0xcb]

set_option maxRecDepth 4096 in
theorem part02_bytes [Bindings] : part02.flatMap CheckedInstruction.bytes = part02Bytes  := by
  rfl

def part02Layout : List (BitVec 64 × Nat) :=
  [(0x10b6cf, 3), (0x10b6d2, 3), (0x10b6d5, 3), (0x10b6d8, 3), (0x10b6db, 3), (0x10b6de, 2), (0x10b6e0, 3), (0x10b6e3, 3), (0x10b6e6, 8), (0x10b6ee, 2), (0x10b6f0, 3), (0x10b6f3, 4), (0x10b6f7, 7), (0x10b6fe, 3), (0x10b701, 4), (0x10b705, 2), (0x10b707, 3), (0x10b70a, 4), (0x10b70e, 2), (0x10b710, 3), (0x10b713, 3), (0x10b716, 3), (0x10b719, 3), (0x10b71c, 5), (0x10b721, 4), (0x10b725, 3), (0x10b728, 5), (0x10b72d, 3), (0x10b730, 3), (0x10b733, 3), (0x10b736, 3), (0x10b739, 3), (0x10b73c, 3), (0x10b73f, 3), (0x10b742, 3), (0x10b745, 3), (0x10b748, 4), (0x10b74c, 4), (0x10b750, 3), (0x10b753, 7), (0x10b75a, 2), (0x10b75c, 3), (0x10b75f, 3), (0x10b762, 3), (0x10b765, 4), (0x10b769, 3), (0x10b76c, 2), (0x10b76e, 2), (0x10b770, 2), (0x10b772, 2), (0x10b774, 2), (0x10b776, 2), (0x10b778, 3), (0x10b77b, 3), (0x10b77e, 6), (0x10b784, 3), (0x10b787, 4), (0x10b78b, 3), (0x10b78e, 3), (0x10b791, 4), (0x10b795, 3), (0x10b798, 3), (0x10b79b, 4), (0x10b79f, 3)]

theorem part02_layout [Bindings] : InstructionTrace.layout part02 = part02Layout := by
  rfl

theorem part02_ordered [Bindings] : InstructionTrace.ordered 0x10b6cf part02 = true := by
  rw [InstructionTrace.ordered_eq_layout, part02_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part02_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xb6cf 211 = part02Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
