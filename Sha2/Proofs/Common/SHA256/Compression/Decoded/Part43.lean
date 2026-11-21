import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part43 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (add_m32_r32_effect_step 0x10d606 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d60a 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d60d 0xcd rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d60f 7 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d613 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d615 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d618 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d61b 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d61e 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d621 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d623 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d626 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d629 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d62b 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d62e 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d631 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d634 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d637 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d63a 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d63d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d640 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d643 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10d646 0x34b0bcb5) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d64b 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d64e 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d651 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d653 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d656 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d659 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d65b 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d65e 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d660 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d663 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d666 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d669 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d66c 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d66f 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d672 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d674 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d677 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d67a 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d67c 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d67f 0xc8 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10d681 6 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d688 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d68a 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d68d 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d68f 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d692 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d695 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d699 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d69b 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d69e 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d6a1 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d6a3 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d6a6 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d6a9 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d6ab 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d6ae 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d6b1 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d6b4 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d6b7 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d6ba 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d6bd 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part43Bytes : List UInt8 :=
  [0x1,0x6c,0x24,0x68,0xc1,0xed,0xa,0x31,0xcd,0x8b,0x7c,0x24,0x50,0x1,0xef,0x44,0x89,0xf0,0xc1,0xc0,0x1a,0x44,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xe1,0x44,0x31,0xe9,0x44,0x21,0xf1,0x44,0x31,0xe9,0x41,0x1,0xf9,0x41,0x1,0xc9,0x44,0x89,0xd1,0xc1,0xc1,0x1e,0x44,0x1,0xc8,0x5,0xb5,0xbc,0xb0,0x34,0x44,0x89,0xd2,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xda,0x21,0xda,0x45,0x89,0xd9,0x41,0x31,0xd9,0x45,0x21,0xd1,0x41,0x31,0xd1,0x41,0x1,0xc9,0x41,0x1,0xc0,0x89,0xf1,0xc1,0xc1,0xf,0x41,0x1,0xc1,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x1,0xb4,0x24,0x80,0x0,0x0,0x0,0x89,0xf1,0xc1,0xe9,0xa,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x8b,0x6c,0x24,0x78,0x1,0xcd,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf1,0x44,0x31,0xe1,0x44,0x21,0xc1,0x44,0x31,0xe1,0x41,0x1,0xed,0x41,0x1,0xcd,0x44,0x1,0xe8]

set_option maxRecDepth 4096 in
theorem part43_bytes [Bindings] : part43.flatMap CheckedInstruction.bytes = part43Bytes  := by
  rfl

def part43Layout : List (BitVec 64 × Nat) :=
  [(0x10d606, 4), (0x10d60a, 3), (0x10d60d, 2), (0x10d60f, 4), (0x10d613, 2), (0x10d615, 3), (0x10d618, 3), (0x10d61b, 3), (0x10d61e, 3), (0x10d621, 2), (0x10d623, 3), (0x10d626, 3), (0x10d629, 2), (0x10d62b, 3), (0x10d62e, 3), (0x10d631, 3), (0x10d634, 3), (0x10d637, 3), (0x10d63a, 3), (0x10d63d, 3), (0x10d640, 3), (0x10d643, 3), (0x10d646, 5), (0x10d64b, 3), (0x10d64e, 3), (0x10d651, 2), (0x10d653, 3), (0x10d656, 3), (0x10d659, 2), (0x10d65b, 3), (0x10d65e, 2), (0x10d660, 3), (0x10d663, 3), (0x10d666, 3), (0x10d669, 3), (0x10d66c, 3), (0x10d66f, 3), (0x10d672, 2), (0x10d674, 3), (0x10d677, 3), (0x10d67a, 2), (0x10d67c, 3), (0x10d67f, 2), (0x10d681, 7), (0x10d688, 2), (0x10d68a, 3), (0x10d68d, 2), (0x10d68f, 3), (0x10d692, 3), (0x10d695, 4), (0x10d699, 2), (0x10d69b, 3), (0x10d69e, 3), (0x10d6a1, 2), (0x10d6a3, 3), (0x10d6a6, 3), (0x10d6a9, 2), (0x10d6ab, 3), (0x10d6ae, 3), (0x10d6b1, 3), (0x10d6b4, 3), (0x10d6b7, 3), (0x10d6ba, 3), (0x10d6bd, 3)]

theorem part43_layout [Bindings] : InstructionTrace.layout part43 = part43Layout := by
  rfl

theorem part43_ordered [Bindings] : InstructionTrace.ordered 0x10d606 part43 = true := by
  rw [InstructionTrace.ordered_eq_layout, part43_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part43_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd606 186 = part43Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
