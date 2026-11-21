import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part43 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b6e6 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b6ea 0xed 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b6ed 0xcd rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b6ef 7 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b6f3 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6f5 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b6f8 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b6fb 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b6fe 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b701 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b703 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b706 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b709 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b70b 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b70e 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b711 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b714 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b717 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b71a 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b71d 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b720 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b723 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10b726 0x34b0bcb5) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b72b 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b72e 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b731 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b733 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b736 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b739 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b73b 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b73e 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b740 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b743 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b746 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b749 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b74c 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b74f 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b752 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b754 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b757 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b75a 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b75c 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b75f 0xc8 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b761 6 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b768 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b76a 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b76d 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b76f 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b772 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b775 5 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b779 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b77b 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b77e 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b781 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b783 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b786 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b789 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b78b 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b78e 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b791 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b794 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b797 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b79a 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b79d 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part43Bytes : List UInt8 :=
  [0x1,0x6c,0x24,0x68,0xc1,0xed,0xa,0x31,0xcd,0x8b,0x7c,0x24,0x50,0x1,0xef,0x44,0x89,0xf0,0xc1,0xc0,0x1a,0x44,0x89,0xf1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xf0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xe1,0x44,0x31,0xe9,0x44,0x21,0xf1,0x44,0x31,0xe9,0x41,0x1,0xf9,0x41,0x1,0xc9,0x44,0x89,0xd1,0xc1,0xc1,0x1e,0x44,0x1,0xc8,0x5,0xb5,0xbc,0xb0,0x34,0x44,0x89,0xd2,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xda,0x21,0xda,0x45,0x89,0xd9,0x41,0x31,0xd9,0x45,0x21,0xd1,0x41,0x31,0xd1,0x41,0x1,0xc9,0x41,0x1,0xc0,0x89,0xf1,0xc1,0xc1,0xf,0x41,0x1,0xc1,0x89,0xf0,0xc1,0xc0,0xd,0x31,0xc8,0x1,0xb4,0x24,0x80,0x0,0x0,0x0,0x89,0xf1,0xc1,0xe9,0xa,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x8b,0x6c,0x24,0x78,0x1,0xcd,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xf1,0x44,0x31,0xe1,0x44,0x21,0xc1,0x44,0x31,0xe1,0x41,0x1,0xed,0x41,0x1,0xcd,0x44,0x1,0xe8]

set_option maxRecDepth 4096 in
theorem part43_bytes [Bindings] : part43.flatMap CheckedInstruction.bytes = part43Bytes  := by
  rfl

def part43Layout : List (BitVec 64 × Nat) :=
  [(0x10b6e6, 4), (0x10b6ea, 3), (0x10b6ed, 2), (0x10b6ef, 4), (0x10b6f3, 2), (0x10b6f5, 3), (0x10b6f8, 3), (0x10b6fb, 3), (0x10b6fe, 3), (0x10b701, 2), (0x10b703, 3), (0x10b706, 3), (0x10b709, 2), (0x10b70b, 3), (0x10b70e, 3), (0x10b711, 3), (0x10b714, 3), (0x10b717, 3), (0x10b71a, 3), (0x10b71d, 3), (0x10b720, 3), (0x10b723, 3), (0x10b726, 5), (0x10b72b, 3), (0x10b72e, 3), (0x10b731, 2), (0x10b733, 3), (0x10b736, 3), (0x10b739, 2), (0x10b73b, 3), (0x10b73e, 2), (0x10b740, 3), (0x10b743, 3), (0x10b746, 3), (0x10b749, 3), (0x10b74c, 3), (0x10b74f, 3), (0x10b752, 2), (0x10b754, 3), (0x10b757, 3), (0x10b75a, 2), (0x10b75c, 3), (0x10b75f, 2), (0x10b761, 7), (0x10b768, 2), (0x10b76a, 3), (0x10b76d, 2), (0x10b76f, 3), (0x10b772, 3), (0x10b775, 4), (0x10b779, 2), (0x10b77b, 3), (0x10b77e, 3), (0x10b781, 2), (0x10b783, 3), (0x10b786, 3), (0x10b789, 2), (0x10b78b, 3), (0x10b78e, 3), (0x10b791, 3), (0x10b794, 3), (0x10b797, 3), (0x10b79a, 3), (0x10b79d, 3)]

theorem part43_layout [Bindings] : InstructionTrace.layout part43 = part43Layout := by
  rfl

theorem part43_ordered [Bindings] : InstructionTrace.ordered 0x10b6e6 part43 = true := by
  rw [InstructionTrace.ordered_eq_layout, part43_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part43_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb6e6 186 = part43Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
