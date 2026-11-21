import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part45 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d775 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d777 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d77a 0xca rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10d77c 0x44 (by simp [RexNoWPrefix]) 4 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d781 0x41 0xec (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d784 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d786 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d789 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d78b 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d78e 0xc2 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d791 5 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d795 0xcd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d797 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d79a 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d79d 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d79f 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d7a2 0xc2 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d7a5 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d7a7 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d7a9 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d7ac 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d7af 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d7b2 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d7b5 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10d7b8 0x42 (by simp [RexNoWPrefix]) 1 (.sib 2 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10d7bc 0xc1 0x5b9cca4f rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d7c2 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d7c4 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d7c7 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d7c9 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d7cc 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d7ce 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d7d0 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d7d3 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d7d5 0x44 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d7d8 0x44 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d7db 0x44 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d7de 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10d7e1 0xc6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d7e3 0xfe rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d7e5 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d7e7 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d7ea 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d7ec 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d7ef 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d7f2 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d7f5 0xc2 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d7f8 0xca rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10d7fa 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d7fe 0x44 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d801 0xe9 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d804 0xd1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10d806 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d80b 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d80e 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d811 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d814 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d817 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d81a 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d81c 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d81f 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d822 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d824 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d827 0xda rfl) (by x86_local)]

def part45Bytes : List UInt8 :=
  [0x89,0xea,0xc1,0xc2,0xd,0x31,0xca,0x44,0x8b,0x64,0x24,0x10,0x41,0x1,0xec,0x89,0xe9,0xc1,0xe9,0xa,0x31,0xd1,0x44,0x89,0xda,0xc1,0xc2,0x1a,0x8b,0x6c,0x24,0x48,0x1,0xcd,0x44,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xd1,0x44,0x89,0xda,0xc1,0xc2,0x7,0x31,0xca,0x89,0xd9,0x44,0x31,0xc1,0x44,0x21,0xd9,0x44,0x31,0xc1,0x41,0x1,0xee,0x41,0x1,0xce,0x42,0x8d,0xc,0x32,0x81,0xc1,0x4f,0xca,0x9c,0x5b,0x89,0xc2,0xc1,0xc2,0x1e,0x89,0xc6,0xc1,0xc6,0x13,0x31,0xd6,0x89,0xc2,0xc1,0xc2,0xa,0x31,0xf2,0x44,0x89,0xef,0x44,0x21,0xcf,0x44,0x89,0xee,0x44,0x31,0xce,0x21,0xc6,0x31,0xfe,0x1,0xd6,0x41,0x1,0xca,0x1,0xce,0x44,0x89,0xf9,0xc1,0xc1,0xf,0x44,0x89,0xfa,0xc1,0xc2,0xd,0x31,0xca,0x44,0x1,0x3c,0x24,0x44,0x89,0xf9,0xc1,0xe9,0xa,0x31,0xd1,0x44,0x8b,0x74,0x24,0x70,0x41,0x1,0xce,0x44,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x89,0xd2,0xc1,0xc2,0x15,0x31,0xca,0x44,0x89,0xd1,0xc1,0xc1,0x7,0x31,0xd1,0x44,0x89,0xda,0x31,0xda]

set_option maxRecDepth 4096 in
theorem part45_bytes [Bindings] : part45.flatMap CheckedInstruction.bytes = part45Bytes  := by
  rfl

def part45Layout : List (BitVec 64 × Nat) :=
  [(0x10d775, 2), (0x10d777, 3), (0x10d77a, 2), (0x10d77c, 5), (0x10d781, 3), (0x10d784, 2), (0x10d786, 3), (0x10d789, 2), (0x10d78b, 3), (0x10d78e, 3), (0x10d791, 4), (0x10d795, 2), (0x10d797, 3), (0x10d79a, 3), (0x10d79d, 2), (0x10d79f, 3), (0x10d7a2, 3), (0x10d7a5, 2), (0x10d7a7, 2), (0x10d7a9, 3), (0x10d7ac, 3), (0x10d7af, 3), (0x10d7b2, 3), (0x10d7b5, 3), (0x10d7b8, 4), (0x10d7bc, 6), (0x10d7c2, 2), (0x10d7c4, 3), (0x10d7c7, 2), (0x10d7c9, 3), (0x10d7cc, 2), (0x10d7ce, 2), (0x10d7d0, 3), (0x10d7d3, 2), (0x10d7d5, 3), (0x10d7d8, 3), (0x10d7db, 3), (0x10d7de, 3), (0x10d7e1, 2), (0x10d7e3, 2), (0x10d7e5, 2), (0x10d7e7, 3), (0x10d7ea, 2), (0x10d7ec, 3), (0x10d7ef, 3), (0x10d7f2, 3), (0x10d7f5, 3), (0x10d7f8, 2), (0x10d7fa, 4), (0x10d7fe, 3), (0x10d801, 3), (0x10d804, 2), (0x10d806, 5), (0x10d80b, 3), (0x10d80e, 3), (0x10d811, 3), (0x10d814, 3), (0x10d817, 3), (0x10d81a, 2), (0x10d81c, 3), (0x10d81f, 3), (0x10d822, 2), (0x10d824, 3), (0x10d827, 2)]

theorem part45_layout [Bindings] : InstructionTrace.layout part45 = part45Layout := by
  rfl

theorem part45_ordered [Bindings] : InstructionTrace.ordered 0x10d775 part45 = true := by
  rw [InstructionTrace.ordered_eq_layout, part45_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part45_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd775 180 = part45Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
