import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part44 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10b7a0 0x391c0cb3) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7a5 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b7a8 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7ab 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b7ae 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b7b1 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7b3 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b7b6 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b7b9 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7bb 0x44 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b7be 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b7c1 0x45 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b7c4 0x45 0xdd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b7c7 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b7ca 0x41 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b7cd 0x41 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b7d0 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b7d2 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b7d5 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b7d7 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b7da 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b7dc 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b7df 0xc1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b7e1 7 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b7e5 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b7e7 0xe8 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b7ea 0xc8 rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10b7ec 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 20)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b7f1 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b7f4 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b7f6 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b7f9 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b7fb 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b7fe 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b800 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b802 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b805 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b807 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b80a 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b80d 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b80f 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b812 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b815 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b818 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b81b 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b81e 0x42 (by simp [RexNoWPrefix]) 2 (.sib 0 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b822 0xc2 0x4ed8aa4a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b828 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b82b 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b82e 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b830 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b833 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b836 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b838 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b83b 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b83e 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b841 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b844 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b847 0xf0 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b849 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b84b 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b84e 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b850 0xc1 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b853 0xd0 rfl) (by x86_local)]

def part44Bytes : List UInt8 :=
  [0x5,0xb3,0xc,0x1c,0x39,0x44,0x89,0xc9,0xc1,0xc1,0x1e,0x44,0x89,0xca,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xc9,0xc1,0xc1,0xa,0x31,0xd1,0x44,0x89,0xd2,0x44,0x21,0xda,0x45,0x89,0xd5,0x45,0x31,0xdd,0x45,0x21,0xcd,0x41,0x31,0xd5,0x41,0x1,0xcd,0x1,0xc3,0x41,0x1,0xc5,0x89,0xf8,0xc1,0xc0,0xf,0x89,0xf9,0xc1,0xc1,0xd,0x31,0xc1,0x1,0x7c,0x24,0x58,0x89,0xf8,0xc1,0xe8,0xa,0x31,0xc8,0x44,0x8b,0x7c,0x24,0x14,0x41,0x1,0xc7,0x89,0xd8,0xc1,0xc0,0x1a,0x89,0xd9,0xc1,0xc1,0x15,0x31,0xc1,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xc1,0x44,0x31,0xf1,0x21,0xd9,0x44,0x31,0xf1,0x45,0x1,0xfc,0x41,0x1,0xcc,0x44,0x89,0xe9,0xc1,0xc1,0x1e,0x42,0x8d,0x14,0x20,0x81,0xc2,0x4a,0xaa,0xd8,0x4e,0x44,0x89,0xe8,0xc1,0xc0,0x13,0x31,0xc8,0x44,0x89,0xe9,0xc1,0xc1,0xa,0x31,0xc1,0x44,0x89,0xce,0x44,0x21,0xd6,0x44,0x89,0xc8,0x44,0x31,0xd0,0x44,0x21,0xe8,0x31,0xf0,0x1,0xc8,0x41,0x1,0xd3,0x89,0xe9,0xc1,0xc1,0xf,0x1,0xd0]

set_option maxRecDepth 4096 in
theorem part44_bytes [Bindings] : part44.flatMap CheckedInstruction.bytes = part44Bytes  := by
  rfl

def part44Layout : List (BitVec 64 × Nat) :=
  [(0x10b7a0, 5), (0x10b7a5, 3), (0x10b7a8, 3), (0x10b7ab, 3), (0x10b7ae, 3), (0x10b7b1, 2), (0x10b7b3, 3), (0x10b7b6, 3), (0x10b7b9, 2), (0x10b7bb, 3), (0x10b7be, 3), (0x10b7c1, 3), (0x10b7c4, 3), (0x10b7c7, 3), (0x10b7ca, 3), (0x10b7cd, 3), (0x10b7d0, 2), (0x10b7d2, 3), (0x10b7d5, 2), (0x10b7d7, 3), (0x10b7da, 2), (0x10b7dc, 3), (0x10b7df, 2), (0x10b7e1, 4), (0x10b7e5, 2), (0x10b7e7, 3), (0x10b7ea, 2), (0x10b7ec, 5), (0x10b7f1, 3), (0x10b7f4, 2), (0x10b7f6, 3), (0x10b7f9, 2), (0x10b7fb, 3), (0x10b7fe, 2), (0x10b800, 2), (0x10b802, 3), (0x10b805, 2), (0x10b807, 3), (0x10b80a, 3), (0x10b80d, 2), (0x10b80f, 3), (0x10b812, 3), (0x10b815, 3), (0x10b818, 3), (0x10b81b, 3), (0x10b81e, 4), (0x10b822, 6), (0x10b828, 3), (0x10b82b, 3), (0x10b82e, 2), (0x10b830, 3), (0x10b833, 3), (0x10b836, 2), (0x10b838, 3), (0x10b83b, 3), (0x10b83e, 3), (0x10b841, 3), (0x10b844, 3), (0x10b847, 2), (0x10b849, 2), (0x10b84b, 3), (0x10b84e, 2), (0x10b850, 3), (0x10b853, 2)]

theorem part44_layout [Bindings] : InstructionTrace.layout part44 = part44Layout := by
  rfl

theorem part44_ordered [Bindings] : InstructionTrace.ordered 0x10b7a0 part44 = true := by
  rw [InstructionTrace.ordered_eq_layout, part44_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part44_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb7a0 181 = part44Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
