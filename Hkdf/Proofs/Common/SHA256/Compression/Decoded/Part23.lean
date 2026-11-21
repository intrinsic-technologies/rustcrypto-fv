import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part23 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a7f8 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a7fb 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a7fe 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a800 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10a803 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a805 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a808 0x41 0xc4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a80b 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10a80e 0x43 (by simp [RexNoWPrefix]) 1 (.sib 9 (some 12) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10a812 0xc1 0xbf597fc7 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a818 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a81b 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a81f 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a822 0x41 0xc2 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a826 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a829 0x41 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a82c 0x41 0xc1 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a830 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a833 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a836 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a839 0x45 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a83c 0x45 0xfc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a83f 0x41 0xf4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a842 0x45 0xd4 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a845 0x45 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a848 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a84b 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a84e 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a851 0x41 0xc1 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10a855 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a857 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a85a 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a85d 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a860 0x41 0xc1 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a864 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a867 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a86b 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a86e 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a871 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a875 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10a878 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a87c 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10a87f 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a887 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10a88a 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a88e 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10a891 5 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a895 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a898 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a89b 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a89e 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a8a1 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a8a5 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a8a8 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10a8ab 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a8ae 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a8b1 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a8b4 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10a8b7 0x45 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10a8ba 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a8bd 0x41 0xed (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10a8c0 0x45 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10a8c3 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10a8c6 0x41 0xc1 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part23Bytes : List UInt8 :=
  [0x44,0x31,0xd1,0x41,0x31,0xc9,0x89,0xf9,0x44,0x31,0xe9,0x21,0xd9,0x44,0x31,0xe9,0x41,0x1,0xc4,0x41,0x1,0xcc,0x43,0x8d,0xc,0x21,0x81,0xc1,0xc7,0x7f,0x59,0xbf,0x41,0x89,0xf1,0x41,0xc1,0xc1,0x1e,0x41,0x89,0xf2,0x41,0xc1,0xc2,0x13,0x45,0x31,0xca,0x41,0x89,0xf1,0x41,0xc1,0xc1,0xa,0x45,0x31,0xd1,0x45,0x89,0xf2,0x45,0x21,0xfa,0x45,0x89,0xf4,0x45,0x31,0xfc,0x41,0x21,0xf4,0x45,0x31,0xd4,0x45,0x1,0xcc,0x41,0x1,0xc8,0x41,0x1,0xcc,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x44,0x31,0xc9,0x41,0x89,0xc1,0x41,0xc1,0xc1,0x19,0x41,0x89,0xc2,0x41,0xc1,0xc2,0xe,0x45,0x31,0xca,0x41,0x89,0xc1,0x41,0xc1,0xe9,0x3,0x45,0x31,0xd1,0x1,0x6c,0x24,0x8,0x41,0x1,0xe9,0x44,0x89,0x8c,0x24,0x80,0x0,0x0,0x0,0x41,0x89,0xe9,0x41,0xc1,0xe9,0xa,0x41,0x31,0xc9,0x8b,0x6c,0x24,0x10,0x44,0x1,0xcd,0x44,0x89,0xc1,0xc1,0xc1,0x1a,0x45,0x89,0xc1,0x41,0xc1,0xc1,0x15,0x41,0x31,0xc9,0x44,0x89,0xc1,0xc1,0xc1,0x7,0x44,0x31,0xc9,0x41,0x89,0xd9,0x41,0x31,0xf9,0x45,0x21,0xc1,0x41,0x31,0xf9,0x41,0x1,0xed,0x45,0x1,0xcd,0x45,0x89,0xe1,0x41,0xc1,0xc1,0x1e]

set_option maxRecDepth 4096 in
theorem part23_bytes [Bindings] : part23.flatMap CheckedInstruction.bytes = part23Bytes  := by
  rfl

def part23Layout : List (BitVec 64 × Nat) :=
  [(0x10a7f8, 3), (0x10a7fb, 3), (0x10a7fe, 2), (0x10a800, 3), (0x10a803, 2), (0x10a805, 3), (0x10a808, 3), (0x10a80b, 3), (0x10a80e, 4), (0x10a812, 6), (0x10a818, 3), (0x10a81b, 4), (0x10a81f, 3), (0x10a822, 4), (0x10a826, 3), (0x10a829, 3), (0x10a82c, 4), (0x10a830, 3), (0x10a833, 3), (0x10a836, 3), (0x10a839, 3), (0x10a83c, 3), (0x10a83f, 3), (0x10a842, 3), (0x10a845, 3), (0x10a848, 3), (0x10a84b, 3), (0x10a84e, 3), (0x10a851, 4), (0x10a855, 2), (0x10a857, 3), (0x10a85a, 3), (0x10a85d, 3), (0x10a860, 4), (0x10a864, 3), (0x10a867, 4), (0x10a86b, 3), (0x10a86e, 3), (0x10a871, 4), (0x10a875, 3), (0x10a878, 4), (0x10a87c, 3), (0x10a87f, 8), (0x10a887, 3), (0x10a88a, 4), (0x10a88e, 3), (0x10a891, 4), (0x10a895, 3), (0x10a898, 3), (0x10a89b, 3), (0x10a89e, 3), (0x10a8a1, 4), (0x10a8a5, 3), (0x10a8a8, 3), (0x10a8ab, 3), (0x10a8ae, 3), (0x10a8b1, 3), (0x10a8b4, 3), (0x10a8b7, 3), (0x10a8ba, 3), (0x10a8bd, 3), (0x10a8c0, 3), (0x10a8c3, 3), (0x10a8c6, 4)]

theorem part23_layout [Bindings] : InstructionTrace.layout part23 = part23Layout := by
  rfl

theorem part23_ordered [Bindings] : InstructionTrace.ordered 0x10a7f8 part23 = true := by
  rw [InstructionTrace.ordered_eq_layout, part23_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part23_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xa7f8 210 = part23Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
