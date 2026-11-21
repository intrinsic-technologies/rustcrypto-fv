import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part28 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10aba5 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10aba8 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10abab 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10abae 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10abb0 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10abb3 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10abb6 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10abb8 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10abbb 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10abbd 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10abc0 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10abc2 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10abc5 0xcf rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10abc7 0xc7 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10abca 0x41 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10abcd 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10abcf 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10abd2 0x42 (by simp [RexNoWPrefix]) 3 (.sib 0 (some 14) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10abd6 0xc3 0x2e1b2138 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10abdc 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10abde 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10abe1 0xfa rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10abe3 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10abe5 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10abe8 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10abeb 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10abee 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10abf1 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10abf4 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10abf7 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10abfa 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10abfd 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ac00 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac03 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac06 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ac09 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ac0c 0xef rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac0e 0xc7 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ac11 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ac13 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac15 0xc2 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ac18 0xfa rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ac1a 0xef rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ac1c 0xef 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ac1f 0xd7 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10ac21 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ac26 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ac29 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac2e 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ac31 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ac34 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac36 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac39 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r32_m32_effect_step 0x10ac3c 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ac41 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac44 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac47 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ac4a 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac4c 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ac4f 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ac52 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ac54 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ac57 0x44 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ac5a 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part28Bytes : List UInt8 :=
  [0xc1,0xc0,0x1a,0x44,0x89,0xca,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xc8,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xe2,0x31,0xf2,0x44,0x21,0xca,0x31,0xf2,0x41,0x1,0xee,0x89,0xcf,0xc1,0xc7,0x1e,0x41,0x1,0xd6,0x89,0xca,0xc1,0xc2,0x13,0x42,0x8d,0x1c,0x30,0x81,0xc3,0x38,0x21,0x1b,0x2e,0x89,0xc8,0xc1,0xc0,0xa,0x31,0xfa,0x31,0xd0,0x44,0x89,0xc2,0x44,0x21,0xea,0x45,0x89,0xc2,0x45,0x31,0xea,0x41,0x21,0xca,0x41,0x31,0xd2,0x41,0x1,0xc2,0x44,0x89,0xfa,0xc1,0xc2,0xf,0x41,0x1,0xdb,0x44,0x89,0xf8,0xc1,0xc0,0xd,0x41,0x1,0xda,0x89,0xef,0xc1,0xc7,0x19,0x31,0xd0,0x89,0xea,0xc1,0xc2,0xe,0x31,0xfa,0x89,0xef,0xc1,0xef,0x3,0x31,0xd7,0x44,0x1,0x7c,0x24,0x48,0x44,0x1,0xff,0x48,0x89,0x7c,0x24,0x28,0x44,0x89,0xfa,0xc1,0xea,0xa,0x31,0xc2,0x44,0x89,0xd8,0xc1,0xc0,0x1a,0x44,0x8b,0x7c,0x24,0x38,0x41,0x1,0xd7,0x44,0x89,0xda,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xd8,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xca,0x44,0x31,0xe2,0x44,0x21,0xda]

set_option maxRecDepth 4096 in
theorem part28_bytes [Bindings] : part28.flatMap CheckedInstruction.bytes = part28Bytes  := by
  rfl

def part28Layout : List (BitVec 64 × Nat) :=
  [(0x10aba5, 3), (0x10aba8, 3), (0x10abab, 3), (0x10abae, 2), (0x10abb0, 3), (0x10abb3, 3), (0x10abb6, 2), (0x10abb8, 3), (0x10abbb, 2), (0x10abbd, 3), (0x10abc0, 2), (0x10abc2, 3), (0x10abc5, 2), (0x10abc7, 3), (0x10abca, 3), (0x10abcd, 2), (0x10abcf, 3), (0x10abd2, 4), (0x10abd6, 6), (0x10abdc, 2), (0x10abde, 3), (0x10abe1, 2), (0x10abe3, 2), (0x10abe5, 3), (0x10abe8, 3), (0x10abeb, 3), (0x10abee, 3), (0x10abf1, 3), (0x10abf4, 3), (0x10abf7, 3), (0x10abfa, 3), (0x10abfd, 3), (0x10ac00, 3), (0x10ac03, 3), (0x10ac06, 3), (0x10ac09, 3), (0x10ac0c, 2), (0x10ac0e, 3), (0x10ac11, 2), (0x10ac13, 2), (0x10ac15, 3), (0x10ac18, 2), (0x10ac1a, 2), (0x10ac1c, 3), (0x10ac1f, 2), (0x10ac21, 5), (0x10ac26, 3), (0x10ac29, 5), (0x10ac2e, 3), (0x10ac31, 3), (0x10ac34, 2), (0x10ac36, 3), (0x10ac39, 3), (0x10ac3c, 5), (0x10ac41, 3), (0x10ac44, 3), (0x10ac47, 3), (0x10ac4a, 2), (0x10ac4c, 3), (0x10ac4f, 3), (0x10ac52, 2), (0x10ac54, 3), (0x10ac57, 3), (0x10ac5a, 3)]

theorem part28_layout [Bindings] : InstructionTrace.layout part28 = part28Layout := by
  rfl

theorem part28_ordered [Bindings] : InstructionTrace.ordered 0x10aba5 part28 = true := by
  rw [InstructionTrace.ordered_eq_layout, part28_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part28_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xaba5 184 = part28Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
