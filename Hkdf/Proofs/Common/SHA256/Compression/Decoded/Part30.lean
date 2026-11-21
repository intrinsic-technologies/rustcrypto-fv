import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part30 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad16 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad19 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad1c 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad1e 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ad21 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad23 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad26 0xcf rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ad28 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad2b 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ad2d 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ad2f 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ad32 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad34 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad37 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad3a 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad3d 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad40 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ad42 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad44 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ad47 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad49 0xc6 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad4c 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ad4e 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ad50 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad53 0xf2 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10ad55 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ad59 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10ad5c 2 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad60 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10ad63 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad66 0xc2 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10ad68 3 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10ad6c 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad6e 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad71 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad74 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad77 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad7a 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad7c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad7f 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ad82 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ad84 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ad87 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ad8a 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ad8d 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ad90 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ad93 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ad96 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ad98 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10ad9b 0x42 (by simp [RexNoWPrefix]) 6 (.sib 0 (some 9) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10ad9f 0xc6 0x650a7354 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ada5 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ada7 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10adaa 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10adac 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10adae 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10adb1 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10adb3 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10adb6 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10adb9 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10adbc 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10adbf 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10adc1 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10adc4 0xd0 rfl) (by x86_local)]

def part30Bytes : List UInt8 :=
  [0x44,0x89,0xf2,0xc1,0xc2,0xa,0x31,0xf2,0x44,0x89,0xd6,0x21,0xce,0x44,0x89,0xd7,0x31,0xcf,0x44,0x21,0xf7,0x31,0xf7,0x1,0xd7,0x41,0x1,0xc0,0x1,0xc7,0x44,0x89,0xfa,0xc1,0xc2,0xf,0x44,0x89,0xf8,0xc1,0xc0,0xd,0x31,0xd0,0x89,0xea,0xc1,0xc2,0x19,0x89,0xee,0xc1,0xc6,0xe,0x31,0xd6,0x89,0xea,0xc1,0xea,0x3,0x31,0xf2,0x44,0x1,0x3c,0x24,0x44,0x1,0xfa,0x89,0x54,0x24,0x8,0x44,0x89,0xfa,0xc1,0xea,0xa,0x31,0xc2,0x8b,0x5c,0x24,0x78,0x1,0xd3,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x44,0x89,0xc2,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xea,0x44,0x31,0xda,0x44,0x21,0xc2,0x44,0x31,0xda,0x41,0x1,0xd9,0x41,0x1,0xd1,0x89,0xfa,0xc1,0xc2,0x1e,0x42,0x8d,0x34,0x8,0x81,0xc6,0x54,0x73,0xa,0x65,0x89,0xf8,0xc1,0xc0,0x13,0x31,0xd0,0x89,0xfa,0xc1,0xc2,0xa,0x31,0xc2,0x45,0x89,0xf1,0x45,0x21,0xd1,0x44,0x89,0xf0,0x44,0x31,0xd0,0x21,0xf8,0x44,0x31,0xc8,0x1,0xd0]

set_option maxRecDepth 4096 in
theorem part30_bytes [Bindings] : part30.flatMap CheckedInstruction.bytes = part30Bytes  := by
  rfl

def part30Layout : List (BitVec 64 × Nat) :=
  [(0x10ad16, 3), (0x10ad19, 3), (0x10ad1c, 2), (0x10ad1e, 3), (0x10ad21, 2), (0x10ad23, 3), (0x10ad26, 2), (0x10ad28, 3), (0x10ad2b, 2), (0x10ad2d, 2), (0x10ad2f, 3), (0x10ad32, 2), (0x10ad34, 3), (0x10ad37, 3), (0x10ad3a, 3), (0x10ad3d, 3), (0x10ad40, 2), (0x10ad42, 2), (0x10ad44, 3), (0x10ad47, 2), (0x10ad49, 3), (0x10ad4c, 2), (0x10ad4e, 2), (0x10ad50, 3), (0x10ad53, 2), (0x10ad55, 4), (0x10ad59, 3), (0x10ad5c, 4), (0x10ad60, 3), (0x10ad63, 3), (0x10ad66, 2), (0x10ad68, 4), (0x10ad6c, 2), (0x10ad6e, 3), (0x10ad71, 3), (0x10ad74, 3), (0x10ad77, 3), (0x10ad7a, 2), (0x10ad7c, 3), (0x10ad7f, 3), (0x10ad82, 2), (0x10ad84, 3), (0x10ad87, 3), (0x10ad8a, 3), (0x10ad8d, 3), (0x10ad90, 3), (0x10ad93, 3), (0x10ad96, 2), (0x10ad98, 3), (0x10ad9b, 4), (0x10ad9f, 6), (0x10ada5, 2), (0x10ada7, 3), (0x10adaa, 2), (0x10adac, 2), (0x10adae, 3), (0x10adb1, 2), (0x10adb3, 3), (0x10adb6, 3), (0x10adb9, 3), (0x10adbc, 3), (0x10adbf, 2), (0x10adc1, 3), (0x10adc4, 2)]

theorem part30_layout [Bindings] : InstructionTrace.layout part30 = part30Layout := by
  rfl

theorem part30_ordered [Bindings] : InstructionTrace.ordered 0x10ad16 part30 = true := by
  rw [InstructionTrace.ordered_eq_layout, part30_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part30_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xad16 176 = part30Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
