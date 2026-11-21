import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part30 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc36 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc39 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc3c 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc3e 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10cc41 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc43 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc46 0xcf rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10cc48 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc4b 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cc4d 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cc4f 0x41 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cc52 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc54 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc57 0xc2 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc5a 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc5d 0xc0 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc60 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cc62 0xea rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc64 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cc67 0xee rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc69 0xc6 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc6c 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cc6e 0xea rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cc70 0xea 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc73 0xf2 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10cc75 0x44 (by simp [RexNoWPrefix]) 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10cc79 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10cc7c 2 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc80 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10cc83 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc86 0xc2 rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10cc88 3 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cc8c 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc8e 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc91 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc94 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc97 0xc2 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cc9a 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cc9c 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10cc9f 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10cca2 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10cca4 0x44 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cca7 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ccaa 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ccad 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ccb0 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10ccb3 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ccb6 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ccb8 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10ccbb 0x42 (by simp [RexNoWPrefix]) 6 (.sib 0 (some 9) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10ccbf 0xc6 0x650a7354 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ccc5 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ccc7 0xc0 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ccca 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10cccc 0xfa rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10ccce 0xc2 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10ccd1 0xc2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ccd3 0x45 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ccd6 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ccd9 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ccdc 0x44 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10ccdf 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10cce1 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10cce4 0xd0 rfl) (by x86_local)]

def part30Bytes : List UInt8 :=
  [0x44,0x89,0xf2,0xc1,0xc2,0xa,0x31,0xf2,0x44,0x89,0xd6,0x21,0xce,0x44,0x89,0xd7,0x31,0xcf,0x44,0x21,0xf7,0x31,0xf7,0x1,0xd7,0x41,0x1,0xc0,0x1,0xc7,0x44,0x89,0xfa,0xc1,0xc2,0xf,0x44,0x89,0xf8,0xc1,0xc0,0xd,0x31,0xd0,0x89,0xea,0xc1,0xc2,0x19,0x89,0xee,0xc1,0xc6,0xe,0x31,0xd6,0x89,0xea,0xc1,0xea,0x3,0x31,0xf2,0x44,0x1,0x3c,0x24,0x44,0x1,0xfa,0x89,0x54,0x24,0x8,0x44,0x89,0xfa,0xc1,0xea,0xa,0x31,0xc2,0x8b,0x5c,0x24,0x78,0x1,0xd3,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x44,0x89,0xc2,0xc1,0xc2,0x15,0x31,0xc2,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xd0,0x44,0x89,0xea,0x44,0x31,0xda,0x44,0x21,0xc2,0x44,0x31,0xda,0x41,0x1,0xd9,0x41,0x1,0xd1,0x89,0xfa,0xc1,0xc2,0x1e,0x42,0x8d,0x34,0x8,0x81,0xc6,0x54,0x73,0xa,0x65,0x89,0xf8,0xc1,0xc0,0x13,0x31,0xd0,0x89,0xfa,0xc1,0xc2,0xa,0x31,0xc2,0x45,0x89,0xf1,0x45,0x21,0xd1,0x44,0x89,0xf0,0x44,0x31,0xd0,0x21,0xf8,0x44,0x31,0xc8,0x1,0xd0]

set_option maxRecDepth 4096 in
theorem part30_bytes [Bindings] : part30.flatMap CheckedInstruction.bytes = part30Bytes  := by
  rfl

def part30Layout : List (BitVec 64 × Nat) :=
  [(0x10cc36, 3), (0x10cc39, 3), (0x10cc3c, 2), (0x10cc3e, 3), (0x10cc41, 2), (0x10cc43, 3), (0x10cc46, 2), (0x10cc48, 3), (0x10cc4b, 2), (0x10cc4d, 2), (0x10cc4f, 3), (0x10cc52, 2), (0x10cc54, 3), (0x10cc57, 3), (0x10cc5a, 3), (0x10cc5d, 3), (0x10cc60, 2), (0x10cc62, 2), (0x10cc64, 3), (0x10cc67, 2), (0x10cc69, 3), (0x10cc6c, 2), (0x10cc6e, 2), (0x10cc70, 3), (0x10cc73, 2), (0x10cc75, 4), (0x10cc79, 3), (0x10cc7c, 4), (0x10cc80, 3), (0x10cc83, 3), (0x10cc86, 2), (0x10cc88, 4), (0x10cc8c, 2), (0x10cc8e, 3), (0x10cc91, 3), (0x10cc94, 3), (0x10cc97, 3), (0x10cc9a, 2), (0x10cc9c, 3), (0x10cc9f, 3), (0x10cca2, 2), (0x10cca4, 3), (0x10cca7, 3), (0x10ccaa, 3), (0x10ccad, 3), (0x10ccb0, 3), (0x10ccb3, 3), (0x10ccb6, 2), (0x10ccb8, 3), (0x10ccbb, 4), (0x10ccbf, 6), (0x10ccc5, 2), (0x10ccc7, 3), (0x10ccca, 2), (0x10cccc, 2), (0x10ccce, 3), (0x10ccd1, 2), (0x10ccd3, 3), (0x10ccd6, 3), (0x10ccd9, 3), (0x10ccdc, 3), (0x10ccdf, 2), (0x10cce1, 3), (0x10cce4, 2)]

theorem part30_layout [Bindings] : InstructionTrace.layout part30 = part30Layout := by
  rfl

theorem part30_ordered [Bindings] : InstructionTrace.ordered 0x10cc36 part30 = true := by
  rw [InstructionTrace.ordered_eq_layout, part30_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part30_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xcc36 176 = part30Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
