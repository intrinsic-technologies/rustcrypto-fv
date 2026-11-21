import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part21 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c574 0x41 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c577 0x41 0xc3 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c57b 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c57e 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c581 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c585 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10c588 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c58d 0x45 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10c590 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c595 0x41 0xee 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c599 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c59c 0 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c59f 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c5a2 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c5a5 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c5a8 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c5ab 0x41 0xc2 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c5af 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c5b2 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c5b5 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c5b8 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c5bb 0x45 0xe2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c5be 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c5c1 0x45 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c5c4 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c5c7 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c5ca 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c5cd 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c5d1 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c5d4 0x41 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c5d7 0x41 0xc2 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10c5db 0x42 (by simp [RexNoWPrefix]) 5 (.sib 1 (some 9) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10c5df 0xc5 0xa831c66d rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c5e5 0xf1 rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10c5e7 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c5ec 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c5ef 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c5f2 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c5f5 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c5f8 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c5fb 0x45 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c5fe 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c601 0x41 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c604 0x45 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c607 0x41 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c60a 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c60d 0x41 0xc2 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c611 0xef rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c613 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c615 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c618 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c61b 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c61e 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c622 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c625 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c628 0x41 0xc2 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c62c 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c62f 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c632 0x41 0xe9 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c636 0x45 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c639 2 (.sib 4 none 0 (.d32 140)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c640 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10c643 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10c648 0xea 0xa rfl rfl) (by x86_local)]

def part21Bytes : List UInt8 :=
  [0x41,0x89,0xd3,0x41,0xc1,0xc3,0xe,0x45,0x31,0xd3,0x41,0x89,0xd2,0x41,0xc1,0xea,0x3,0x45,0x31,0xda,0x44,0x1,0x74,0x24,0x4,0x45,0x1,0xf2,0x44,0x89,0x54,0x24,0x48,0x41,0xc1,0xee,0xa,0x41,0x31,0xce,0x8b,0x4,0x24,0x44,0x1,0xf0,0x44,0x89,0xe9,0xc1,0xc1,0x1a,0x45,0x89,0xea,0x41,0xc1,0xc2,0x15,0x41,0x31,0xca,0x44,0x89,0xe9,0xc1,0xc1,0x7,0x44,0x31,0xd1,0x45,0x89,0xe2,0x45,0x31,0xfa,0x45,0x21,0xea,0x45,0x31,0xfa,0x41,0x1,0xc1,0x41,0x89,0xf3,0x41,0xc1,0xc3,0x1e,0x45,0x1,0xd1,0x41,0x89,0xf2,0x41,0xc1,0xc2,0x13,0x42,0x8d,0x2c,0x9,0x81,0xc5,0x6d,0xc6,0x31,0xa8,0x89,0xf1,0x48,0x89,0x74,0x24,0x28,0xc1,0xc1,0xa,0x45,0x31,0xda,0x44,0x31,0xd1,0x45,0x89,0xc2,0x41,0x21,0xda,0x45,0x89,0xc6,0x41,0x31,0xde,0x41,0x21,0xf6,0x45,0x31,0xd6,0x41,0x1,0xce,0x41,0x89,0xd2,0x41,0xc1,0xc2,0xf,0x1,0xef,0x89,0xd1,0xc1,0xc1,0xd,0x41,0x1,0xee,0x41,0x89,0xc3,0x41,0xc1,0xc3,0x19,0x44,0x31,0xd1,0x41,0x89,0xc2,0x41,0xc1,0xc2,0xe,0x45,0x31,0xda,0x41,0x89,0xc1,0x41,0xc1,0xe9,0x3,0x45,0x31,0xd1,0x1,0x94,0x24,0x8c,0x0,0x0,0x0,0x41,0x1,0xd1,0x44,0x89,0x4c,0x24,0x70,0xc1,0xea,0xa]

set_option maxRecDepth 4096 in
theorem part21_bytes [Bindings] : part21.flatMap CheckedInstruction.bytes = part21Bytes  := by
  rfl

def part21Layout : List (BitVec 64 × Nat) :=
  [(0x10c574, 3), (0x10c577, 4), (0x10c57b, 3), (0x10c57e, 3), (0x10c581, 4), (0x10c585, 3), (0x10c588, 5), (0x10c58d, 3), (0x10c590, 5), (0x10c595, 4), (0x10c599, 3), (0x10c59c, 3), (0x10c59f, 3), (0x10c5a2, 3), (0x10c5a5, 3), (0x10c5a8, 3), (0x10c5ab, 4), (0x10c5af, 3), (0x10c5b2, 3), (0x10c5b5, 3), (0x10c5b8, 3), (0x10c5bb, 3), (0x10c5be, 3), (0x10c5c1, 3), (0x10c5c4, 3), (0x10c5c7, 3), (0x10c5ca, 3), (0x10c5cd, 4), (0x10c5d1, 3), (0x10c5d4, 3), (0x10c5d7, 4), (0x10c5db, 4), (0x10c5df, 6), (0x10c5e5, 2), (0x10c5e7, 5), (0x10c5ec, 3), (0x10c5ef, 3), (0x10c5f2, 3), (0x10c5f5, 3), (0x10c5f8, 3), (0x10c5fb, 3), (0x10c5fe, 3), (0x10c601, 3), (0x10c604, 3), (0x10c607, 3), (0x10c60a, 3), (0x10c60d, 4), (0x10c611, 2), (0x10c613, 2), (0x10c615, 3), (0x10c618, 3), (0x10c61b, 3), (0x10c61e, 4), (0x10c622, 3), (0x10c625, 3), (0x10c628, 4), (0x10c62c, 3), (0x10c62f, 3), (0x10c632, 4), (0x10c636, 3), (0x10c639, 7), (0x10c640, 3), (0x10c643, 5), (0x10c648, 3)]

theorem part21_layout [Bindings] : InstructionTrace.layout part21 = part21Layout := by
  rfl

theorem part21_ordered [Bindings] : InstructionTrace.ordered 0x10c574 part21 = true := by
  rw [InstructionTrace.ordered_eq_layout, part21_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part21_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc574 215 = part21Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
