import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu
import Sha2.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part42 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d54c 0x41 0xc3 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10d550 0x42 (by simp [RexNoWPrefix]) 1 (.sib 0 (some 15) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10d554 0xc1 0x1e376c08 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d55a 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10d55d 0x41 0xc7 0x13 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d561 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d564 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d566 0xc0 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d569 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d56c 0x45 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d56f 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d572 0x45 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d575 0x45 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d578 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d57b 0x45 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d57e 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d581 0x41 0xcc (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d584 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d587 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d58a 0xc6 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d58d 0xfe rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10d58f 0xea 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d592 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d594 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d597 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10d59a 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d59e 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d5a0 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d5a3 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d5a6 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d5a8 0x44 0xe0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d5ab 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d5ae 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d5b0 0x44 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d5b3 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d5b6 0x44 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d5b9 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10d5bc 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d5bf 0xf2 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d5c1 0xca rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10d5c3 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10d5c5 0x2748774c) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d5ca 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d5cd 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d5d0 0x44 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d5d3 0xc2 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d5d6 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d5d8 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d5db 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d5de 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d5e0 0xda rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d5e2 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10d5e5 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d5e8 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10d5eb 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10d5ee 0x41 0xd2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d5f1 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d5f4 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10d5f7 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d5fa 0xe8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d5fc 0xc0 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10d5ff 0xe9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10d601 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10d604 0xc1 rfl) (by x86_local)]

def part42Bytes : List UInt8 :=
  [0x41,0xc1,0xc3,0x1e,0x42,0x8d,0xc,0x38,0x81,0xc1,0x8,0x6c,0x37,0x1e,0x41,0x89,0xdf,0x41,0xc1,0xc7,0x13,0x45,0x31,0xdf,0x89,0xd8,0xc1,0xc0,0xa,0x44,0x31,0xf8,0x45,0x89,0xc7,0x45,0x21,0xf7,0x45,0x89,0xc3,0x45,0x31,0xf3,0x41,0x21,0xdb,0x45,0x31,0xfb,0x41,0x1,0xc3,0x41,0x1,0xcc,0x41,0x1,0xcb,0xc1,0xc7,0xf,0xc1,0xc6,0xd,0x31,0xfe,0xc1,0xea,0xa,0x31,0xf2,0x44,0x89,0xe0,0xc1,0xc0,0x1a,0x8b,0x74,0x24,0x8,0x1,0xd6,0x44,0x89,0xe1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xe0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xe9,0x44,0x31,0xc9,0x44,0x21,0xe1,0x44,0x31,0xc9,0x4c,0x89,0xd2,0x1,0xf2,0x1,0xca,0x1,0xd0,0x5,0x4c,0x77,0x48,0x27,0x44,0x89,0xd9,0xc1,0xc1,0x1e,0x44,0x89,0xda,0xc1,0xc2,0x13,0x31,0xca,0x44,0x89,0xd9,0xc1,0xc1,0xa,0x31,0xd1,0x89,0xda,0x44,0x21,0xc2,0x41,0x89,0xda,0x45,0x31,0xc2,0x45,0x21,0xda,0x41,0x31,0xd2,0x41,0x1,0xca,0x41,0x1,0xc6,0x41,0x1,0xc2,0x89,0xe8,0xc1,0xc0,0xf,0x89,0xe9,0xc1,0xc1,0xd,0x31,0xc1]

set_option maxRecDepth 4096 in
theorem part42_bytes [Bindings] : part42.flatMap CheckedInstruction.bytes = part42Bytes  := by
  rfl

def part42Layout : List (BitVec 64 × Nat) :=
  [(0x10d54c, 4), (0x10d550, 4), (0x10d554, 6), (0x10d55a, 3), (0x10d55d, 4), (0x10d561, 3), (0x10d564, 2), (0x10d566, 3), (0x10d569, 3), (0x10d56c, 3), (0x10d56f, 3), (0x10d572, 3), (0x10d575, 3), (0x10d578, 3), (0x10d57b, 3), (0x10d57e, 3), (0x10d581, 3), (0x10d584, 3), (0x10d587, 3), (0x10d58a, 3), (0x10d58d, 2), (0x10d58f, 3), (0x10d592, 2), (0x10d594, 3), (0x10d597, 3), (0x10d59a, 4), (0x10d59e, 2), (0x10d5a0, 3), (0x10d5a3, 3), (0x10d5a6, 2), (0x10d5a8, 3), (0x10d5ab, 3), (0x10d5ae, 2), (0x10d5b0, 3), (0x10d5b3, 3), (0x10d5b6, 3), (0x10d5b9, 3), (0x10d5bc, 3), (0x10d5bf, 2), (0x10d5c1, 2), (0x10d5c3, 2), (0x10d5c5, 5), (0x10d5ca, 3), (0x10d5cd, 3), (0x10d5d0, 3), (0x10d5d3, 3), (0x10d5d6, 2), (0x10d5d8, 3), (0x10d5db, 3), (0x10d5de, 2), (0x10d5e0, 2), (0x10d5e2, 3), (0x10d5e5, 3), (0x10d5e8, 3), (0x10d5eb, 3), (0x10d5ee, 3), (0x10d5f1, 3), (0x10d5f4, 3), (0x10d5f7, 3), (0x10d5fa, 2), (0x10d5fc, 3), (0x10d5ff, 2), (0x10d601, 3), (0x10d604, 2)]

theorem part42_layout [Bindings] : InstructionTrace.layout part42 = part42Layout := by
  rfl

theorem part42_ordered [Bindings] : InstructionTrace.ordered 0x10d54c part42 = true := by
  rw [InstructionTrace.ordered_eq_layout, part42_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part42_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xd54c 186 = part42Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
