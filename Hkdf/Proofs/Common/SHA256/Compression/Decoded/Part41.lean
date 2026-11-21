import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu
import Hkdf.Proofs.Common.SHA256.Compression.Accumulator

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part41 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b56f 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b571 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b574 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b577 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b57a 0xcb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b57c 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b57e 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b581 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b584 0xd8 rfl) (by x86_local),
    CheckedInstruction.register (add_eax_imm32_effect_step 0x10b586 0x19a4c116) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b58b 0x44 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b58e 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b591 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b593 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b596 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b599 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b59b 0x44 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b59e 0x44 0xe7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b5a1 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b5a4 0x44 0xe3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b5a7 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b5aa 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b5ac 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b5ae 0x41 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b5b1 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b5b4 0xc6 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b5b7 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b5b9 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b5bc 0x41 0xc3 0xd (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b5c0 0x41 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5c3 0xca rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b5c5 0xc2 0x19 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5c8 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b5ca 0xc0 0xe rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b5cd 0xd0 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10b5cf 1 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5d3 0xcf rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5d5 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5d7 0xca rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10b5d9 0xe9 0x3 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b5dc 0xc1 rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_rex_effect_step 0x10b5de 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b5e3 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b5e6 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10b5eb 0x41 0xea 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b5ef 0x45 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b5f2 5 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b5f6 0x44 0xd5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b5f9 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b5fc 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b5ff 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b602 0x41 0xc3 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b606 0x41 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b609 0x44 0xe8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b60c 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b60f 0x44 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b612 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10b615 0x4c (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b61a 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b61d 0x45 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b620 0x45 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b623 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b626 0x45 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b629 0x41 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part41Bytes : List UInt8 :=
  [0x89,0xd6,0x44,0x31,0xfe,0x44,0x21,0xce,0x44,0x31,0xfe,0x1,0xcb,0x1,0xf3,0x44,0x89,0xc6,0xc1,0xc6,0x1e,0x1,0xd8,0x5,0x16,0xc1,0xa4,0x19,0x44,0x89,0xc7,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xc6,0xc1,0xc6,0xa,0x31,0xfe,0x44,0x89,0xf7,0x44,0x21,0xe7,0x44,0x89,0xf3,0x44,0x31,0xe3,0x44,0x21,0xc3,0x31,0xfb,0x1,0xf3,0x41,0x1,0xc5,0x44,0x89,0xd6,0xc1,0xc6,0xf,0x1,0xc3,0x45,0x89,0xd3,0x41,0xc1,0xc3,0xd,0x41,0x31,0xf3,0x89,0xca,0xc1,0xc2,0x19,0x89,0xc8,0xc1,0xc0,0xe,0x31,0xd0,0x1,0x4c,0x24,0x70,0x89,0xcf,0x89,0xce,0x89,0xca,0xc1,0xe9,0x3,0x31,0xc1,0x44,0x1,0x54,0x24,0x48,0x44,0x1,0xd1,0x48,0x89,0x4c,0x24,0x28,0x41,0xc1,0xea,0xa,0x45,0x31,0xda,0x8b,0x6c,0x24,0xc,0x44,0x1,0xd5,0x44,0x89,0xe8,0xc1,0xc0,0x1a,0x45,0x89,0xeb,0x41,0xc1,0xc3,0x15,0x41,0x31,0xc3,0x44,0x89,0xe8,0xc1,0xc0,0x7,0x44,0x31,0xd8,0x45,0x89,0xcb,0x4c,0x8b,0x54,0x24,0x38,0x45,0x31,0xd3,0x45,0x21,0xeb,0x45,0x31,0xd3,0x41,0x1,0xef,0x45,0x1,0xdf,0x41,0x89,0xdb]

set_option maxRecDepth 4096 in
theorem part41_bytes [Bindings] : part41.flatMap CheckedInstruction.bytes = part41Bytes  := by
  rfl

def part41Layout : List (BitVec 64 × Nat) :=
  [(0x10b56f, 2), (0x10b571, 3), (0x10b574, 3), (0x10b577, 3), (0x10b57a, 2), (0x10b57c, 2), (0x10b57e, 3), (0x10b581, 3), (0x10b584, 2), (0x10b586, 5), (0x10b58b, 3), (0x10b58e, 3), (0x10b591, 2), (0x10b593, 3), (0x10b596, 3), (0x10b599, 2), (0x10b59b, 3), (0x10b59e, 3), (0x10b5a1, 3), (0x10b5a4, 3), (0x10b5a7, 3), (0x10b5aa, 2), (0x10b5ac, 2), (0x10b5ae, 3), (0x10b5b1, 3), (0x10b5b4, 3), (0x10b5b7, 2), (0x10b5b9, 3), (0x10b5bc, 4), (0x10b5c0, 3), (0x10b5c3, 2), (0x10b5c5, 3), (0x10b5c8, 2), (0x10b5ca, 3), (0x10b5cd, 2), (0x10b5cf, 4), (0x10b5d3, 2), (0x10b5d5, 2), (0x10b5d7, 2), (0x10b5d9, 3), (0x10b5dc, 2), (0x10b5de, 5), (0x10b5e3, 3), (0x10b5e6, 5), (0x10b5eb, 4), (0x10b5ef, 3), (0x10b5f2, 4), (0x10b5f6, 3), (0x10b5f9, 3), (0x10b5fc, 3), (0x10b5ff, 3), (0x10b602, 4), (0x10b606, 3), (0x10b609, 3), (0x10b60c, 3), (0x10b60f, 3), (0x10b612, 3), (0x10b615, 5), (0x10b61a, 3), (0x10b61d, 3), (0x10b620, 3), (0x10b623, 3), (0x10b626, 3), (0x10b629, 3)]

theorem part41_layout [Bindings] : InstructionTrace.layout part41 = part41Layout := by
  rfl

theorem part41_ordered [Bindings] : InstructionTrace.ordered 0x10b56f part41 = true := by
  rw [InstructionTrace.ordered_eq_layout, part41_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part41_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0xb56f 189 = part41Bytes := by
  rfl

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
