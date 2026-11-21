import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part22 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c64b 0xca rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c64d 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c64f 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c652 5 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c659 0xd5 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c65b 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c65e 0x41 0xc1 0x15 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c662 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c665 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c667 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c66a 0x44 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c66d 0x45 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c670 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c673 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c676 0x45 0xe1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c679 0x41 0xef (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c67c 0x45 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10c67f 0x46 (by simp [RexNoWPrefix]) 1 (.sib 1 (some 15) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_rex_effect_step 0x10c683 0x41 0xc1 0xb00327c8 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c68a 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c68d 0xc1 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c690 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c693 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c696 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c698 0x44 0xf1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c69b 0xc1 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10c69e 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10c6a0 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c6a5 0x45 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c6a8 0x45 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c6ab 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c6ae 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10c6b1 0x44 0xf6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c6b4 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c6b7 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c6ba 0x41 0xc2 0xf (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10c6be 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c6c0 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c6c2 0xc1 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c6c5 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c6c8 0x41 0xeb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c6cb 0x41 0xc3 0x19 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c6cf 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c6d2 0x41 0xe9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c6d5 0x41 0xc1 0xe (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c6d9 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c6dc 0x45 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c6df 0x41 0xea (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c6e2 0x41 0xea 0x3 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c6e6 0x45 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m32_r32_effect_step 0x10c6e9 0 (.sib 4 none 0 (.d8 12)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c6ed 0x41 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m32_r32_effect_step 0x10c6f0 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c6f4 0x41 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_rex_effect_step 0x10c6f7 0x41 0xe9 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c6fb 0x41 0xda (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c6fe 0x41 0xc2 0x1a (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10c702 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10c705 0xd9 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10c707 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10c70a 0 (.sib 4 none 0 (.d8 100)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10c70e 0x44 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10c711 0x41 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10c714 0x41 0xc1 0x7 (by simp [RexNoWPrefix]) rfl rfl) (by x86_local)]

def part22Bytes : List UInt8 :=
  [0x31,0xca,0x89,0xf9,0xc1,0xc1,0x1a,0x8b,0xac,0x24,0x88,0x0,0x0,0x0,0x1,0xd5,0x41,0x89,0xf9,0x41,0xc1,0xc1,0x15,0x41,0x31,0xc9,0x89,0xf9,0xc1,0xc1,0x7,0x44,0x31,0xc9,0x45,0x89,0xe9,0x45,0x31,0xe1,0x41,0x21,0xf9,0x45,0x31,0xe1,0x41,0x1,0xef,0x45,0x1,0xcf,0x46,0x8d,0xc,0x39,0x41,0x81,0xc1,0xc8,0x27,0x3,0xb0,0x44,0x89,0xf1,0xc1,0xc1,0x1e,0x44,0x89,0xf6,0xc1,0xc6,0x13,0x31,0xce,0x44,0x89,0xf1,0xc1,0xc1,0xa,0x31,0xf1,0x4c,0x8b,0x7c,0x24,0x28,0x45,0x89,0xfa,0x45,0x21,0xc2,0x44,0x89,0xfe,0x44,0x31,0xc6,0x44,0x21,0xf6,0x44,0x31,0xd6,0x41,0x89,0xc2,0x41,0xc1,0xc2,0xf,0x1,0xce,0x89,0xc1,0xc1,0xc1,0xd,0x44,0x1,0xcb,0x41,0x89,0xeb,0x41,0xc1,0xc3,0x19,0x44,0x1,0xce,0x41,0x89,0xe9,0x41,0xc1,0xc1,0xe,0x44,0x31,0xd1,0x45,0x31,0xd9,0x41,0x89,0xea,0x41,0xc1,0xea,0x3,0x45,0x31,0xca,0x1,0x44,0x24,0xc,0x41,0x1,0xc2,0x44,0x89,0x14,0x24,0x41,0x89,0xc1,0x41,0xc1,0xe9,0xa,0x41,0x89,0xda,0x41,0xc1,0xc2,0x1a,0x41,0x31,0xc9,0x89,0xd9,0xc1,0xc1,0x15,0x8b,0x44,0x24,0x64,0x44,0x1,0xc8,0x41,0x89,0xd9,0x41,0xc1,0xc1,0x7]

set_option maxRecDepth 4096 in
theorem part22_bytes [Bindings] : part22.flatMap CheckedInstruction.bytes = part22Bytes  := by
  rfl

def part22Layout : List (BitVec 64 × Nat) :=
  [(0x10c64b, 2), (0x10c64d, 2), (0x10c64f, 3), (0x10c652, 7), (0x10c659, 2), (0x10c65b, 3), (0x10c65e, 4), (0x10c662, 3), (0x10c665, 2), (0x10c667, 3), (0x10c66a, 3), (0x10c66d, 3), (0x10c670, 3), (0x10c673, 3), (0x10c676, 3), (0x10c679, 3), (0x10c67c, 3), (0x10c67f, 4), (0x10c683, 7), (0x10c68a, 3), (0x10c68d, 3), (0x10c690, 3), (0x10c693, 3), (0x10c696, 2), (0x10c698, 3), (0x10c69b, 3), (0x10c69e, 2), (0x10c6a0, 5), (0x10c6a5, 3), (0x10c6a8, 3), (0x10c6ab, 3), (0x10c6ae, 3), (0x10c6b1, 3), (0x10c6b4, 3), (0x10c6b7, 3), (0x10c6ba, 4), (0x10c6be, 2), (0x10c6c0, 2), (0x10c6c2, 3), (0x10c6c5, 3), (0x10c6c8, 3), (0x10c6cb, 4), (0x10c6cf, 3), (0x10c6d2, 3), (0x10c6d5, 4), (0x10c6d9, 3), (0x10c6dc, 3), (0x10c6df, 3), (0x10c6e2, 4), (0x10c6e6, 3), (0x10c6e9, 4), (0x10c6ed, 3), (0x10c6f0, 4), (0x10c6f4, 3), (0x10c6f7, 4), (0x10c6fb, 3), (0x10c6fe, 4), (0x10c702, 3), (0x10c705, 2), (0x10c707, 3), (0x10c70a, 4), (0x10c70e, 3), (0x10c711, 3), (0x10c714, 4)]

theorem part22_layout [Bindings] : InstructionTrace.layout part22 = part22Layout := by
  rfl

theorem part22_ordered [Bindings] : InstructionTrace.ordered 0x10c64b part22 = true := by
  rw [InstructionTrace.ordered_eq_layout, part22_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part22_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xc64b 205 = part22Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
