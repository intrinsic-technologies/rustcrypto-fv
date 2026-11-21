import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.SHA256.Compression.Layout
import Hkdf.Proofs.Common.SHA256.Compression.Bswap32
import Hkdf.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Instructions

def part00 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109610 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109615 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109618 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10961b 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10961e 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 280)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109626 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109629 0xcf rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10962b 1 (.sib 4 none 0 (.d32 188)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109632 0 (.base 6 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x109634 1 (.base 6 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x109637 0) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x109639 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (bswap_r32_effect_step 0x10963c 1) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10963e 0x49 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109641 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109646 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109649 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10964c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10964f 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x109652 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109654 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x109657 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10965a 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10965c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10965f 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109662 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x109665 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x109667 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10966a 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 272)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109672 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109674 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109676 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109678 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10967a 0xda rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10967c 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10967f 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x109682 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x109687 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x109689 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10968b 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10968e 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x109690 0xc7 0x428a2f98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x109696 0x4d 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x109699 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10969c 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1096a0 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1096a2 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1096a5 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x1096a8 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x1096ab 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x1096ad 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x1096b0 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1096b3 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 264)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x1096bb 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x1096bd 0x41 (by simp [RexNoWPrefix]) 2 (.sib 11 (some 1) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x1096c1 0xc2 0x428a2f98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1096c7 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1096c9 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x1096cc 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1096cf 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1096d1 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x1096d4 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x1096d6 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x1096d8 0xc7 0x7 rfl rfl) (by x86_local)]

def part00Bytes : List UInt8 :=
  [0x48,0x89,0x74,0x24,0x18,0x45,0x89,0xf7,0x41,0x89,0xc6,0x45,0x89,0xcb,0x4c,0x89,0x9c,0x24,0x18,0x1,0x0,0x0,0x41,0x89,0xd1,0x89,0xcf,0x89,0x8c,0x24,0xbc,0x0,0x0,0x0,0x8b,0x6,0x8b,0x4e,0x4,0xf,0xc8,0x48,0x89,0xc6,0xf,0xc9,0x49,0x89,0xcd,0x48,0x89,0x4c,0x24,0x38,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xc1,0x44,0x21,0xd1,0x44,0x89,0xc2,0xf7,0xd2,0x44,0x21,0xca,0x4c,0x89,0x8c,0x24,0x10,0x1,0x0,0x0,0x1,0xf9,0x1,0xd1,0x1,0xc1,0x89,0xc8,0x89,0xda,0xc1,0xc2,0x1e,0x48,0x89,0xf7,0x48,0x89,0x74,0x24,0x50,0x1,0xf9,0x89,0xde,0xc1,0xc6,0x13,0x1,0xc7,0x81,0xc7,0x98,0x2f,0x8a,0x42,0x4d,0x89,0xc4,0x41,0x89,0xd8,0x41,0xc1,0xc0,0xa,0x31,0xd6,0x41,0x31,0xf0,0x44,0x89,0xfa,0x44,0x31,0xf2,0x21,0xda,0x44,0x89,0xf8,0x44,0x21,0xf0,0x4c,0x89,0xb4,0x24,0x8,0x1,0x0,0x0,0x31,0xd0,0x41,0x8d,0x14,0xb,0x81,0xc2,0x98,0x2f,0x8a,0x42,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x1,0xc0,0x89,0xd6,0xc1,0xc6,0x15,0x1,0xf8,0x89,0xd7,0xc1,0xc7,0x7]

set_option maxRecDepth 4096 in
theorem part00_bytes [Bindings] : part00.flatMap CheckedInstruction.bytes = part00Bytes  := by
  rfl

def part00Layout : List (BitVec 64 × Nat) :=
  [(0x109610, 5), (0x109615, 3), (0x109618, 3), (0x10961b, 3), (0x10961e, 8), (0x109626, 3), (0x109629, 2), (0x10962b, 7), (0x109632, 2), (0x109634, 3), (0x109637, 2), (0x109639, 3), (0x10963c, 2), (0x10963e, 3), (0x109641, 5), (0x109646, 3), (0x109649, 3), (0x10964c, 3), (0x10964f, 3), (0x109652, 2), (0x109654, 3), (0x109657, 3), (0x10965a, 2), (0x10965c, 3), (0x10965f, 3), (0x109662, 3), (0x109665, 2), (0x109667, 3), (0x10966a, 8), (0x109672, 2), (0x109674, 2), (0x109676, 2), (0x109678, 2), (0x10967a, 2), (0x10967c, 3), (0x10967f, 3), (0x109682, 5), (0x109687, 2), (0x109689, 2), (0x10968b, 3), (0x10968e, 2), (0x109690, 6), (0x109696, 3), (0x109699, 3), (0x10969c, 4), (0x1096a0, 2), (0x1096a2, 3), (0x1096a5, 3), (0x1096a8, 3), (0x1096ab, 2), (0x1096ad, 3), (0x1096b0, 3), (0x1096b3, 8), (0x1096bb, 2), (0x1096bd, 4), (0x1096c1, 6), (0x1096c7, 2), (0x1096c9, 3), (0x1096cc, 3), (0x1096cf, 2), (0x1096d1, 3), (0x1096d4, 2), (0x1096d6, 2), (0x1096d8, 3)]

theorem part00_layout [Bindings] : InstructionTrace.layout part00 = part00Layout := by
  rfl

theorem part00_ordered [Bindings] : InstructionTrace.ordered 0x109610 part00 = true := by
  rw [InstructionTrace.ordered_eq_layout, part00_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part00_source : Hkdf.Spec.Program.Extracted.textBytes.toListFrom 0x9610 203 = part00Bytes := by
  decide +kernel

end Hkdf.Proofs.Common.SHA256.Compression.Decoded
