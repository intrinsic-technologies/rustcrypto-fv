import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part07 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10ba90 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ba92 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10ba95 0x41 0xc7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ba98 0x45 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10ba9b 0x41 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10ba9e 0x41 0xdf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10baa1 0x41 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10baa4 0x41 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10baa7 0x41 0xcf (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10baaa 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10baad 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bab0 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bab3 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bab6 0xce rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bab8 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10babb 0xc1 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10babe 0xf1 rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bac0 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bac5 3 (.base 6 (.d8 44)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10bac8 3) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10baca 3 (.sib 4 none 0 (.d8 52)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bace 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bad1 0x44 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bad4 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bad6 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bad8 0x44 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10badb 0xd6 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10badd 0x44 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bae0 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bae2 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bae5 0xc6 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bae8 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10baea 0xc1 0x550c7dc3 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10baf0 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10baf3 0xc7 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10baf6 0xf7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10baf8 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bafb 0xc6 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bafe 0xfe rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb00 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10bb02 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10bb04 0xd3 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bb06 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bb08 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bb0b 0xfb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bb0d 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb0f 0x41 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb12 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb15 0xc6 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10bb18 0xcb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb1a 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb1d 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bb20 0xf1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb22 0x44 0xd6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10bb25 0xc6 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10bb28 0xce rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10bb2a 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10bb2f 7 (.base 1 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10bb32 7) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10bb34 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10bb37 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10bb3a 0x44 0xd9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb3d 0x41 0xf9 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10bb40 0x41 0xc9 (by simp [RexNoWPrefix]) rfl) (by x86_local)]

def part07Bytes : List UInt8 :=
  [0x89,0xc3,0x44,0x21,0xd3,0x41,0x89,0xc7,0x45,0x31,0xd7,0x41,0x21,0xd7,0x41,0x31,0xdf,0x41,0x1,0xf7,0x41,0x1,0xcb,0x41,0x1,0xcf,0x44,0x89,0xd9,0xc1,0xc1,0x1a,0x44,0x89,0xde,0xc1,0xc6,0x15,0x31,0xce,0x44,0x89,0xd9,0xc1,0xc1,0x7,0x31,0xf1,0x48,0x8b,0x74,0x24,0x18,0x8b,0x5e,0x2c,0xf,0xcb,0x89,0x5c,0x24,0x34,0x44,0x89,0xde,0x44,0x21,0xc6,0x1,0xdf,0x1,0xf7,0x44,0x89,0xde,0xf7,0xd6,0x44,0x21,0xce,0x1,0xf7,0x44,0x89,0xfe,0xc1,0xc6,0x1e,0x1,0xf9,0x81,0xc1,0xc3,0x7d,0xc,0x55,0x44,0x89,0xff,0xc1,0xc7,0x13,0x31,0xf7,0x44,0x89,0xfe,0xc1,0xc6,0xa,0x31,0xfe,0x89,0xd7,0x21,0xc7,0x89,0xd3,0x31,0xc3,0x44,0x21,0xfb,0x31,0xfb,0x1,0xf3,0x41,0x1,0xca,0x44,0x89,0xd6,0xc1,0xc6,0x1a,0x1,0xcb,0x44,0x89,0xd1,0xc1,0xc1,0x15,0x31,0xf1,0x44,0x89,0xd6,0xc1,0xc6,0x7,0x31,0xce,0x48,0x8b,0x4c,0x24,0x18,0x8b,0x79,0x30,0xf,0xcf,0x89,0x3c,0x24,0x44,0x89,0xd1,0x44,0x21,0xd9,0x41,0x1,0xf9,0x41,0x1,0xc9]

set_option maxRecDepth 4096 in
theorem part07_bytes [Bindings] : part07.flatMap CheckedInstruction.bytes = part07Bytes  := by
  rfl

def part07Layout : List (BitVec 64 × Nat) :=
  [(0x10ba90, 2), (0x10ba92, 3), (0x10ba95, 3), (0x10ba98, 3), (0x10ba9b, 3), (0x10ba9e, 3), (0x10baa1, 3), (0x10baa4, 3), (0x10baa7, 3), (0x10baaa, 3), (0x10baad, 3), (0x10bab0, 3), (0x10bab3, 3), (0x10bab6, 2), (0x10bab8, 3), (0x10babb, 3), (0x10babe, 2), (0x10bac0, 5), (0x10bac5, 3), (0x10bac8, 2), (0x10baca, 4), (0x10bace, 3), (0x10bad1, 3), (0x10bad4, 2), (0x10bad6, 2), (0x10bad8, 3), (0x10badb, 2), (0x10badd, 3), (0x10bae0, 2), (0x10bae2, 3), (0x10bae5, 3), (0x10bae8, 2), (0x10baea, 6), (0x10baf0, 3), (0x10baf3, 3), (0x10baf6, 2), (0x10baf8, 3), (0x10bafb, 3), (0x10bafe, 2), (0x10bb00, 2), (0x10bb02, 2), (0x10bb04, 2), (0x10bb06, 2), (0x10bb08, 3), (0x10bb0b, 2), (0x10bb0d, 2), (0x10bb0f, 3), (0x10bb12, 3), (0x10bb15, 3), (0x10bb18, 2), (0x10bb1a, 3), (0x10bb1d, 3), (0x10bb20, 2), (0x10bb22, 3), (0x10bb25, 3), (0x10bb28, 2), (0x10bb2a, 5), (0x10bb2f, 3), (0x10bb32, 2), (0x10bb34, 3), (0x10bb37, 3), (0x10bb3a, 3), (0x10bb3d, 3), (0x10bb40, 3)]

theorem part07_layout [Bindings] : InstructionTrace.layout part07 = part07Layout := by
  rfl

theorem part07_ordered [Bindings] : InstructionTrace.ordered 0x10ba90 part07 = true := by
  rw [InstructionTrace.ordered_eq_layout, part07_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part07_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xba90 179 = part07Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
