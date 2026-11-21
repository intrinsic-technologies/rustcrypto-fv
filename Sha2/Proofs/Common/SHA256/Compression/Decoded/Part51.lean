import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part51 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dbce 0xc5 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10dbd1 0xdd rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dbd3 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10dbd6 0x44 0xdb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dbd9 0x45 0xce (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dbdc 0x45 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10dbdf 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dbe2 0x41 0xde (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dbe5 0x41 0xee (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dbe8 0x41 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dbeb 0x41 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dbee 0x44 0xfe (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dbf1 0x44 0xff (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dbf4 0xc7 0xf rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dbf7 0x44 0xfb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dbfa 0xc3 0xd rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10dbfd 0xfb rfl) (by x86_local),
    CheckedInstruction.register (shr_r32_imm8_effect_step 0x10dbff 0xee 0xa rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10dc02 0xde rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dc04 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dc07 0xc7 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dc0a 0x44 0xd3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dc0d 0xc3 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10dc10 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dc12 0x44 0xd7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dc15 0xc7 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10dc18 0xdf rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10dc1a 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10dc1f 0xf3 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dc21 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dc24 0x41 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dc27 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10dc2a 0x45 0xd0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dc2d 0x41 0xc8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dc30 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10dc33 0xdf rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10dc35 0xc7 0xc67178f2 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dc3b 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10dc3e 0x41 0xc0 0x1e (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dc42 0x44 0xf3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10dc45 0xc3 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dc48 0x44 0xc3 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dc4b 0x45 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10dc4e 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dc52 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10dc55 0xc3 rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10dc57 0x44 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10dc5a 0xc5 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10dc5c 0x44 0xcd (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10dc5f 0x44 0xf5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10dc62 0xdd rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_effect_step 0x10dc64 5 (.sib 4 none 0 (.d32 232)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dc6b 0x44 0xc5 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10dc6e 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10dc73 0x44 (by simp [RexNoWPrefix]) 6 (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_effect_step 0x10dc7b 0 (.sib 4 none 0 (.d32 264)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10dc82 0x44 (by simp [RexNoWPrefix]) 1 (.sib 4 none 0 (.d32 280)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10dc8a 0x44 (by simp [RexNoWPrefix]) 3 (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10dc92 0xeb rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10dc94 0xfb rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10dc96 0x45 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10dc99 0x41 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r32_m32_rex_effect_step 0x10dc9c 0x44 (by simp [RexNoWPrefix]) 2 (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r32_m32_effect_step 0x10dca4 2 (.sib 4 none 0 (.d32 272)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)]

def part51Bytes : List UInt8 :=
  [0xc1,0xc5,0xa,0x31,0xdd,0x44,0x89,0xcb,0x44,0x21,0xdb,0x45,0x89,0xce,0x45,0x31,0xde,0x41,0x21,0xc6,0x41,0x31,0xde,0x41,0x1,0xee,0x41,0x1,0xfa,0x41,0x1,0xfe,0x44,0x89,0xfe,0x44,0x89,0xff,0xc1,0xc7,0xf,0x44,0x89,0xfb,0xc1,0xc3,0xd,0x31,0xfb,0xc1,0xee,0xa,0x31,0xde,0x44,0x89,0xd7,0xc1,0xc7,0x1a,0x44,0x89,0xd3,0xc1,0xc3,0x15,0x31,0xfb,0x44,0x89,0xd7,0xc1,0xc7,0x7,0x31,0xdf,0x48,0x8b,0x5c,0x24,0x28,0x1,0xf3,0x44,0x1,0xc3,0x41,0x89,0xd0,0x41,0x31,0xc8,0x45,0x21,0xd0,0x41,0x31,0xc8,0x44,0x1,0xc3,0x1,0xdf,0x81,0xc7,0xf2,0x78,0x71,0xc6,0x45,0x89,0xf0,0x41,0xc1,0xc0,0x1e,0x44,0x89,0xf3,0xc1,0xc3,0x13,0x44,0x31,0xc3,0x45,0x89,0xf0,0x41,0xc1,0xc0,0xa,0x41,0x31,0xd8,0x89,0xc3,0x44,0x21,0xcb,0x89,0xc5,0x44,0x31,0xcd,0x44,0x21,0xf5,0x31,0xdd,0x3,0xac,0x24,0xe8,0x0,0x0,0x0,0x44,0x1,0xc5,0x48,0x8b,0x74,0x24,0x18,0x44,0x3,0xb4,0x24,0xf8,0x0,0x0,0x0,0x3,0x84,0x24,0x8,0x1,0x0,0x0,0x44,0x3,0x8c,0x24,0x18,0x1,0x0,0x0,0x44,0x3,0x9c,0x24,0xf0,0x0,0x0,0x0,0x89,0xeb,0x1,0xfb,0x45,0x89,0xd8,0x41,0x1,0xf8,0x44,0x3,0x94,0x24,0x0,0x1,0x0,0x0,0x3,0x94,0x24,0x10,0x1,0x0,0x0]

set_option maxRecDepth 4096 in
theorem part51_bytes [Bindings] : part51.flatMap CheckedInstruction.bytes = part51Bytes  := by
  rfl

def part51Layout : List (BitVec 64 × Nat) :=
  [(0x10dbce, 3), (0x10dbd1, 2), (0x10dbd3, 3), (0x10dbd6, 3), (0x10dbd9, 3), (0x10dbdc, 3), (0x10dbdf, 3), (0x10dbe2, 3), (0x10dbe5, 3), (0x10dbe8, 3), (0x10dbeb, 3), (0x10dbee, 3), (0x10dbf1, 3), (0x10dbf4, 3), (0x10dbf7, 3), (0x10dbfa, 3), (0x10dbfd, 2), (0x10dbff, 3), (0x10dc02, 2), (0x10dc04, 3), (0x10dc07, 3), (0x10dc0a, 3), (0x10dc0d, 3), (0x10dc10, 2), (0x10dc12, 3), (0x10dc15, 3), (0x10dc18, 2), (0x10dc1a, 5), (0x10dc1f, 2), (0x10dc21, 3), (0x10dc24, 3), (0x10dc27, 3), (0x10dc2a, 3), (0x10dc2d, 3), (0x10dc30, 3), (0x10dc33, 2), (0x10dc35, 6), (0x10dc3b, 3), (0x10dc3e, 4), (0x10dc42, 3), (0x10dc45, 3), (0x10dc48, 3), (0x10dc4b, 3), (0x10dc4e, 4), (0x10dc52, 3), (0x10dc55, 2), (0x10dc57, 3), (0x10dc5a, 2), (0x10dc5c, 3), (0x10dc5f, 3), (0x10dc62, 2), (0x10dc64, 7), (0x10dc6b, 3), (0x10dc6e, 5), (0x10dc73, 8), (0x10dc7b, 7), (0x10dc82, 8), (0x10dc8a, 8), (0x10dc92, 2), (0x10dc94, 2), (0x10dc96, 3), (0x10dc99, 3), (0x10dc9c, 8), (0x10dca4, 7)]

theorem part51_layout [Bindings] : InstructionTrace.layout part51 = part51Layout := by
  rfl

theorem part51_ordered [Bindings] : InstructionTrace.ordered 0x10dbce part51 = true := by
  rw [InstructionTrace.ordered_eq_layout, part51_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part51_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xdbce 221 = part51Bytes := by
  rfl

end Sha2.Proofs.Common.SHA256.Compression.Decoded
