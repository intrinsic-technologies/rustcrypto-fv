import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA256.Compression.Layout
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.SHA256.Compression.MemoryAlu

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions

def part00 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b530 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b535 0x45 0xf7 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b538 0x41 0xc6 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b53b 0x45 0xcb (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b53e 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 280)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b546 0x41 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b549 0xcf rfl) (by x86_local),
    CheckedInstruction.store (store32_legacy_effect_step 0x10b54b 1 (.sib 4 none 0 (.d32 188)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b552 0 (.base 6 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (LegacyLoad.mov_r32_m32_legacy_effect_step 0x10b554 1 (.base 6 (.d8 4)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b557 0) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b559 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (bswap_r32_effect_step 0x10b55c 1) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b55e 0x49 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b561 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b566 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b569 0xc0 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b56c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b56f 0xc1 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b572 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b574 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b577 0xc0 0x7 rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b57a 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b57c 0x44 0xc1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b57f 0x44 0xd1 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b582 0x44 0xc2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r32_effect_step 0x10b585 0xd2 rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b587 0x44 0xca (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b58a 0x4c (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 272)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b592 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b594 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b596 0xc1 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b598 0xc8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b59a 0xda rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b59c 0xc2 0x1e rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b59f 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b5a2 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b5a7 0xf9 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5a9 0xde rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b5ab 0xc6 0x13 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b5ae 0xc7 rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b5b0 0xc7 0x428a2f98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10b5b6 0x4d 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b5b9 0x41 0xd8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_rex_effect_step 0x10b5bc 0x41 0xc0 0xa (by simp [RexNoWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b5c0 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b5c2 0x41 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b5c5 0x44 0xfa (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r32_r32_rex_effect_step 0x10b5c8 0x44 0xf2 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_effect_step 0x10b5cb 0xda rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_rex_effect_step 0x10b5cd 0x44 0xf8 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r32_r32_rex_effect_step 0x10b5d0 0x44 0xf0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10b5d3 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 264)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r32_r32_effect_step 0x10b5db 0xd0 rfl) (by x86_local),
    CheckedInstruction.register (Lea32.lea_r32_effect_step 0x10b5dd 0x41 (by simp [RexNoWPrefix]) 2 (.sib 11 (some 1) 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_imm32_effect_step 0x10b5e1 0xc2 0x428a2f98 rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5e7 0xd1 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b5e9 0xc1 0x1a rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_rex_effect_step 0x10b5ec 0x44 0xc0 (by simp [RexNoWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5ef 0xd6 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b5f1 0xc6 0x15 rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r32_r32_effect_step 0x10b5f4 0xf8 rfl) (by x86_local),
    CheckedInstruction.register (mov_r32_r32_effect_step 0x10b5f6 0xd7 rfl) (by x86_local),
    CheckedInstruction.register (rol_r32_imm8_effect_step 0x10b5f8 0xc7 0x7 rfl rfl) (by x86_local)]

def part00Bytes : List UInt8 :=
  [0x48,0x89,0x74,0x24,0x18,0x45,0x89,0xf7,0x41,0x89,0xc6,0x45,0x89,0xcb,0x4c,0x89,0x9c,0x24,0x18,0x1,0x0,0x0,0x41,0x89,0xd1,0x89,0xcf,0x89,0x8c,0x24,0xbc,0x0,0x0,0x0,0x8b,0x6,0x8b,0x4e,0x4,0xf,0xc8,0x48,0x89,0xc6,0xf,0xc9,0x49,0x89,0xcd,0x48,0x89,0x4c,0x24,0x38,0x44,0x89,0xc0,0xc1,0xc0,0x1a,0x44,0x89,0xc1,0xc1,0xc1,0x15,0x31,0xc1,0x44,0x89,0xc0,0xc1,0xc0,0x7,0x31,0xc8,0x44,0x89,0xc1,0x44,0x21,0xd1,0x44,0x89,0xc2,0xf7,0xd2,0x44,0x21,0xca,0x4c,0x89,0x8c,0x24,0x10,0x1,0x0,0x0,0x1,0xf9,0x1,0xd1,0x1,0xc1,0x89,0xc8,0x89,0xda,0xc1,0xc2,0x1e,0x48,0x89,0xf7,0x48,0x89,0x74,0x24,0x50,0x1,0xf9,0x89,0xde,0xc1,0xc6,0x13,0x1,0xc7,0x81,0xc7,0x98,0x2f,0x8a,0x42,0x4d,0x89,0xc4,0x41,0x89,0xd8,0x41,0xc1,0xc0,0xa,0x31,0xd6,0x41,0x31,0xf0,0x44,0x89,0xfa,0x44,0x31,0xf2,0x21,0xda,0x44,0x89,0xf8,0x44,0x21,0xf0,0x4c,0x89,0xb4,0x24,0x8,0x1,0x0,0x0,0x31,0xd0,0x41,0x8d,0x14,0xb,0x81,0xc2,0x98,0x2f,0x8a,0x42,0x89,0xd1,0xc1,0xc1,0x1a,0x44,0x1,0xc0,0x89,0xd6,0xc1,0xc6,0x15,0x1,0xf8,0x89,0xd7,0xc1,0xc7,0x7]

set_option maxRecDepth 4096 in
theorem part00_bytes [Bindings] : part00.flatMap CheckedInstruction.bytes = part00Bytes  := by
  rfl

def part00Layout : List (BitVec 64 × Nat) :=
  [(0x10b530, 5), (0x10b535, 3), (0x10b538, 3), (0x10b53b, 3), (0x10b53e, 8), (0x10b546, 3), (0x10b549, 2), (0x10b54b, 7), (0x10b552, 2), (0x10b554, 3), (0x10b557, 2), (0x10b559, 3), (0x10b55c, 2), (0x10b55e, 3), (0x10b561, 5), (0x10b566, 3), (0x10b569, 3), (0x10b56c, 3), (0x10b56f, 3), (0x10b572, 2), (0x10b574, 3), (0x10b577, 3), (0x10b57a, 2), (0x10b57c, 3), (0x10b57f, 3), (0x10b582, 3), (0x10b585, 2), (0x10b587, 3), (0x10b58a, 8), (0x10b592, 2), (0x10b594, 2), (0x10b596, 2), (0x10b598, 2), (0x10b59a, 2), (0x10b59c, 3), (0x10b59f, 3), (0x10b5a2, 5), (0x10b5a7, 2), (0x10b5a9, 2), (0x10b5ab, 3), (0x10b5ae, 2), (0x10b5b0, 6), (0x10b5b6, 3), (0x10b5b9, 3), (0x10b5bc, 4), (0x10b5c0, 2), (0x10b5c2, 3), (0x10b5c5, 3), (0x10b5c8, 3), (0x10b5cb, 2), (0x10b5cd, 3), (0x10b5d0, 3), (0x10b5d3, 8), (0x10b5db, 2), (0x10b5dd, 4), (0x10b5e1, 6), (0x10b5e7, 2), (0x10b5e9, 3), (0x10b5ec, 3), (0x10b5ef, 2), (0x10b5f1, 3), (0x10b5f4, 2), (0x10b5f6, 2), (0x10b5f8, 3)]

theorem part00_layout [Bindings] : InstructionTrace.layout part00 = part00Layout := by
  rfl

theorem part00_ordered [Bindings] : InstructionTrace.ordered 0x10b530 part00 = true := by
  rw [InstructionTrace.ordered_eq_layout, part00_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part00_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xb530 203 = part00Bytes := by
  decide +kernel

end Sha2.Proofs.Common.SHA256.Compression.Decoded
