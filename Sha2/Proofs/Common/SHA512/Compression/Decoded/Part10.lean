import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part09

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part10 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e184 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e187 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e18a 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e18d 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e190 0x49 0xd0 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e193 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e196 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e199 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e19d 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e1a0 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e1a3 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e1a7 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e1aa 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e1ad 0x49 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e1b1 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e1b4 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e1b7 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e1ba 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e1bd 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e1c0 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e1c3 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e1c6 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e1c9 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e1cc 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e1cf 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e1d3 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e1d6 0x49 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e1d9 0x49 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e1dd 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e1e0 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e1e3 0x49 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e1e7 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e1ea 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e1ed 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e1f2 5) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e1f5 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part10Bytes : List UInt8 :=
  [0x49,0x89,0xc0,0x49,0x21,0xd0,0x4c,0x1,0xc1,0x49,0x89,0xc0,0x49,0xf7,0xd0,0x4d,0x21,0xc8,0x49,0x89,0xfe,0x49,0xc1,0xc6,0x24,0x4c,0x1,0xc1,0x49,0x89,0xf8,0x49,0xc1,0xc0,0x1e,0x4c,0x1,0xd1,0x49,0x89,0xfa,0x49,0xc1,0xc2,0x19,0x4d,0x31,0xf0,0x4d,0x31,0xc2,0x4d,0x89,0xde,0x49,0x21,0xf6,0x4d,0x89,0xd8,0x49,0x31,0xf0,0x49,0x21,0xf8,0x4d,0x31,0xf0,0x48,0x1,0xcb,0x49,0x89,0xde,0x49,0xc1,0xc6,0x32,0x4d,0x1,0xd0,0x49,0x89,0xdf,0x49,0xc1,0xc7,0x2e,0x49,0x1,0xc8,0x49,0x89,0xda,0x49,0xc1,0xc2,0x17,0x4d,0x31,0xf7,0x4d,0x31,0xfa,0x48,0x8b,0x6c,0x24,0x20,0x48,0xf,0xcd,0x48,0x89,0x6c,0x24,0x20]

def part10Layout : List (BitVec 64 × Nat) :=
  [(0x10e184, 3), (0x10e187, 3), (0x10e18a, 3), (0x10e18d, 3), (0x10e190, 3),
   (0x10e193, 3), (0x10e196, 3), (0x10e199, 4), (0x10e19d, 3), (0x10e1a0, 3),
   (0x10e1a3, 4), (0x10e1a7, 3), (0x10e1aa, 3), (0x10e1ad, 4), (0x10e1b1, 3),
   (0x10e1b4, 3), (0x10e1b7, 3), (0x10e1ba, 3), (0x10e1bd, 3), (0x10e1c0, 3),
   (0x10e1c3, 3), (0x10e1c6, 3), (0x10e1c9, 3), (0x10e1cc, 3), (0x10e1cf, 4),
   (0x10e1d3, 3), (0x10e1d6, 3), (0x10e1d9, 4), (0x10e1dd, 3), (0x10e1e0, 3),
   (0x10e1e3, 4), (0x10e1e7, 3), (0x10e1ea, 3), (0x10e1ed, 5), (0x10e1f2, 3),
   (0x10e1f5, 5)]

set_option maxRecDepth 4096 in
theorem part10_bytes [Bindings] : part10.flatMap CheckedInstruction.bytes = part10Bytes := by
  rfl

theorem part10_layout [Bindings] : InstructionTrace.layout part10 = part10Layout := by
  rfl

theorem part10_ordered [Bindings] : InstructionTrace.ordered 0x10e184 part10 = true := by
  rw [InstructionTrace.ordered_eq_layout, part10_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part10_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe184 118 = part10Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
