import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part11

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part12 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e27d 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf1db4) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e284 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e287 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e28a 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e28d 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e290 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e293 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e296 0x48 0xd2 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e299 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e29c 0x4d 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e29f 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e2a3 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e2a6 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e2a9 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e2ad 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e2b0 0x4d 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e2b3 0x49 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e2b7 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e2ba 0x49 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e2bd 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e2c0 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e2c3 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e2c6 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e2c9 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e2cc 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e2cf 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e2d2 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e2d5 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e2d9 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e2dc 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e2df 0x49 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e2e3 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e2e6 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e2e9 0x48 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e2ed 0x49 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e2f0 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e2f3 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e2f8 14) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e2fb 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part12Bytes : List UInt8 :=
  [0x48,0x8b,0xd,0xb4,0x1d,0xf,0x0,0x4c,0x1,0xe1,0x48,0x1,0xd1,0x48,0x89,0xf2,0x48,0x21,0xda,0x48,0x1,0xd1,0x48,0x89,0xf2,0x48,0xf7,0xd2,0x48,0x21,0xc2,0x4d,0x89,0xce,0x49,0xc1,0xc6,0x24,0x48,0x1,0xd1,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x1e,0x4c,0x1,0xd1,0x4d,0x89,0xcf,0x49,0xc1,0xc7,0x19,0x4c,0x31,0xf2,0x49,0x31,0xd7,0x4c,0x89,0xc2,0x48,0x21,0xfa,0x4d,0x89,0xc2,0x49,0x31,0xfa,0x4d,0x21,0xca,0x49,0x31,0xd2,0x49,0x1,0xcb,0x4c,0x89,0xda,0x48,0xc1,0xc2,0x32,0x4d,0x1,0xfa,0x4d,0x89,0xde,0x49,0xc1,0xc6,0x2e,0x49,0x1,0xca,0x4c,0x89,0xd9,0x48,0xc1,0xc1,0x17,0x49,0x31,0xd6,0x4c,0x31,0xf1,0x4c,0x8b,0x74,0x24,0x68,0x49,0xf,0xce,0x4c,0x89,0x74,0x24,0x68]

def part12Layout : List (BitVec 64 × Nat) :=
  [(0x10e27d, 7), (0x10e284, 3), (0x10e287, 3), (0x10e28a, 3), (0x10e28d, 3),
   (0x10e290, 3), (0x10e293, 3), (0x10e296, 3), (0x10e299, 3), (0x10e29c, 3),
   (0x10e29f, 4), (0x10e2a3, 3), (0x10e2a6, 3), (0x10e2a9, 4), (0x10e2ad, 3),
   (0x10e2b0, 3), (0x10e2b3, 4), (0x10e2b7, 3), (0x10e2ba, 3), (0x10e2bd, 3),
   (0x10e2c0, 3), (0x10e2c3, 3), (0x10e2c6, 3), (0x10e2c9, 3), (0x10e2cc, 3),
   (0x10e2cf, 3), (0x10e2d2, 3), (0x10e2d5, 4), (0x10e2d9, 3), (0x10e2dc, 3),
   (0x10e2df, 4), (0x10e2e3, 3), (0x10e2e6, 3), (0x10e2e9, 4), (0x10e2ed, 3),
   (0x10e2f0, 3), (0x10e2f3, 5), (0x10e2f8, 3), (0x10e2fb, 5)]

set_option maxRecDepth 4096 in
theorem part12_bytes [Bindings] : part12.flatMap CheckedInstruction.bytes = part12Bytes := by
  rfl

theorem part12_layout [Bindings] : InstructionTrace.layout part12 = part12Layout := by
  rfl

theorem part12_ordered [Bindings] : InstructionTrace.ordered 0x10e27d part12 = true := by
  rw [InstructionTrace.ordered_eq_layout, part12_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part12_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe27d 131 = part12Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
