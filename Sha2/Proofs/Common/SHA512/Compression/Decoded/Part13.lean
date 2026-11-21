import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part12

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part13 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e300 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1d39) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e307 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e30a 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e30d 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e310 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e313 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e316 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e319 0x48 0xd0 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e31c 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e31f 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e322 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e326 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e329 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e32c 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e330 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e333 0x4d 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e336 0x49 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e33a 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e33d 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e340 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e343 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e346 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e349 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e34c 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e34f 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e352 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e355 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e358 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e35c 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e35f 0x49 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e362 0x49 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e366 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e369 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e36c 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e370 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e373 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e376 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e37b 14) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e37e 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part13Bytes : List UInt8 :=
  [0x48,0x8b,0x15,0x39,0x1d,0xf,0x0,0x4c,0x1,0xf2,0x48,0x1,0xc2,0x4c,0x89,0xd8,0x48,0x21,0xf0,0x48,0x1,0xc2,0x4c,0x89,0xd8,0x48,0xf7,0xd0,0x48,0x21,0xd8,0x4d,0x89,0xd6,0x49,0xc1,0xc6,0x24,0x48,0x1,0xc2,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x1e,0x48,0x1,0xca,0x4d,0x89,0xd7,0x49,0xc1,0xc7,0x19,0x4c,0x31,0xf0,0x49,0x31,0xc7,0x4c,0x89,0xc8,0x4c,0x21,0xc0,0x4c,0x89,0xc9,0x4c,0x31,0xc1,0x4c,0x21,0xd1,0x48,0x31,0xc1,0x48,0x1,0xd7,0x49,0x89,0xfe,0x49,0xc1,0xc6,0x32,0x4c,0x1,0xf9,0x49,0x89,0xff,0x49,0xc1,0xc7,0x2e,0x48,0x1,0xd1,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x17,0x4d,0x31,0xf7,0x4c,0x31,0xf8,0x4c,0x8b,0x74,0x24,0x8,0x49,0xf,0xce,0x4c,0x89,0x74,0x24,0x8]

def part13Layout : List (BitVec 64 × Nat) :=
  [(0x10e300, 7), (0x10e307, 3), (0x10e30a, 3), (0x10e30d, 3), (0x10e310, 3),
   (0x10e313, 3), (0x10e316, 3), (0x10e319, 3), (0x10e31c, 3), (0x10e31f, 3),
   (0x10e322, 4), (0x10e326, 3), (0x10e329, 3), (0x10e32c, 4), (0x10e330, 3),
   (0x10e333, 3), (0x10e336, 4), (0x10e33a, 3), (0x10e33d, 3), (0x10e340, 3),
   (0x10e343, 3), (0x10e346, 3), (0x10e349, 3), (0x10e34c, 3), (0x10e34f, 3),
   (0x10e352, 3), (0x10e355, 3), (0x10e358, 4), (0x10e35c, 3), (0x10e35f, 3),
   (0x10e362, 4), (0x10e366, 3), (0x10e369, 3), (0x10e36c, 4), (0x10e370, 3),
   (0x10e373, 3), (0x10e376, 5), (0x10e37b, 3), (0x10e37e, 5)]

set_option maxRecDepth 4096 in
theorem part13_bytes [Bindings] : part13.flatMap CheckedInstruction.bytes = part13Bytes := by
  rfl

theorem part13_layout [Bindings] : InstructionTrace.layout part13 = part13Layout := by
  rfl

theorem part13_ordered [Bindings] : InstructionTrace.ordered 0x10e300 part13 = true := by
  rw [InstructionTrace.ordered_eq_layout, part13_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part13_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe300 131 = part13Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
