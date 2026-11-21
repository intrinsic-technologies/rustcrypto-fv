import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part16

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part17 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e50c 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1b4d) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e513 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e516 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e519 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e51c 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e51f 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e522 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e525 0x48 0xd7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e528 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e52b 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e52e 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e532 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e535 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e538 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e53c 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e53f 0x49 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e542 0x49 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e546 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e549 0x49 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e54c 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e54f 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e552 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e555 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e558 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e55b 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e55e 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e561 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e564 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e568 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e56b 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e56e 0x49 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e572 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e575 0x4d 0xdc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e578 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e57b 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e57f 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e582 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e585 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e58a 11) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e58d 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part17Bytes : List UInt8 :=
  [0x48,0x8b,0x15,0x4d,0x1b,0xf,0x0,0x4c,0x1,0xf2,0x48,0x1,0xfa,0x4c,0x89,0xd7,0x4c,0x21,0xcf,0x48,0x1,0xfa,0x4c,0x89,0xd7,0x48,0xf7,0xd7,0x4c,0x21,0xc7,0x49,0x89,0xde,0x49,0xc1,0xc6,0x24,0x48,0x1,0xfa,0x48,0x89,0xdf,0x48,0xc1,0xc7,0x1e,0x4c,0x1,0xda,0x49,0x89,0xdf,0x49,0xc1,0xc7,0x19,0x4c,0x31,0xf7,0x49,0x31,0xff,0x48,0x89,0xf7,0x48,0x21,0xc7,0x49,0x89,0xf3,0x49,0x31,0xc3,0x49,0x21,0xdb,0x49,0x31,0xfb,0x48,0x1,0xd1,0x49,0x89,0xce,0x49,0xc1,0xc6,0x32,0x4d,0x1,0xfb,0x49,0x89,0xcf,0x49,0xc1,0xc7,0x2e,0x49,0x1,0xd3,0x4d,0x89,0xdc,0x48,0x89,0xcf,0x48,0xc1,0xc7,0x17,0x4d,0x31,0xf7,0x4c,0x31,0xff,0x4c,0x8b,0x5c,0x24,0x58,0x49,0xf,0xcb,0x4c,0x89,0x5c,0x24,0x58]

def part17Layout : List (BitVec 64 × Nat) :=
  [(0x10e50c, 7), (0x10e513, 3), (0x10e516, 3), (0x10e519, 3), (0x10e51c, 3),
   (0x10e51f, 3), (0x10e522, 3), (0x10e525, 3), (0x10e528, 3), (0x10e52b, 3),
   (0x10e52e, 4), (0x10e532, 3), (0x10e535, 3), (0x10e538, 4), (0x10e53c, 3),
   (0x10e53f, 3), (0x10e542, 4), (0x10e546, 3), (0x10e549, 3), (0x10e54c, 3),
   (0x10e54f, 3), (0x10e552, 3), (0x10e555, 3), (0x10e558, 3), (0x10e55b, 3),
   (0x10e55e, 3), (0x10e561, 3), (0x10e564, 4), (0x10e568, 3), (0x10e56b, 3),
   (0x10e56e, 4), (0x10e572, 3), (0x10e575, 3), (0x10e578, 3), (0x10e57b, 4),
   (0x10e57f, 3), (0x10e582, 3), (0x10e585, 5), (0x10e58a, 3), (0x10e58d, 5)]

set_option maxRecDepth 4096 in
theorem part17_bytes [Bindings] : part17.flatMap CheckedInstruction.bytes = part17Bytes := by
  rfl

theorem part17_layout [Bindings] : InstructionTrace.layout part17 = part17Layout := by
  rfl

theorem part17_ordered [Bindings] : InstructionTrace.ordered 0x10e50c part17 = true := by
  rw [InstructionTrace.ordered_eq_layout, part17_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part17_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe50c 134 = part17Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
