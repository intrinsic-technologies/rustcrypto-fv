import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part17

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part18 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e592 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1acf) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e599 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e59c 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e59f 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e5a2 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e5a5 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5a8 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e5ab 0x49 0xd0 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e5ae 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5b1 0x4d 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e5b4 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e5b8 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5bb 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e5be 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e5c2 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5c5 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e5c8 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e5cc 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e5cf 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5d2 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e5d5 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5d8 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e5db 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e5de 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e5e1 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e5e4 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5e7 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e5ea 0x49 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e5ee 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5f1 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e5f4 0x49 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e5f8 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e5fb 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e5fe 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e602 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e605 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local)
  ]

def part18Bytes : List UInt8 :=
  [0x48,0x8b,0x15,0xcf,0x1a,0xf,0x0,0x4c,0x1,0xda,0x4c,0x1,0xc2,0x49,0x89,0xc8,0x4d,0x21,0xd0,0x4c,0x1,0xc2,0x49,0x89,0xc8,0x49,0xf7,0xd0,0x4d,0x21,0xc8,0x4d,0x89,0xe6,0x49,0xc1,0xc6,0x24,0x4c,0x1,0xc2,0x4d,0x89,0xe0,0x49,0xc1,0xc0,0x1e,0x48,0x1,0xfa,0x4c,0x89,0xe7,0x48,0xc1,0xc7,0x19,0x4d,0x31,0xf0,0x4c,0x31,0xc7,0x49,0x89,0xd8,0x49,0x21,0xf0,0x49,0x89,0xdb,0x49,0x31,0xf3,0x4d,0x21,0xe3,0x4d,0x31,0xc3,0x48,0x1,0xd0,0x49,0x89,0xc0,0x49,0xc1,0xc0,0x32,0x49,0x1,0xfb,0x49,0x89,0xc6,0x49,0xc1,0xc6,0x2e,0x49,0x1,0xd3,0x48,0x89,0xc7,0x48,0xc1,0xc7,0x17,0x4d,0x31,0xc6,0x4c,0x31,0xf7]

def part18Layout : List (BitVec 64 × Nat) :=
  [(0x10e592, 7), (0x10e599, 3), (0x10e59c, 3), (0x10e59f, 3), (0x10e5a2, 3),
   (0x10e5a5, 3), (0x10e5a8, 3), (0x10e5ab, 3), (0x10e5ae, 3), (0x10e5b1, 3),
   (0x10e5b4, 4), (0x10e5b8, 3), (0x10e5bb, 3), (0x10e5be, 4), (0x10e5c2, 3),
   (0x10e5c5, 3), (0x10e5c8, 4), (0x10e5cc, 3), (0x10e5cf, 3), (0x10e5d2, 3),
   (0x10e5d5, 3), (0x10e5d8, 3), (0x10e5db, 3), (0x10e5de, 3), (0x10e5e1, 3),
   (0x10e5e4, 3), (0x10e5e7, 3), (0x10e5ea, 4), (0x10e5ee, 3), (0x10e5f1, 3),
   (0x10e5f4, 4), (0x10e5f8, 3), (0x10e5fb, 3), (0x10e5fe, 4), (0x10e602, 3),
   (0x10e605, 3)]

set_option maxRecDepth 4096 in
theorem part18_bytes [Bindings] : part18.flatMap CheckedInstruction.bytes = part18Bytes := by
  rfl

theorem part18_layout [Bindings] : InstructionTrace.layout part18 = part18Layout := by
  rfl

theorem part18_ordered [Bindings] : InstructionTrace.ordered 0x10e592 part18 = true := by
  rw [InstructionTrace.ordered_eq_layout, part18_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part18_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe592 118 = part18Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
