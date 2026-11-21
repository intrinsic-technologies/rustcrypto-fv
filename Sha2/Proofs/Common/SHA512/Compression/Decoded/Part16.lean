import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part15

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part16 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e489 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1bc8) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e490 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e493 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e496 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e499 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e49c 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e49f 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e4a2 0x49 0xd3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e4a5 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e4a8 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e4ab 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e4af 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e4b2 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e4b5 0x49 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e4b9 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e4bc 0x49 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e4bf 0x49 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e4c3 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e4c6 0x4d 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e4c9 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e4cc 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e4cf 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e4d2 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e4d5 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e4d8 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e4db 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e4de 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e4e1 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e4e5 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e4e8 0x4d 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e4eb 0x49 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e4ef 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e4f2 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e4f5 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e4f9 0x4d 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e4fc 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e4ff 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e504 14) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e507 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _)
  ]

def part16Bytes : List UInt8 :=
  [0x48,0x8b,0x15,0xc8,0x1b,0xf,0x0,0x4c,0x1,0xf2,0x4c,0x1,0xda,0x4d,0x89,0xcb,0x4d,0x21,0xc3,0x4c,0x1,0xda,0x4d,0x89,0xcb,0x49,0xf7,0xd3,0x49,0x21,0xfb,0x49,0x89,0xf6,0x49,0xc1,0xc6,0x24,0x4c,0x1,0xda,0x49,0x89,0xf3,0x49,0xc1,0xc3,0x1e,0x48,0x1,0xda,0x49,0x89,0xf7,0x49,0xc1,0xc7,0x19,0x4d,0x31,0xf3,0x4d,0x31,0xdf,0x49,0x89,0xc3,0x49,0x21,0xcb,0x48,0x89,0xc3,0x48,0x31,0xcb,0x48,0x21,0xf3,0x4c,0x31,0xdb,0x49,0x1,0xd2,0x4d,0x89,0xd6,0x49,0xc1,0xc6,0x32,0x4c,0x1,0xfb,0x4d,0x89,0xd7,0x49,0xc1,0xc7,0x2e,0x48,0x1,0xd3,0x4d,0x89,0xd3,0x49,0xc1,0xc3,0x17,0x4d,0x31,0xf7,0x4d,0x31,0xfb,0x4c,0x8b,0x74,0x24,0x28,0x49,0xf,0xce,0x4c,0x89,0x74,0x24,0x28]

def part16Layout : List (BitVec 64 × Nat) :=
  [(0x10e489, 7), (0x10e490, 3), (0x10e493, 3), (0x10e496, 3), (0x10e499, 3),
   (0x10e49c, 3), (0x10e49f, 3), (0x10e4a2, 3), (0x10e4a5, 3), (0x10e4a8, 3),
   (0x10e4ab, 4), (0x10e4af, 3), (0x10e4b2, 3), (0x10e4b5, 4), (0x10e4b9, 3),
   (0x10e4bc, 3), (0x10e4bf, 4), (0x10e4c3, 3), (0x10e4c6, 3), (0x10e4c9, 3),
   (0x10e4cc, 3), (0x10e4cf, 3), (0x10e4d2, 3), (0x10e4d5, 3), (0x10e4d8, 3),
   (0x10e4db, 3), (0x10e4de, 3), (0x10e4e1, 4), (0x10e4e5, 3), (0x10e4e8, 3),
   (0x10e4eb, 4), (0x10e4ef, 3), (0x10e4f2, 3), (0x10e4f5, 4), (0x10e4f9, 3),
   (0x10e4fc, 3), (0x10e4ff, 5), (0x10e504, 3), (0x10e507, 5)]

set_option maxRecDepth 4096 in
theorem part16_bytes [Bindings] : part16.flatMap CheckedInstruction.bytes = part16Bytes := by
  rfl

theorem part16_layout [Bindings] : InstructionTrace.layout part16 = part16Layout := by
  rfl

theorem part16_ordered [Bindings] : InstructionTrace.ordered 0x10e489 part16 = true := by
  rw [InstructionTrace.ordered_eq_layout, part16_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part16_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe489 131 = part16Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
