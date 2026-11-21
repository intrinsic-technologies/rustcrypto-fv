import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part18

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part19 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e608 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e60d 5) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e610 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1a59) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e617 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e61a 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e61d 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e620 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e623 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e626 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e629 0x49 0xd0 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e62c 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e62f 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e632 0x49 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e636 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e639 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e63c 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e640 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e643 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e646 0x4d 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e649 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e64d 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e650 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e653 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e656 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e659 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e65c 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e65f 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e662 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e665 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e668 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e66b 0x49 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e66f 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e672 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e675 0x49 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e679 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e67c 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e67f 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e683 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e686 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e689 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (bswap_r64_effect_step 0x10e691 8) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e694 0x4c (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e69c 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf19d5) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e6a3 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e6a6 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6a9 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e6ac 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e6af 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6b2 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (not_r64_effect_step 0x10e6b5 0x49 0xd0 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e6b8 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6bb 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e6be 0x49 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e6c2 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6c5 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e6c8 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e6cc 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6cf 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6d2 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e6d5 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e6d9 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e6dc 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6df 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e6e2 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6e5 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e6e8 0x4d 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e6eb 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e6ee 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e6f1 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e6f4 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e6f9 0x4c 0xef (by simp [RexWPrefix]) rfl) (by x86_local)
  ]

def part19Bytes : List UInt8 :=
  [0x48,0x8b,0x6c,0x24,0x60,0x48,0xf,0xcd,0x48,0x8b,0x15,0x59,0x1a,0xf,0x0,0x48,0x1,0xea,0x4c,0x1,0xca,0x49,0x89,0xc0,0x49,0x21,0xc8,0x4c,0x1,0xc2,0x49,0x89,0xc0,0x49,0xf7,0xd0,0x4d,0x21,0xd0,0x4d,0x89,0xd9,0x49,0xc1,0xc1,0x24,0x4c,0x1,0xc2,0x4d,0x89,0xd8,0x49,0xc1,0xc0,0x1e,0x48,0x1,0xfa,0x4c,0x89,0xdf,0x4d,0x89,0xdf,0x48,0xc1,0xc7,0x19,0x4d,0x31,0xc8,0x4c,0x31,0xc7,0x4d,0x89,0xe0,0x49,0x21,0xd8,0x4d,0x89,0xe3,0x49,0x31,0xdb,0x4d,0x21,0xfb,0x4d,0x31,0xc3,0x48,0x1,0xd6,0x49,0x89,0xf0,0x49,0xc1,0xc0,0x32,0x49,0x1,0xfb,0x49,0x89,0xf1,0x49,0xc1,0xc1,0x2e,0x49,0x1,0xd3,0x48,0x89,0xf7,0x48,0xc1,0xc7,0x17,0x4d,0x31,0xc1,0x4c,0x31,0xcf,0x4c,0x8b,0x84,0x24,0x88,0x0,0x0,0x0,0x49,0xf,0xc8,0x4c,0x89,0x84,0x24,0x88,0x0,0x0,0x0,0x48,0x8b,0x15,0xd5,0x19,0xf,0x0,0x4c,0x1,0xc2,0x4c,0x1,0xd2,0x49,0x89,0xf0,0x49,0x21,0xc0,0x4c,0x1,0xc2,0x49,0x89,0xf0,0x49,0xf7,0xd0,0x49,0x21,0xc8,0x4d,0x89,0xd9,0x49,0xc1,0xc1,0x24,0x4c,0x1,0xc2,0x4d,0x89,0xd8,0x49,0xc1,0xc0,0x1e,0x48,0x1,0xfa,0x4c,0x89,0xdf,0x4d,0x89,0xde,0x48,0xc1,0xc7,0x19,0x4d,0x31,0xc8,0x4c,0x31,0xc7,0x4d,0x89,0xf8,0x4d,0x21,0xe0,0x4d,0x89,0xf9,0x4d,0x31,0xe1,0x4d,0x21,0xd9,0x4d,0x31,0xc1,0x49,0x1,0xf9,0x4c,0x8b,0x6c,0x24,0x70,0x4c,0x89,0xef]

def part19Layout : List (BitVec 64 × Nat) :=
  [(0x10e608, 5), (0x10e60d, 3), (0x10e610, 7), (0x10e617, 3), (0x10e61a, 3),
   (0x10e61d, 3), (0x10e620, 3), (0x10e623, 3), (0x10e626, 3), (0x10e629, 3),
   (0x10e62c, 3), (0x10e62f, 3), (0x10e632, 4), (0x10e636, 3), (0x10e639, 3),
   (0x10e63c, 4), (0x10e640, 3), (0x10e643, 3), (0x10e646, 3), (0x10e649, 4),
   (0x10e64d, 3), (0x10e650, 3), (0x10e653, 3), (0x10e656, 3), (0x10e659, 3),
   (0x10e65c, 3), (0x10e65f, 3), (0x10e662, 3), (0x10e665, 3), (0x10e668, 3),
   (0x10e66b, 4), (0x10e66f, 3), (0x10e672, 3), (0x10e675, 4), (0x10e679, 3),
   (0x10e67c, 3), (0x10e67f, 4), (0x10e683, 3), (0x10e686, 3), (0x10e689, 8),
   (0x10e691, 3), (0x10e694, 8), (0x10e69c, 7), (0x10e6a3, 3), (0x10e6a6, 3),
   (0x10e6a9, 3), (0x10e6ac, 3), (0x10e6af, 3), (0x10e6b2, 3), (0x10e6b5, 3),
   (0x10e6b8, 3), (0x10e6bb, 3), (0x10e6be, 4), (0x10e6c2, 3), (0x10e6c5, 3),
   (0x10e6c8, 4), (0x10e6cc, 3), (0x10e6cf, 3), (0x10e6d2, 3), (0x10e6d5, 4),
   (0x10e6d9, 3), (0x10e6dc, 3), (0x10e6df, 3), (0x10e6e2, 3), (0x10e6e5, 3),
   (0x10e6e8, 3), (0x10e6eb, 3), (0x10e6ee, 3), (0x10e6f1, 3), (0x10e6f4, 5), (0x10e6f9, 3)]

set_option maxRecDepth 4096 in
theorem part19_bytes [Bindings] : part19.flatMap CheckedInstruction.bytes = part19Bytes := by
  rfl

theorem part19_layout [Bindings] : InstructionTrace.layout part19 = part19Layout := by
  rfl

theorem part19_ordered [Bindings] : InstructionTrace.ordered 0x10e608 part19 = true := by
  rw [InstructionTrace.ordered_eq_layout, part19_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part19_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe608 244 = part19Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
