import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part30

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part31 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f695 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f699 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f69c 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f69f 0x48 0xc6 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f6a3 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f6a6 0x48 (by simp [RexWPrefix]) 7 (.rip 0xf0a53) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f6ad 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f6b0 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f6b3 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f6b6 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f6b9 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f6bc 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f6bf 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f6c2 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f6c5 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f6c8 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f6cc 0x4d 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f6cf 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f6d3 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f6d6 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f6d9 0x48 0xc6 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f6dd 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f6e0 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f6e3 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f6e6 0x4c 0xe5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f6e9 0x4c 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f6ec 0x4c 0xed (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f6ef 0x4c 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f6f2 0x48 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f6f5 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f6f8 0x48 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f6fb 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f6fe 0x48 0xc7 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f702 0x4c 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f705 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f709 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f70c 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f70f 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f712 0x48 0xcf (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f715 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f718 0x49 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f71c 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f71f 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f722 0x48 0xef 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f726 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f729 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f72e 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f731 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f736 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f739 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f73d 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f740 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f745 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f748 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f74b 0x48 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f74f 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f752 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f756 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f759 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f75c 0x48 0xc6 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f760 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f763 0x48 (by simp [RexWPrefix]) 7 (.rip 0xf099e) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f76a 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f76d 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f770 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f773 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f776 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f779 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f77c 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f77f 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f782 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f785 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f789 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f78c 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f790 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f793 0x49 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f796 0x49 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f79a 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f79d 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f7a0 0x4c 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f7a3 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f7a6 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f7a9 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f7ac 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f7af 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f7b2 0x49 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f7b6 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f7b9 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f7bc 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f7c0 0x49 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f7c3 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f7c6 0x49 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f7c9 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f7cc 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f7cf 0x48 0xc7 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f7d3 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f7d6 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f7d9 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f7dc 0x49 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f7e0 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part31Bytes : List UInt8 :=
  [0x48,0xc1,0xc7,0x2e,0x48,0x31,0xf7,0x48,0x89,0xd6,0x48,0xc1,0xc6,0x17,0x48,0x31,0xfe,0x48,0x8b,0x3d,0x53,0xa,0xf,0x0,0x4c,0x1,0xd7,0x4c,0x1,0xdf,0x49,0x89,0xc0,0x49,0x31,0xc8,0x49,0x21,0xd0,0x49,0x31,0xc8,0x4c,0x1,0xc7,0x48,0x1,0xf7,0x4c,0x89,0xee,0x48,0xc1,0xc6,0x24,0x4d,0x89,0xe8,0x49,0xc1,0xc0,0x1e,0x49,0x31,0xf0,0x4c,0x89,0xee,0x48,0xc1,0xc6,0x19,0x4c,0x31,0xc6,0x4d,0x89,0xe0,0x4d,0x21,0xf8,0x4c,0x89,0xe5,0x4c,0x31,0xfd,0x4c,0x21,0xed,0x4c,0x31,0xc5,0x48,0x1,0xf5,0x48,0x1,0xfb,0x48,0x1,0xfd,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x2d,0x4c,0x89,0xce,0x48,0xc1,0xc6,0x3,0x48,0x31,0xfe,0x4d,0x89,0xd3,0x4c,0x89,0xd7,0x48,0xd1,0xcf,0x4d,0x89,0xd0,0x49,0xc1,0xc0,0x38,0x49,0x31,0xf8,0x4c,0x89,0xd7,0x48,0xc1,0xef,0x7,0x4c,0x31,0xc7,0x4c,0x1,0x4c,0x24,0x20,0x4c,0x1,0xcf,0x48,0x89,0x7c,0x24,0x10,0x4c,0x89,0xcf,0x48,0xc1,0xef,0x6,0x48,0x31,0xf7,0x4c,0x8b,0x4c,0x24,0x8,0x49,0x1,0xf9,0x48,0x89,0xde,0x48,0xc1,0xc6,0x32,0x48,0x89,0xdf,0x48,0xc1,0xc7,0x2e,0x48,0x31,0xf7,0x48,0x89,0xde,0x48,0xc1,0xc6,0x17,0x48,0x31,0xfe,0x48,0x8b,0x3d,0x9e,0x9,0xf,0x0,0x4c,0x1,0xcf,0x48,0x1,0xcf,0x48,0x89,0xd1,0x48,0x31,0xc1,0x48,0x21,0xd9,0x48,0x31,0xc1,0x48,0x1,0xcf,0x48,0x1,0xf7,0x48,0x89,0xe9,0x48,0xc1,0xc1,0x24,0x48,0x89,0xee,0x48,0xc1,0xc6,0x1e,0x48,0x31,0xce,0x49,0x89,0xea,0x49,0xc1,0xc2,0x19,0x49,0x31,0xf2,0x4c,0x89,0xee,0x4c,0x21,0xe6,0x4c,0x89,0xe9,0x4c,0x31,0xe1,0x48,0x21,0xe9,0x48,0x31,0xf1,0x4d,0x89,0xd8,0x49,0xc1,0xc0,0x2d,0x4c,0x1,0xd1,0x4c,0x89,0xde,0x48,0xc1,0xc6,0x3,0x49,0x1,0xff,0x4d,0x89,0xca,0x49,0xd1,0xca,0x48,0x1,0xf9,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x38,0x4c,0x31,0xc6,0x4c,0x31,0xd7,0x4d,0x89,0xc8,0x49,0xc1,0xe8,0x7,0x49,0x31,0xf8]

set_option maxRecDepth 4096 in
theorem part31_bytes [Bindings] : part31.flatMap CheckedInstruction.bytes = part31Bytes := by
  rfl

def part31Layout : List (BitVec 64 × Nat) :=
  [(0x10f695, 4), (0x10f699, 3), (0x10f69c, 3), (0x10f69f, 4), (0x10f6a3, 3), (0x10f6a6, 7), (0x10f6ad, 3), (0x10f6b0, 3), (0x10f6b3, 3), (0x10f6b6, 3), (0x10f6b9, 3), (0x10f6bc, 3), (0x10f6bf, 3), (0x10f6c2, 3), (0x10f6c5, 3), (0x10f6c8, 4), (0x10f6cc, 3), (0x10f6cf, 4), (0x10f6d3, 3), (0x10f6d6, 3), (0x10f6d9, 4), (0x10f6dd, 3), (0x10f6e0, 3), (0x10f6e3, 3), (0x10f6e6, 3), (0x10f6e9, 3), (0x10f6ec, 3), (0x10f6ef, 3), (0x10f6f2, 3), (0x10f6f5, 3), (0x10f6f8, 3), (0x10f6fb, 3), (0x10f6fe, 4), (0x10f702, 3), (0x10f705, 4), (0x10f709, 3), (0x10f70c, 3), (0x10f70f, 3), (0x10f712, 3), (0x10f715, 3), (0x10f718, 4), (0x10f71c, 3), (0x10f71f, 3), (0x10f722, 4), (0x10f726, 3), (0x10f729, 5), (0x10f72e, 3), (0x10f731, 5), (0x10f736, 3), (0x10f739, 4), (0x10f73d, 3), (0x10f740, 5), (0x10f745, 3), (0x10f748, 3), (0x10f74b, 4), (0x10f74f, 3), (0x10f752, 4), (0x10f756, 3), (0x10f759, 3), (0x10f75c, 4), (0x10f760, 3), (0x10f763, 7), (0x10f76a, 3), (0x10f76d, 3), (0x10f770, 3), (0x10f773, 3), (0x10f776, 3), (0x10f779, 3), (0x10f77c, 3), (0x10f77f, 3), (0x10f782, 3), (0x10f785, 4), (0x10f789, 3), (0x10f78c, 4), (0x10f790, 3), (0x10f793, 3), (0x10f796, 4), (0x10f79a, 3), (0x10f79d, 3), (0x10f7a0, 3), (0x10f7a3, 3), (0x10f7a6, 3), (0x10f7a9, 3), (0x10f7ac, 3), (0x10f7af, 3), (0x10f7b2, 4), (0x10f7b6, 3), (0x10f7b9, 3), (0x10f7bc, 4), (0x10f7c0, 3), (0x10f7c3, 3), (0x10f7c6, 3), (0x10f7c9, 3), (0x10f7cc, 3), (0x10f7cf, 4), (0x10f7d3, 3), (0x10f7d6, 3), (0x10f7d9, 3), (0x10f7dc, 4), (0x10f7e0, 3)]

theorem part31_layout [Bindings] : InstructionTrace.layout part31 = part31Layout := by
  rfl

theorem part31_ordered [Bindings] : InstructionTrace.ordered 0x10f695 part31 = true := by
  rw [InstructionTrace.ordered_eq_layout, part31_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part31_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xf695 334 = part31Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
