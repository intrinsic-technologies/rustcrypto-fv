import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part19

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part20 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e6fc 0x48 0xcf (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e6ff 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e702 0x4d 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e705 0x49 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e709 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e70c 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e70f 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10e712 0x48 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e716 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e719 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e71e 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e721 0x48 0xc7 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e725 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e728 0x49 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e72c 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e72f 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10e732 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e736 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e739 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10e741 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e746 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e749 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e74c 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e750 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e753 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e756 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e75a 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e75d 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e760 0x49 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e764 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e767 0x48 (by simp [RexWPrefix]) 2 (.rip 0xf1912) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e76e 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e771 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e774 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e777 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e77a 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e77d 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e785 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e788 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e78b 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e78e 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e792 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e795 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e798 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e79c 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e79f 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e7a2 0x48 0xc1 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e7a6 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7a9 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7ac 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e7af 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7b2 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e7b5 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e7b8 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e7bb 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e7be 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e7c1 0x49 0xd4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e7c4 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7c9 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e7cc 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e7cf 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7d2 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e7d5 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e7d9 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7dc 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10e7df 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e7e3 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e7e6 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7ee 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e7f1 0x48 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7f5 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e7f8 0x48 0xc7 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e7fc 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e7ff 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10e802 0x48 0xea 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e806 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10e809 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e80e 0x49 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e811 0x49 0xd5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e814 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e819 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e81c 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e820 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e823 0x48 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e827 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e82a 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e82d 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e835 0x48 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e839 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e83c 0x48 (by simp [RexWPrefix]) 5 (.rip 0xf1845) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e843 0x4c 0xed (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e846 0x48 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e849 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e84c 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e84f 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e852 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e855 0x48 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e858 0x48 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e85b 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e85e 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
  ]

def part20Bytes : List UInt8 :=
  [0x48,0xd1,0xcf,0x48,0x1,0xd3,0x4d,0x89,0xe8,0x49,0xc1,0xc0,0x38,0x49,0x1,0xd1,0x49,0x31,0xf8,0x4c,0x89,0xea,0x48,0xc1,0xea,0x7,0x4c,0x31,0xc2,0x48,0x89,0x6c,0x24,0x60,0x48,0x89,0xef,0x48,0xc1,0xc7,0x2d,0x49,0x89,0xe8,0x49,0xc1,0xc0,0x3,0x49,0x31,0xf8,0x48,0x89,0xef,0x48,0xc1,0xef,0x6,0x4c,0x31,0xc7,0x4c,0x8b,0x94,0x24,0x90,0x0,0x0,0x0,0x4c,0x3,0x54,0x24,0x8,0x49,0x1,0xd2,0x48,0x89,0xda,0x48,0xc1,0xc2,0x32,0x49,0x1,0xfa,0x48,0x89,0xdf,0x48,0xc1,0xc7,0x2e,0x48,0x31,0xd7,0x49,0x89,0xd8,0x49,0xc1,0xc0,0x17,0x49,0x31,0xf8,0x48,0x8b,0x15,0x12,0x19,0xf,0x0,0x4c,0x1,0xd2,0x48,0x1,0xca,0x48,0x89,0xf1,0x48,0x31,0xc1,0x48,0x21,0xd9,0x48,0x89,0x9c,0x24,0xd8,0x0,0x0,0x0,0x48,0x31,0xc1,0x48,0x1,0xca,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x24,0x4c,0x1,0xc2,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x1e,0x48,0x31,0xcf,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x19,0x48,0x31,0xf9,0x4c,0x89,0xdf,0x4d,0x89,0xfb,0x4c,0x21,0xff,0x4d,0x89,0xf0,0x4d,0x31,0xf8,0x4d,0x21,0xc8,0x49,0x31,0xf8,0x49,0x1,0xc8,0x49,0x1,0xd4,0x48,0x8b,0x7c,0x24,0x48,0x48,0x89,0xf9,0x48,0xd1,0xc9,0x49,0x1,0xd0,0x48,0x89,0xfa,0x48,0xc1,0xc2,0x38,0x48,0x31,0xca,0x48,0x89,0xf9,0x48,0xc1,0xe9,0x7,0x48,0x31,0xd1,0x4c,0x8b,0xbc,0x24,0x88,0x0,0x0,0x0,0x4c,0x89,0xfa,0x48,0xc1,0xc2,0x2d,0x4c,0x89,0xff,0x48,0xc1,0xc7,0x3,0x48,0x31,0xd7,0x4c,0x89,0xfa,0x48,0xc1,0xea,0x6,0x48,0x31,0xfa,0x4c,0x3,0x6c,0x24,0x10,0x49,0x1,0xcd,0x49,0x1,0xd5,0x4c,0x89,0x6c,0x24,0x70,0x4c,0x89,0xe1,0x48,0xc1,0xc1,0x32,0x4c,0x89,0xe2,0x48,0xc1,0xc2,0x2e,0x48,0x31,0xca,0x4c,0x89,0xe1,0x4c,0x89,0xa4,0x24,0x80,0x0,0x0,0x0,0x48,0xc1,0xc1,0x17,0x48,0x31,0xd1,0x48,0x8b,0x2d,0x45,0x18,0xf,0x0,0x4c,0x1,0xed,0x48,0x1,0xc5,0x48,0x89,0xd8,0x48,0x31,0xf0,0x4c,0x21,0xe0,0x48,0x31,0xf0,0x48,0x1,0xc5,0x48,0x1,0xcd,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x24]

set_option maxRecDepth 4096 in
theorem part20_bytes [Bindings] : part20.flatMap CheckedInstruction.bytes = part20Bytes := by
  rfl

def part20Layout : List (BitVec 64 × Nat) :=
  [(0x10e6fc, 3), (0x10e6ff, 3), (0x10e702, 3), (0x10e705, 4), (0x10e709, 3), (0x10e70c, 3), (0x10e70f, 3), (0x10e712, 4), (0x10e716, 3), (0x10e719, 5), (0x10e71e, 3), (0x10e721, 4), (0x10e725, 3), (0x10e728, 4), (0x10e72c, 3), (0x10e72f, 3), (0x10e732, 4), (0x10e736, 3), (0x10e739, 8), (0x10e741, 5), (0x10e746, 3), (0x10e749, 3), (0x10e74c, 4), (0x10e750, 3), (0x10e753, 3), (0x10e756, 4), (0x10e75a, 3), (0x10e75d, 3), (0x10e760, 4), (0x10e764, 3), (0x10e767, 7), (0x10e76e, 3), (0x10e771, 3), (0x10e774, 3), (0x10e777, 3), (0x10e77a, 3), (0x10e77d, 8), (0x10e785, 3), (0x10e788, 3), (0x10e78b, 3), (0x10e78e, 4), (0x10e792, 3), (0x10e795, 3), (0x10e798, 4), (0x10e79c, 3), (0x10e79f, 3), (0x10e7a2, 4), (0x10e7a6, 3), (0x10e7a9, 3), (0x10e7ac, 3), (0x10e7af, 3), (0x10e7b2, 3), (0x10e7b5, 3), (0x10e7b8, 3), (0x10e7bb, 3), (0x10e7be, 3), (0x10e7c1, 3), (0x10e7c4, 5), (0x10e7c9, 3), (0x10e7cc, 3), (0x10e7cf, 3), (0x10e7d2, 3), (0x10e7d5, 4), (0x10e7d9, 3), (0x10e7dc, 3), (0x10e7df, 4), (0x10e7e3, 3), (0x10e7e6, 8), (0x10e7ee, 3), (0x10e7f1, 4), (0x10e7f5, 3), (0x10e7f8, 4), (0x10e7fc, 3), (0x10e7ff, 3), (0x10e802, 4), (0x10e806, 3), (0x10e809, 5), (0x10e80e, 3), (0x10e811, 3), (0x10e814, 5), (0x10e819, 3), (0x10e81c, 4), (0x10e820, 3), (0x10e823, 4), (0x10e827, 3), (0x10e82a, 3), (0x10e82d, 8), (0x10e835, 4), (0x10e839, 3), (0x10e83c, 7), (0x10e843, 3), (0x10e846, 3), (0x10e849, 3), (0x10e84c, 3), (0x10e84f, 3), (0x10e852, 3), (0x10e855, 3), (0x10e858, 3), (0x10e85b, 3), (0x10e85e, 4)]

theorem part20_layout [Bindings] : InstructionTrace.layout part20 = part20Layout := by
  rfl

theorem part20_ordered [Bindings] : InstructionTrace.ordered 0x10e6fc part20 = true := by
  rw [InstructionTrace.ordered_eq_layout, part20_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part20_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe6fc 358 = part20Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
