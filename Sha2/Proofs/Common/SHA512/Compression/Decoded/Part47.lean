import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part46

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part47 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110bce 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110bd1 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110bd5 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110bd8 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110bdd 0x49 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110be0 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110be3 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110be7 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110bea 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110bee 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110bf1 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110bf4 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110bf8 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110bfb 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef5e6) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110c02 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110c05 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c08 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c0b 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110c0e 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c11 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110c14 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110c17 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c1a 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110c1d 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c21 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110c24 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c28 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c2b 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110c2e 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c32 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c35 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110c38 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c3b 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c3e 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110c41 0x49 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c44 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c47 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110c4a 0x48 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110c4e 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c51 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110c54 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110c58 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c5b 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110c5e 0x48 0xce (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110c61 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c64 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110c67 0x48 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c6b 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c6e 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c71 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110c74 0x48 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c78 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110c7b 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110c80 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110c83 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c88 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110c8b 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c8f 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110c92 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110c96 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110c99 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110c9c 0x48 0xc0 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110ca0 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ca5 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ca8 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110cab 0x48 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110caf 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110cb2 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110cb5 0x48 (by simp [RexWPrefix]) 2 (.rip 0xef534) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110cbc 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110cbf 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110cc2 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110cc5 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110cc8 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ccb 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110cce 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110cd1 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110cd5 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110cd8 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110cdb 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110cdf 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ce2 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110ce5 0x48 0xc1 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ce9 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110cec 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110cef 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110cf2 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110cf5 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110cf8 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110cfb 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110cfe 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d01 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d04 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110d07 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d0b 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d0e 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110d11 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d15 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d18 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110d1b 0x48 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
  ]

def part47Bytes : List UInt8 :=
  [0x48,0x89,0xf1,0x48,0xc1,0xe9,0x6,0x48,0x31,0xc1,0x4c,0x8b,0x6c,0x24,0x30,0x49,0x1,0xcd,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x32,0x4c,0x89,0xd9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0xe6,0xf5,0xe,0x0,0x4c,0x1,0xe9,0x4c,0x1,0xc9,0x4c,0x89,0xc2,0x4c,0x31,0xfa,0x4c,0x21,0xda,0x4c,0x31,0xfa,0x48,0x1,0xd1,0x48,0x1,0xc1,0x48,0x89,0xe8,0x48,0xc1,0xc0,0x24,0x48,0x89,0xea,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xc2,0x48,0x89,0xe8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xd0,0x48,0x89,0xda,0x48,0x21,0xfa,0x49,0x89,0xda,0x49,0x31,0xfa,0x49,0x21,0xea,0x49,0x31,0xd2,0x4c,0x89,0xe2,0x48,0xc1,0xc2,0x2d,0x49,0x1,0xc2,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x3,0x49,0x1,0xce,0x4c,0x89,0xee,0x48,0xd1,0xce,0x49,0x1,0xca,0x4c,0x89,0xe9,0x48,0xc1,0xc1,0x38,0x48,0x31,0xd0,0x48,0x31,0xf1,0x4c,0x89,0xea,0x48,0xc1,0xea,0x7,0x48,0x31,0xca,0x4c,0x1,0x64,0x24,0x78,0x4c,0x1,0xe2,0x48,0x89,0x54,0x24,0x30,0x4c,0x89,0xe1,0x48,0xc1,0xe9,0x6,0x4c,0x89,0xf2,0x48,0xc1,0xc2,0x32,0x48,0x31,0xc1,0x4c,0x89,0xf0,0x48,0xc1,0xc0,0x2e,0x4c,0x8b,0x4c,0x24,0x20,0x49,0x1,0xc9,0x4c,0x89,0xf1,0x48,0xc1,0xc1,0x17,0x48,0x31,0xd0,0x48,0x31,0xc1,0x48,0x8b,0x15,0x34,0xf5,0xe,0x0,0x4c,0x1,0xca,0x4c,0x1,0xfa,0x4c,0x89,0xd8,0x4c,0x31,0xc0,0x4c,0x21,0xf0,0x4c,0x31,0xc0,0x4c,0x89,0xd6,0x48,0xc1,0xc6,0x24,0x48,0x1,0xc2,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x1e,0x48,0x1,0xca,0x4c,0x89,0xd1,0x48,0xc1,0xc1,0x19,0x48,0x31,0xf0,0x48,0x31,0xc1,0x48,0x89,0xe8,0x48,0x21,0xd8,0x48,0x89,0xee,0x48,0x31,0xde,0x4c,0x21,0xd6,0x48,0x31,0xc6,0x48,0x1,0xce,0x4c,0x89,0xe9,0x48,0xc1,0xc1,0x2d,0x48,0x1,0xd7,0x4c,0x89,0xe8,0x48,0xc1,0xc0,0x3,0x48,0x1,0xd6,0x4c,0x89,0xca,0x48,0xd1,0xca]

set_option maxRecDepth 4096 in
theorem part47_bytes [Bindings] : part47.flatMap CheckedInstruction.bytes = part47Bytes := by
  rfl

def part47Layout : List (BitVec 64 × Nat) :=
  [(0x110bce, 3), (0x110bd1, 4), (0x110bd5, 3), (0x110bd8, 5), (0x110bdd, 3), (0x110be0, 3), (0x110be3, 4), (0x110be7, 3), (0x110bea, 4), (0x110bee, 3), (0x110bf1, 3), (0x110bf4, 4), (0x110bf8, 3), (0x110bfb, 7), (0x110c02, 3), (0x110c05, 3), (0x110c08, 3), (0x110c0b, 3), (0x110c0e, 3), (0x110c11, 3), (0x110c14, 3), (0x110c17, 3), (0x110c1a, 3), (0x110c1d, 4), (0x110c21, 3), (0x110c24, 4), (0x110c28, 3), (0x110c2b, 3), (0x110c2e, 4), (0x110c32, 3), (0x110c35, 3), (0x110c38, 3), (0x110c3b, 3), (0x110c3e, 3), (0x110c41, 3), (0x110c44, 3), (0x110c47, 3), (0x110c4a, 4), (0x110c4e, 3), (0x110c51, 3), (0x110c54, 4), (0x110c58, 3), (0x110c5b, 3), (0x110c5e, 3), (0x110c61, 3), (0x110c64, 3), (0x110c67, 4), (0x110c6b, 3), (0x110c6e, 3), (0x110c71, 3), (0x110c74, 4), (0x110c78, 3), (0x110c7b, 5), (0x110c80, 3), (0x110c83, 5), (0x110c88, 3), (0x110c8b, 4), (0x110c8f, 3), (0x110c92, 4), (0x110c96, 3), (0x110c99, 3), (0x110c9c, 4), (0x110ca0, 5), (0x110ca5, 3), (0x110ca8, 3), (0x110cab, 4), (0x110caf, 3), (0x110cb2, 3), (0x110cb5, 7), (0x110cbc, 3), (0x110cbf, 3), (0x110cc2, 3), (0x110cc5, 3), (0x110cc8, 3), (0x110ccb, 3), (0x110cce, 3), (0x110cd1, 4), (0x110cd5, 3), (0x110cd8, 3), (0x110cdb, 4), (0x110cdf, 3), (0x110ce2, 3), (0x110ce5, 4), (0x110ce9, 3), (0x110cec, 3), (0x110cef, 3), (0x110cf2, 3), (0x110cf5, 3), (0x110cf8, 3), (0x110cfb, 3), (0x110cfe, 3), (0x110d01, 3), (0x110d04, 3), (0x110d07, 4), (0x110d0b, 3), (0x110d0e, 3), (0x110d11, 4), (0x110d15, 3), (0x110d18, 3), (0x110d1b, 3)]

theorem part47_layout [Bindings] : InstructionTrace.layout part47 = part47Layout := by
  rfl

theorem part47_ordered [Bindings] : InstructionTrace.ordered 0x110bce part47 = true := by
  rw [InstructionTrace.ordered_eq_layout, part47_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part47_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x10bce 336 = part47Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
