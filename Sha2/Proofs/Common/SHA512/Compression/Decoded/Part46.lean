import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part45

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part46 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a7b 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110a7e 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef753) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110a85 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110a88 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a8b 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a8e 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110a91 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a94 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110a97 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a9a 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110a9d 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110aa1 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110aa4 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110aa7 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110aab 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110aae 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110ab1 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ab5 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ab8 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110abb 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110abe 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ac1 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110ac4 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ac7 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110aca 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110acd 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ad0 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110ad3 0x48 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ad7 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ada 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110add 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ae1 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ae4 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110ae7 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110aea 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110aed 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110af1 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110af4 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110af7 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110afb 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110afe 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b06 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110b09 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b0e 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110b11 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b15 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110b18 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b1d 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b20 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110b23 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b27 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110b2a 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b2e 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b31 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110b34 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b38 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110b3b 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef69e) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b42 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b45 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b48 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b4b 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110b4e 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b51 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b54 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b57 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b5a 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110b5d 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b61 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110b64 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b68 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b6b 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110b6e 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b72 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b75 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110b78 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b7b 0x48 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b7e 0x4c 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110b81 0x48 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110b84 0x48 0xd5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b87 0x48 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b8a 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110b8d 0x48 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b90 0x4c 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b93 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110b96 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110b9a 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110b9d 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ba1 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ba4 0x4d 0xd4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ba7 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110baa 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110bad 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110bb0 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110bb4 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110bb7 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110bba 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110bbe 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110bc1 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110bc6 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110bc9 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
  ]

def part46Bytes : List UInt8 :=
  [0x48,0x31,0xc8,0x48,0x8b,0xd,0x53,0xf7,0xe,0x0,0x4c,0x1,0xe1,0x48,0x1,0xd1,0x4c,0x89,0xca,0x48,0x31,0xf2,0x4c,0x21,0xfa,0x48,0x31,0xf2,0x48,0x1,0xd1,0x48,0x89,0xfa,0x48,0xc1,0xc2,0x24,0x48,0x1,0xc1,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x1e,0x48,0x31,0xd0,0x48,0x89,0xfa,0x48,0xc1,0xc2,0x19,0x48,0x31,0xc2,0x4c,0x89,0xf0,0x4c,0x21,0xd8,0x4c,0x89,0xf3,0x4c,0x31,0xdb,0x48,0x21,0xfb,0x48,0x31,0xc3,0x48,0x1,0xd3,0x49,0x1,0xc8,0x4c,0x89,0xd2,0x48,0xc1,0xc2,0x2d,0x48,0x1,0xcb,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x3,0x48,0x31,0xd0,0x4c,0x89,0xe1,0x48,0xd1,0xc9,0x4c,0x89,0xe2,0x48,0xc1,0xc2,0x38,0x48,0x31,0xca,0x4c,0x89,0xe1,0x48,0xc1,0xe9,0x7,0x48,0x31,0xd1,0x4c,0x1,0x94,0x24,0x80,0x0,0x0,0x0,0x4c,0x1,0xd1,0x48,0x89,0x4c,0x24,0x50,0x4c,0x89,0xd1,0x48,0xc1,0xe9,0x6,0x48,0x31,0xc1,0x4c,0x8b,0x54,0x24,0x68,0x49,0x1,0xca,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x32,0x4c,0x89,0xc1,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x9e,0xf6,0xe,0x0,0x4c,0x1,0xd1,0x48,0x1,0xf1,0x4c,0x89,0xfa,0x4c,0x31,0xca,0x4c,0x21,0xc2,0x4c,0x31,0xca,0x48,0x1,0xd1,0x48,0x1,0xc1,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x24,0x48,0x89,0xda,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xc2,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xd0,0x48,0x89,0xfa,0x4c,0x21,0xf2,0x48,0x89,0xfd,0x4c,0x31,0xf5,0x48,0x21,0xdd,0x48,0x31,0xd5,0x48,0x1,0xc5,0x49,0x1,0xcb,0x48,0x1,0xcd,0x4c,0x89,0xe6,0x4c,0x89,0xe1,0x48,0xc1,0xc1,0x2d,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x3,0x48,0x31,0xc8,0x4d,0x89,0xd4,0x4c,0x89,0xd1,0x48,0xd1,0xc9,0x4c,0x89,0xd2,0x48,0xc1,0xc2,0x38,0x48,0x31,0xca,0x4c,0x89,0xd1,0x48,0xc1,0xe9,0x7,0x48,0x31,0xd1,0x48,0x1,0x74,0x24,0x28,0x48,0x1,0xf1,0x48,0x89,0x4c,0x24,0x48]

set_option maxRecDepth 4096 in
theorem part46_bytes [Bindings] : part46.flatMap CheckedInstruction.bytes = part46Bytes := by
  rfl

def part46Layout : List (BitVec 64 × Nat) :=
  [(0x110a7b, 3), (0x110a7e, 7), (0x110a85, 3), (0x110a88, 3), (0x110a8b, 3), (0x110a8e, 3), (0x110a91, 3), (0x110a94, 3), (0x110a97, 3), (0x110a9a, 3), (0x110a9d, 4), (0x110aa1, 3), (0x110aa4, 3), (0x110aa7, 4), (0x110aab, 3), (0x110aae, 3), (0x110ab1, 4), (0x110ab5, 3), (0x110ab8, 3), (0x110abb, 3), (0x110abe, 3), (0x110ac1, 3), (0x110ac4, 3), (0x110ac7, 3), (0x110aca, 3), (0x110acd, 3), (0x110ad0, 3), (0x110ad3, 4), (0x110ad7, 3), (0x110ada, 3), (0x110add, 4), (0x110ae1, 3), (0x110ae4, 3), (0x110ae7, 3), (0x110aea, 3), (0x110aed, 4), (0x110af1, 3), (0x110af4, 3), (0x110af7, 4), (0x110afb, 3), (0x110afe, 8), (0x110b06, 3), (0x110b09, 5), (0x110b0e, 3), (0x110b11, 4), (0x110b15, 3), (0x110b18, 5), (0x110b1d, 3), (0x110b20, 3), (0x110b23, 4), (0x110b27, 3), (0x110b2a, 4), (0x110b2e, 3), (0x110b31, 3), (0x110b34, 4), (0x110b38, 3), (0x110b3b, 7), (0x110b42, 3), (0x110b45, 3), (0x110b48, 3), (0x110b4b, 3), (0x110b4e, 3), (0x110b51, 3), (0x110b54, 3), (0x110b57, 3), (0x110b5a, 3), (0x110b5d, 4), (0x110b61, 3), (0x110b64, 4), (0x110b68, 3), (0x110b6b, 3), (0x110b6e, 4), (0x110b72, 3), (0x110b75, 3), (0x110b78, 3), (0x110b7b, 3), (0x110b7e, 3), (0x110b81, 3), (0x110b84, 3), (0x110b87, 3), (0x110b8a, 3), (0x110b8d, 3), (0x110b90, 3), (0x110b93, 3), (0x110b96, 4), (0x110b9a, 3), (0x110b9d, 4), (0x110ba1, 3), (0x110ba4, 3), (0x110ba7, 3), (0x110baa, 3), (0x110bad, 3), (0x110bb0, 4), (0x110bb4, 3), (0x110bb7, 3), (0x110bba, 4), (0x110bbe, 3), (0x110bc1, 5), (0x110bc6, 3), (0x110bc9, 5)]

theorem part46_layout [Bindings] : InstructionTrace.layout part46 = part46Layout := by
  rfl

theorem part46_ordered [Bindings] : InstructionTrace.ordered 0x110a7b part46 = true := by
  rw [InstructionTrace.ordered_eq_layout, part46_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part46_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x10a7b 339 = part46Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
