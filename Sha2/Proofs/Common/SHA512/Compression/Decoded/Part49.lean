import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part48

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part49 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e72 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110e75 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e79 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110e7c 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110e84 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e87 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e8a 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e8e 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e91 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e95 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e98 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e9b 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e9f 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110ea2 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef35f) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ea9 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110eac 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110eaf 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110eb2 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110eb5 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110eb8 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ebb 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ebe 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ec1 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110ec4 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ec8 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110ecb 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ecf 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ed2 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110ed5 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ed9 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110edc 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110edf 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ee2 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110ee5 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110ee8 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110eeb 0x49 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110eee 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ef1 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ef4 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110ef7 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110efc 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110eff 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f03 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f06 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f0a 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f0d 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110f10 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f14 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f17 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f1b 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f1e 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f21 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110f25 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110f2a 0x49 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f2d 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f30 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f34 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f37 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110f3a 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef2cf) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110f41 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110f44 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f47 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f4a 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110f4d 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f50 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f53 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f56 0x48 0xc7 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110f5a 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f5d 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f60 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110f64 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f67 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f6a 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f6e 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f71 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f74 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110f77 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f7a 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f7d 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110f80 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f83 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110f86 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f89 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f8c 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110f90 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110f93 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110f96 0x48 0xc2 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110f9a 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110f9d 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110fa0 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110fa5 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110fa8 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110fac 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110faf 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110fb3 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110fb6 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110fb9 0x48 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110fbd 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110fc2 0x49 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110fc5 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part49Bytes : List UInt8 :=
  [0x4c,0x89,0xe0,0x48,0xc1,0xe8,0x6,0x48,0x31,0xc8,0x4c,0x8b,0x9c,0x24,0x80,0x0,0x0,0x0,0x49,0x1,0xc3,0x48,0x89,0xe8,0x48,0xc1,0xc0,0x32,0x48,0x89,0xe9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xe8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x5f,0xf3,0xe,0x0,0x4c,0x1,0xd9,0x4c,0x1,0xf1,0x48,0x89,0xda,0x48,0x31,0xfa,0x48,0x21,0xea,0x48,0x31,0xfa,0x48,0x1,0xd1,0x48,0x1,0xc1,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x24,0x4c,0x89,0xfa,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xc2,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xd0,0x4c,0x89,0xc2,0x48,0x21,0xf2,0x4d,0x89,0xc6,0x49,0x31,0xf6,0x4d,0x21,0xfe,0x49,0x31,0xd6,0x49,0x1,0xc6,0x49,0x1,0xca,0x49,0x1,0xce,0x4c,0x89,0x4c,0x24,0x10,0x4c,0x89,0xc8,0x48,0xc1,0xc0,0x2d,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x3,0x48,0x31,0xc1,0x4c,0x89,0xc8,0x48,0xc1,0xe8,0x6,0x4c,0x89,0xd2,0x48,0xc1,0xc2,0x32,0x48,0x31,0xc8,0x4c,0x89,0xd1,0x48,0xc1,0xc1,0x2e,0x4c,0x8b,0x64,0x24,0x28,0x49,0x1,0xc4,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x17,0x48,0x31,0xd1,0x48,0x31,0xc8,0x48,0x8b,0xd,0xcf,0xf2,0xe,0x0,0x4c,0x1,0xe1,0x48,0x1,0xf9,0x48,0x89,0xea,0x48,0x31,0xda,0x4c,0x21,0xd2,0x48,0x31,0xda,0x4c,0x89,0xf7,0x48,0xc1,0xc7,0x24,0x48,0x1,0xd1,0x4c,0x89,0xf2,0x48,0xc1,0xc2,0x1e,0x48,0x1,0xc1,0x4c,0x89,0xf0,0x48,0xc1,0xc0,0x19,0x48,0x31,0xfa,0x48,0x31,0xd0,0x4c,0x89,0xfa,0x4c,0x21,0xc2,0x4d,0x89,0xf9,0x4d,0x31,0xc1,0x4d,0x21,0xf1,0x49,0x31,0xd1,0x49,0x1,0xc1,0x4c,0x89,0xd8,0x48,0xc1,0xc0,0x2d,0x48,0x1,0xce,0x4c,0x89,0xda,0x48,0xc1,0xc2,0x3,0x49,0x1,0xc9,0x48,0x31,0xc2,0x4c,0x1,0x5c,0x24,0x8,0x4c,0x89,0xd8,0x48,0xc1,0xe8,0x6,0x48,0x89,0xf1,0x48,0xc1,0xc1,0x32,0x48,0x31,0xd0,0x48,0x89,0xf2,0x48,0xc1,0xc2,0x2e,0x4c,0x8b,0x6c,0x24,0x78,0x49,0x1,0xc5,0x48,0x89,0xf0]

set_option maxRecDepth 4096 in
theorem part49_bytes [Bindings] : part49.flatMap CheckedInstruction.bytes = part49Bytes := by
  rfl

def part49Layout : List (BitVec 64 × Nat) :=
  [(0x110e72, 3), (0x110e75, 4), (0x110e79, 3), (0x110e7c, 8), (0x110e84, 3), (0x110e87, 3), (0x110e8a, 4), (0x110e8e, 3), (0x110e91, 4), (0x110e95, 3), (0x110e98, 3), (0x110e9b, 4), (0x110e9f, 3), (0x110ea2, 7), (0x110ea9, 3), (0x110eac, 3), (0x110eaf, 3), (0x110eb2, 3), (0x110eb5, 3), (0x110eb8, 3), (0x110ebb, 3), (0x110ebe, 3), (0x110ec1, 3), (0x110ec4, 4), (0x110ec8, 3), (0x110ecb, 4), (0x110ecf, 3), (0x110ed2, 3), (0x110ed5, 4), (0x110ed9, 3), (0x110edc, 3), (0x110edf, 3), (0x110ee2, 3), (0x110ee5, 3), (0x110ee8, 3), (0x110eeb, 3), (0x110eee, 3), (0x110ef1, 3), (0x110ef4, 3), (0x110ef7, 5), (0x110efc, 3), (0x110eff, 4), (0x110f03, 3), (0x110f06, 4), (0x110f0a, 3), (0x110f0d, 3), (0x110f10, 4), (0x110f14, 3), (0x110f17, 4), (0x110f1b, 3), (0x110f1e, 3), (0x110f21, 4), (0x110f25, 5), (0x110f2a, 3), (0x110f2d, 3), (0x110f30, 4), (0x110f34, 3), (0x110f37, 3), (0x110f3a, 7), (0x110f41, 3), (0x110f44, 3), (0x110f47, 3), (0x110f4a, 3), (0x110f4d, 3), (0x110f50, 3), (0x110f53, 3), (0x110f56, 4), (0x110f5a, 3), (0x110f5d, 3), (0x110f60, 4), (0x110f64, 3), (0x110f67, 3), (0x110f6a, 4), (0x110f6e, 3), (0x110f71, 3), (0x110f74, 3), (0x110f77, 3), (0x110f7a, 3), (0x110f7d, 3), (0x110f80, 3), (0x110f83, 3), (0x110f86, 3), (0x110f89, 3), (0x110f8c, 4), (0x110f90, 3), (0x110f93, 3), (0x110f96, 4), (0x110f9a, 3), (0x110f9d, 3), (0x110fa0, 5), (0x110fa5, 3), (0x110fa8, 4), (0x110fac, 3), (0x110faf, 4), (0x110fb3, 3), (0x110fb6, 3), (0x110fb9, 4), (0x110fbd, 5), (0x110fc2, 3), (0x110fc5, 3)]

theorem part49_layout [Bindings] : InstructionTrace.layout part49 = part49Layout := by
  rfl

theorem part49_ordered [Bindings] : InstructionTrace.ordered 0x110e72 part49 = true := by
  rw [InstructionTrace.ordered_eq_layout, part49_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part49_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x10e72 342 = part49Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
