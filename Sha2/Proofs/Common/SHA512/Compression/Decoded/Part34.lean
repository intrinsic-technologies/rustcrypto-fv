import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part33

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part34 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10fa8d 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fa91 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa94 0x49 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa97 0x49 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fa9a 0x49 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa9d 0x4d 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10faa0 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10faa3 0x49 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10faa7 0x49 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10faaa 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10faad 0x48 0xc7 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fab1 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fab4 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10fab7 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10faba 0x4d 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fabd 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fac0 0x49 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fac4 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fac7 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10faca 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10facd 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fad1 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10fad4 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fad9 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10fadc 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fae4 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fae7 0x49 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10faeb 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10faee 0x49 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10faf2 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10faf5 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10faf8 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fafc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb01 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb04 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fb07 0x49 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb0b 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb0e 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fb11 0x48 (by simp [RexWPrefix]) 3 (.rip 0xf0618) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb18 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb1b 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb1e 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb21 0x4c 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fb24 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb27 0x4c 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb2a 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fb2d 0x49 0xc3 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb31 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb34 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fb37 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb3b 0x4c 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb3e 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fb41 0x49 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb45 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb48 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb4b 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fb4e 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb51 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb54 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fb57 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb5a 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb5d 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb60 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb63 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fb66 0x49 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fb6a 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb6e 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb71 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fb74 0x49 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb78 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb7b 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10fb7e 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb81 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb84 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fb87 0x49 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb8b 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fb8e 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fb91 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fb95 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10fb98 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fb9d 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10fba0 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fba8 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fbab 0x49 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fbaf 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fbb2 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fbb5 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fbb8 0x49 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fbbc 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fbc1 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fbc4 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fbc7 0x49 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fbcb 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fbce 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fbd1 0x49 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fbd5 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fbd8 0x4c (by simp [RexWPrefix]) 11 (.rip 0xf0559) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fbdf 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fbe2 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fbe5 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part34Bytes : List UInt8 :=
  [0x48,0x89,0x1c,0x24,0x49,0x21,0xdb,0x49,0x89,0xd7,0x49,0x31,0xdf,0x49,0x21,0xf7,0x4d,0x31,0xdf,0x4d,0x89,0xf3,0x49,0xc1,0xc3,0x2d,0x49,0x1,0xff,0x4c,0x89,0xf7,0x48,0xc1,0xc7,0x3,0x4c,0x1,0xc1,0x4c,0x89,0xd3,0x48,0xd1,0xcb,0x4d,0x1,0xc7,0x4d,0x89,0xd0,0x49,0xc1,0xc0,0x38,0x4c,0x31,0xdf,0x49,0x31,0xd8,0x4d,0x89,0xd1,0x49,0xc1,0xe9,0x7,0x4d,0x31,0xc1,0x4c,0x1,0x74,0x24,0x50,0x4d,0x1,0xf1,0x4c,0x89,0x8c,0x24,0x88,0x0,0x0,0x0,0x4d,0x89,0xf0,0x49,0xc1,0xe8,0x6,0x49,0x89,0xcb,0x49,0xc1,0xc3,0x32,0x49,0x31,0xf8,0x48,0x89,0xcf,0x48,0xc1,0xc7,0x2e,0x48,0x8b,0x44,0x24,0x20,0x4c,0x1,0xc0,0x49,0x89,0xc8,0x49,0xc1,0xc0,0x17,0x4c,0x31,0xdf,0x49,0x31,0xf8,0x48,0x8b,0x1d,0x18,0x6,0xf,0x0,0x48,0x1,0xc3,0x4c,0x1,0xe3,0x48,0x89,0xef,0x4c,0x31,0xef,0x48,0x21,0xcf,0x4c,0x31,0xef,0x4d,0x89,0xfb,0x49,0xc1,0xc3,0x24,0x48,0x1,0xfb,0x4c,0x89,0xff,0x48,0xc1,0xc7,0x1e,0x4c,0x1,0xc3,0x4d,0x89,0xf8,0x49,0xc1,0xc0,0x19,0x4c,0x31,0xdf,0x49,0x31,0xf8,0x49,0x89,0xf3,0x49,0x21,0xd3,0x48,0x89,0xf7,0x48,0x31,0xd7,0x4c,0x21,0xff,0x4c,0x31,0xdf,0x4c,0x1,0xc7,0x4d,0x89,0xd6,0x4d,0x89,0xd3,0x49,0xc1,0xc3,0x2d,0x4c,0x8b,0x14,0x24,0x49,0x1,0xda,0x4d,0x89,0xf0,0x49,0xc1,0xc0,0x3,0x48,0x1,0xdf,0x48,0x89,0xc3,0x48,0xd1,0xcb,0x4d,0x31,0xd8,0x49,0x89,0xc3,0x49,0xc1,0xc3,0x38,0x49,0x31,0xdb,0x49,0x89,0xc1,0x49,0xc1,0xe9,0x7,0x4d,0x31,0xd9,0x4c,0x1,0x74,0x24,0x78,0x4d,0x1,0xf1,0x4c,0x89,0x8c,0x24,0x90,0x0,0x0,0x0,0x4d,0x89,0xf3,0x49,0xc1,0xeb,0x6,0x4d,0x31,0xc3,0x4d,0x89,0xd1,0x4d,0x89,0xd0,0x49,0xc1,0xc0,0x32,0x4c,0x8b,0x54,0x24,0x38,0x4d,0x1,0xda,0x4d,0x89,0xcb,0x49,0xc1,0xc3,0x2e,0x4d,0x31,0xc3,0x4d,0x89,0xc8,0x49,0xc1,0xc0,0x17,0x4d,0x31,0xd8,0x4c,0x8b,0x1d,0x59,0x5,0xf,0x0,0x4d,0x1,0xd3,0x4d,0x1,0xeb,0x48,0x89,0xcb]

set_option maxRecDepth 4096 in
theorem part34_bytes [Bindings] : part34.flatMap CheckedInstruction.bytes = part34Bytes := by
  rfl

def part34Layout : List (BitVec 64 × Nat) :=
  [(0x10fa8d, 4), (0x10fa91, 3), (0x10fa94, 3), (0x10fa97, 3), (0x10fa9a, 3), (0x10fa9d, 3), (0x10faa0, 3), (0x10faa3, 4), (0x10faa7, 3), (0x10faaa, 3), (0x10faad, 4), (0x10fab1, 3), (0x10fab4, 3), (0x10fab7, 3), (0x10faba, 3), (0x10fabd, 3), (0x10fac0, 4), (0x10fac4, 3), (0x10fac7, 3), (0x10faca, 3), (0x10facd, 4), (0x10fad1, 3), (0x10fad4, 5), (0x10fad9, 3), (0x10fadc, 8), (0x10fae4, 3), (0x10fae7, 4), (0x10faeb, 3), (0x10faee, 4), (0x10faf2, 3), (0x10faf5, 3), (0x10faf8, 4), (0x10fafc, 5), (0x10fb01, 3), (0x10fb04, 3), (0x10fb07, 4), (0x10fb0b, 3), (0x10fb0e, 3), (0x10fb11, 7), (0x10fb18, 3), (0x10fb1b, 3), (0x10fb1e, 3), (0x10fb21, 3), (0x10fb24, 3), (0x10fb27, 3), (0x10fb2a, 3), (0x10fb2d, 4), (0x10fb31, 3), (0x10fb34, 3), (0x10fb37, 4), (0x10fb3b, 3), (0x10fb3e, 3), (0x10fb41, 4), (0x10fb45, 3), (0x10fb48, 3), (0x10fb4b, 3), (0x10fb4e, 3), (0x10fb51, 3), (0x10fb54, 3), (0x10fb57, 3), (0x10fb5a, 3), (0x10fb5d, 3), (0x10fb60, 3), (0x10fb63, 3), (0x10fb66, 4), (0x10fb6a, 4), (0x10fb6e, 3), (0x10fb71, 3), (0x10fb74, 4), (0x10fb78, 3), (0x10fb7b, 3), (0x10fb7e, 3), (0x10fb81, 3), (0x10fb84, 3), (0x10fb87, 4), (0x10fb8b, 3), (0x10fb8e, 3), (0x10fb91, 4), (0x10fb95, 3), (0x10fb98, 5), (0x10fb9d, 3), (0x10fba0, 8), (0x10fba8, 3), (0x10fbab, 4), (0x10fbaf, 3), (0x10fbb2, 3), (0x10fbb5, 3), (0x10fbb8, 4), (0x10fbbc, 5), (0x10fbc1, 3), (0x10fbc4, 3), (0x10fbc7, 4), (0x10fbcb, 3), (0x10fbce, 3), (0x10fbd1, 4), (0x10fbd5, 3), (0x10fbd8, 7), (0x10fbdf, 3), (0x10fbe2, 3), (0x10fbe5, 3)]

theorem part34_layout [Bindings] : InstructionTrace.layout part34 = part34Layout := by
  rfl

theorem part34_ordered [Bindings] : InstructionTrace.ordered 0x10fa8d part34 = true := by
  rw [InstructionTrace.ordered_eq_layout, part34_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part34_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xfa8d 347 = part34Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
