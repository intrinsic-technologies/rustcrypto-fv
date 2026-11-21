import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part35

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part36 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fd36 0x49 0xdc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd39 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fd3c 0x49 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd40 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fd43 0x48 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd47 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd4a 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fd4d 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd51 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fd54 0x48 (by simp [RexWPrefix]) 3 (.rip 0xf03ed) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fd5b 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fd5e 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd61 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd64 0x4d 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd67 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fd6a 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd6d 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fd70 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fd73 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd76 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fd79 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd7d 0x49 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fd80 0x49 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd84 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd87 0x49 0xed (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fd8a 0x49 0xc5 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd8e 0x4d 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd91 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fd94 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd97 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd9a 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fd9d 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fda0 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fda3 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fda6 0x49 0xc6 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fdaa 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fdad 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fdb0 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fdb4 0x49 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fdb7 0x4d 0xe5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10fdba 0x49 0xcd (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fdbd 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fdc0 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fdc3 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fdc7 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fdca 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fdcd 0x4d 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fdd0 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fdd4 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10fdd7 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fddc 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10fddf 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fde4 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fde8 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fdeb 0x49 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fdef 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fdf2 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fdf5 0x49 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fdf9 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fdfe 0x49 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe01 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fe04 0x48 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe08 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe0b 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fe0e 0x4c (by simp [RexWPrefix]) 14 (.rip 0xf033b) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fe15 0x4d 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fe18 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe1b 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe1e 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fe21 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe24 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe27 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fe2a 0x49 0xc3 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fe2e 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe31 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fe34 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fe38 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe3b 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fe3e 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe42 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe45 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe48 0x49 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fe4b 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe4e 0x49 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe51 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fe54 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe57 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fe5a 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe5d 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fe60 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fe64 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe67 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fe6a 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fe6e 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe71 0x4d 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10fe74 0x49 0xce (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe77 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe7a 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fe7d 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe81 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part36Bytes : List UInt8 :=
  [0x49,0x1,0xdc,0x49,0x89,0xf3,0x49,0xc1,0xc3,0x32,0x48,0x89,0xf3,0x48,0xc1,0xc3,0x2e,0x4c,0x31,0xdb,0x49,0x89,0xf3,0x49,0xc1,0xc3,0x17,0x49,0x31,0xdb,0x48,0x8b,0x1d,0xed,0x3,0xf,0x0,0x4c,0x1,0xe3,0x48,0x1,0xcb,0x48,0x89,0xd1,0x4d,0x89,0xea,0x4c,0x31,0xe9,0x48,0x21,0xf1,0x4c,0x31,0xe9,0x48,0x1,0xcb,0x4c,0x1,0xdb,0x48,0x89,0xe9,0x48,0xc1,0xc1,0x24,0x49,0x89,0xeb,0x49,0xc1,0xc3,0x1e,0x49,0x31,0xcb,0x49,0x89,0xed,0x49,0xc1,0xc5,0x19,0x4d,0x31,0xdd,0x4d,0x89,0xc3,0x49,0x21,0xfb,0x4c,0x89,0xc1,0x48,0x31,0xf9,0x48,0x21,0xe9,0x4c,0x31,0xd9,0x49,0x89,0xc6,0x49,0xc1,0xc6,0x2d,0x4c,0x1,0xe9,0x49,0x89,0xc3,0x49,0xc1,0xc3,0x3,0x49,0x1,0xdf,0x4d,0x89,0xe5,0x49,0xd1,0xcd,0x48,0x1,0xd9,0x4c,0x89,0xe3,0x48,0xc1,0xc3,0x38,0x4d,0x31,0xf3,0x4c,0x31,0xeb,0x4d,0x89,0xe1,0x49,0xc1,0xe9,0x7,0x49,0x31,0xd9,0x48,0x1,0x44,0x24,0x10,0x49,0x1,0xc1,0x4c,0x89,0x4c,0x24,0x70,0x48,0xc1,0xe8,0x6,0x4d,0x89,0xfe,0x49,0xc1,0xc6,0x32,0x4c,0x31,0xd8,0x4d,0x89,0xfb,0x49,0xc1,0xc3,0x2e,0x4c,0x8b,0x6c,0x24,0x18,0x49,0x1,0xc5,0x4c,0x89,0xfb,0x48,0xc1,0xc3,0x17,0x4d,0x31,0xf3,0x4c,0x31,0xdb,0x4c,0x8b,0x35,0x3b,0x3,0xf,0x0,0x4d,0x1,0xee,0x4d,0x1,0xd6,0x48,0x89,0xf0,0x48,0x31,0xd0,0x4c,0x21,0xf8,0x48,0x31,0xd0,0x49,0x89,0xcb,0x49,0xc1,0xc3,0x24,0x49,0x1,0xc6,0x48,0x89,0xc8,0x48,0xc1,0xc0,0x1e,0x49,0x1,0xde,0x48,0x89,0xcb,0x48,0xc1,0xc3,0x19,0x4c,0x31,0xd8,0x48,0x31,0xc3,0x49,0x89,0xeb,0x4d,0x21,0xc3,0x49,0x89,0xea,0x4d,0x31,0xc2,0x49,0x21,0xca,0x4d,0x31,0xda,0x49,0x1,0xda,0x4c,0x89,0xe3,0x48,0xc1,0xc3,0x2d,0x4c,0x1,0xf7,0x4d,0x89,0xe3,0x49,0xc1,0xc3,0x3,0x4d,0x1,0xf2,0x4d,0x89,0xee,0x49,0xd1,0xce,0x49,0x31,0xdb,0x4c,0x89,0xeb,0x48,0xc1,0xc3,0x38,0x4c,0x31,0xf3]

set_option maxRecDepth 4096 in
theorem part36_bytes [Bindings] : part36.flatMap CheckedInstruction.bytes = part36Bytes := by
  rfl

def part36Layout : List (BitVec 64 × Nat) :=
  [(0x10fd36, 3), (0x10fd39, 3), (0x10fd3c, 4), (0x10fd40, 3), (0x10fd43, 4), (0x10fd47, 3), (0x10fd4a, 3), (0x10fd4d, 4), (0x10fd51, 3), (0x10fd54, 7), (0x10fd5b, 3), (0x10fd5e, 3), (0x10fd61, 3), (0x10fd64, 3), (0x10fd67, 3), (0x10fd6a, 3), (0x10fd6d, 3), (0x10fd70, 3), (0x10fd73, 3), (0x10fd76, 3), (0x10fd79, 4), (0x10fd7d, 3), (0x10fd80, 4), (0x10fd84, 3), (0x10fd87, 3), (0x10fd8a, 4), (0x10fd8e, 3), (0x10fd91, 3), (0x10fd94, 3), (0x10fd97, 3), (0x10fd9a, 3), (0x10fd9d, 3), (0x10fda0, 3), (0x10fda3, 3), (0x10fda6, 4), (0x10fdaa, 3), (0x10fdad, 3), (0x10fdb0, 4), (0x10fdb4, 3), (0x10fdb7, 3), (0x10fdba, 3), (0x10fdbd, 3), (0x10fdc0, 3), (0x10fdc3, 4), (0x10fdc7, 3), (0x10fdca, 3), (0x10fdcd, 3), (0x10fdd0, 4), (0x10fdd4, 3), (0x10fdd7, 5), (0x10fddc, 3), (0x10fddf, 5), (0x10fde4, 4), (0x10fde8, 3), (0x10fdeb, 4), (0x10fdef, 3), (0x10fdf2, 3), (0x10fdf5, 4), (0x10fdf9, 5), (0x10fdfe, 3), (0x10fe01, 3), (0x10fe04, 4), (0x10fe08, 3), (0x10fe0b, 3), (0x10fe0e, 7), (0x10fe15, 3), (0x10fe18, 3), (0x10fe1b, 3), (0x10fe1e, 3), (0x10fe21, 3), (0x10fe24, 3), (0x10fe27, 3), (0x10fe2a, 4), (0x10fe2e, 3), (0x10fe31, 3), (0x10fe34, 4), (0x10fe38, 3), (0x10fe3b, 3), (0x10fe3e, 4), (0x10fe42, 3), (0x10fe45, 3), (0x10fe48, 3), (0x10fe4b, 3), (0x10fe4e, 3), (0x10fe51, 3), (0x10fe54, 3), (0x10fe57, 3), (0x10fe5a, 3), (0x10fe5d, 3), (0x10fe60, 4), (0x10fe64, 3), (0x10fe67, 3), (0x10fe6a, 4), (0x10fe6e, 3), (0x10fe71, 3), (0x10fe74, 3), (0x10fe77, 3), (0x10fe7a, 3), (0x10fe7d, 4), (0x10fe81, 3)]

theorem part36_layout [Bindings] : InstructionTrace.layout part36 = part36Layout := by
  rfl

theorem part36_ordered [Bindings] : InstructionTrace.ordered 0x10fd36 part36 = true := by
  rw [InstructionTrace.ordered_eq_layout, part36_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part36_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xfd36 334 = part36Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
