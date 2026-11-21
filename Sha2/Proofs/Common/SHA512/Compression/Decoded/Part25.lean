import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part24

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part25 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ee8c 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ee8f 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee92 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ee95 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee99 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ee9c 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eea0 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eea3 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eea6 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eeaa 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eead 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10eeb0 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eeb3 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eeb6 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10eeb9 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eebc 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eebf 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eec2 0x49 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eec5 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eec8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eecd 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10eed0 0x48 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eed3 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eed6 0x49 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eeda 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eedd 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eee0 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eee3 0x48 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10eee7 0x48 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eeeb 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eeee 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eef2 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eef5 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10eef8 0x49 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eefb 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eefe 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ef01 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef05 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef08 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ef0b 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef0f 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10ef12 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ef1a 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ef1d 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ef22 0x49 0xee 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef26 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef29 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ef2c 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ef30 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ef35 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef38 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ef3b 0x48 0xc0 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ef3f 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef42 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ef45 0x48 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef49 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef4c 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ef4f 0x4c (by simp [RexWPrefix]) 10 (.rip 0xf115a) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ef56 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10ef59 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef5e 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ef61 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef66 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ef69 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef6c 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef6f 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ef72 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ef76 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef79 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ef7c 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ef80 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef83 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ef86 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef8a 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef8d 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef90 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ef93 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ef96 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef99 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ef9c 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ef9f 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10efa2 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10efa5 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10efa8 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10efac 0x4d 0xd4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10efaf 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10efb2 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10efb6 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10efb9 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10efbc 0x48 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10efbf 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10efc2 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10efc5 0x48 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10efc9 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10efcc 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10efcf 0x48 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10efd3 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10efd6 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10efdb 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10efde 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
  ]

def part25Bytes : List UInt8 :=
  [0x4c,0x1,0xc9,0x48,0x1,0xc1,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x24,0x48,0x89,0xfa,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xc2,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xd0,0x48,0x89,0xda,0x4c,0x21,0xe2,0x49,0x89,0xd8,0x4d,0x31,0xe0,0x49,0x21,0xf8,0x49,0x31,0xd0,0x49,0x1,0xc0,0x49,0x1,0xcd,0x49,0x1,0xc8,0x48,0x8b,0x4c,0x24,0x30,0x48,0x89,0xc8,0x48,0xd1,0xc8,0x49,0x89,0xc9,0x49,0xc1,0xc1,0x38,0x49,0x31,0xc1,0x48,0x89,0xc8,0x4c,0x89,0xf2,0x48,0xc1,0xc2,0x2d,0x48,0xc1,0xe8,0x7,0x4c,0x89,0xf1,0x48,0xc1,0xc1,0x3,0x4c,0x31,0xc8,0x49,0x89,0xf1,0x49,0xd1,0xc9,0x48,0x31,0xd1,0x48,0x89,0xf2,0x48,0xc1,0xc2,0x38,0x4c,0x31,0xca,0x49,0x89,0xf1,0x49,0xc1,0xe9,0x7,0x49,0x31,0xd1,0x4c,0x1,0xb4,0x24,0xa8,0x0,0x0,0x0,0x4d,0x1,0xf1,0x4c,0x89,0x4c,0x24,0x28,0x49,0xc1,0xee,0x6,0x49,0x31,0xce,0x4c,0x89,0xe9,0x48,0xc1,0xc1,0x32,0x4c,0x8b,0x5c,0x24,0x20,0x49,0x1,0xc3,0x4c,0x89,0xe8,0x48,0xc1,0xc0,0x2e,0x4d,0x1,0xf3,0x4c,0x89,0xea,0x48,0xc1,0xc2,0x17,0x48,0x31,0xc8,0x48,0x31,0xc2,0x4c,0x8b,0x15,0x5a,0x11,0xf,0x0,0x4d,0x1,0xda,0x4c,0x3,0x54,0x24,0x38,0x4c,0x89,0xf8,0x4c,0x8b,0x74,0x24,0x50,0x4c,0x31,0xf0,0x4c,0x21,0xe8,0x4c,0x31,0xf0,0x4c,0x89,0xc1,0x48,0xc1,0xc1,0x24,0x49,0x1,0xc2,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x1e,0x49,0x1,0xd2,0x4c,0x89,0xc2,0x48,0xc1,0xc2,0x19,0x48,0x31,0xc8,0x48,0x31,0xc2,0x48,0x89,0xf8,0x48,0x21,0xd8,0x49,0x89,0xf9,0x49,0x31,0xd9,0x4d,0x21,0xc1,0x49,0x31,0xc1,0x49,0x1,0xd1,0x48,0x89,0xf1,0x48,0xc1,0xc1,0x2d,0x4d,0x1,0xd4,0x48,0x89,0xf0,0x48,0xc1,0xc0,0x3,0x4d,0x1,0xd1,0x4c,0x89,0xda,0x48,0xd1,0xca,0x48,0x31,0xc8,0x4c,0x89,0xd9,0x48,0xc1,0xc1,0x38,0x48,0x31,0xd1,0x4c,0x89,0xda,0x48,0xc1,0xea,0x7,0x48,0x31,0xca,0x48,0x1,0x74,0x24,0x58,0x48,0x1,0xf2,0x48,0x89,0x54,0x24,0x40]

set_option maxRecDepth 4096 in
theorem part25_bytes [Bindings] : part25.flatMap CheckedInstruction.bytes = part25Bytes := by
  rfl

def part25Layout : List (BitVec 64 × Nat) :=
  [(0x10ee8c, 3), (0x10ee8f, 3), (0x10ee92, 3), (0x10ee95, 4), (0x10ee99, 3), (0x10ee9c, 4), (0x10eea0, 3), (0x10eea3, 3), (0x10eea6, 4), (0x10eeaa, 3), (0x10eead, 3), (0x10eeb0, 3), (0x10eeb3, 3), (0x10eeb6, 3), (0x10eeb9, 3), (0x10eebc, 3), (0x10eebf, 3), (0x10eec2, 3), (0x10eec5, 3), (0x10eec8, 5), (0x10eecd, 3), (0x10eed0, 3), (0x10eed3, 3), (0x10eed6, 4), (0x10eeda, 3), (0x10eedd, 3), (0x10eee0, 3), (0x10eee3, 4), (0x10eee7, 4), (0x10eeeb, 3), (0x10eeee, 4), (0x10eef2, 3), (0x10eef5, 3), (0x10eef8, 3), (0x10eefb, 3), (0x10eefe, 3), (0x10ef01, 4), (0x10ef05, 3), (0x10ef08, 3), (0x10ef0b, 4), (0x10ef0f, 3), (0x10ef12, 8), (0x10ef1a, 3), (0x10ef1d, 5), (0x10ef22, 4), (0x10ef26, 3), (0x10ef29, 3), (0x10ef2c, 4), (0x10ef30, 5), (0x10ef35, 3), (0x10ef38, 3), (0x10ef3b, 4), (0x10ef3f, 3), (0x10ef42, 3), (0x10ef45, 4), (0x10ef49, 3), (0x10ef4c, 3), (0x10ef4f, 7), (0x10ef56, 3), (0x10ef59, 5), (0x10ef5e, 3), (0x10ef61, 5), (0x10ef66, 3), (0x10ef69, 3), (0x10ef6c, 3), (0x10ef6f, 3), (0x10ef72, 4), (0x10ef76, 3), (0x10ef79, 3), (0x10ef7c, 4), (0x10ef80, 3), (0x10ef83, 3), (0x10ef86, 4), (0x10ef8a, 3), (0x10ef8d, 3), (0x10ef90, 3), (0x10ef93, 3), (0x10ef96, 3), (0x10ef99, 3), (0x10ef9c, 3), (0x10ef9f, 3), (0x10efa2, 3), (0x10efa5, 3), (0x10efa8, 4), (0x10efac, 3), (0x10efaf, 3), (0x10efb2, 4), (0x10efb6, 3), (0x10efb9, 3), (0x10efbc, 3), (0x10efbf, 3), (0x10efc2, 3), (0x10efc5, 4), (0x10efc9, 3), (0x10efcc, 3), (0x10efcf, 4), (0x10efd3, 3), (0x10efd6, 5), (0x10efdb, 3), (0x10efde, 5)]

theorem part25_layout [Bindings] : InstructionTrace.layout part25 = part25Layout := by
  rfl

theorem part25_ordered [Bindings] : InstructionTrace.ordered 0x10ee8c part25 = true := by
  rw [InstructionTrace.ordered_eq_layout, part25_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part25_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xee8c 343 = part25Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
