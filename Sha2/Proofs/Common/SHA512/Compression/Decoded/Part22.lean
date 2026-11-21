import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part21

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part22 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e9e5 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e9e8 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e9ed 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e9f5 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 264)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e9fd 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 272)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ea05 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ea08 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ea0d 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ea10 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d32 200)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea18 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ea1b 0x48 0xef 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ea1f 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ea22 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ea27 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea2f 0x4d 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ea32 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea3a 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ea3d 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ea40 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ea45 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ea48 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ea50 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ea54 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ea57 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea5f 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea62 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea65 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea68 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ea6b 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea6e 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ea71 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ea74 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea79 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ea7c 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ea80 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ea83 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10ea88 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ea8c 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ea8f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ea94 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ea97 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ea9b 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ea9e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eaa3 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eaa8 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eaab 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10eaae 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10eab6 0x48 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r64_m64_effect_step 0x10eaba 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eac2 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eac7 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10eaca 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ead2 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ead5 0x48 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r64_m64_effect_step 0x10ead9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eae1 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eae6 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10eae9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eaf1 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10eaf4 0x48 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eaf8 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eafb 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eb00 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10eb03 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 192)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10eb0b 0x48 0xed 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eb0f 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eb14 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10eb17 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r64_m64_effect_step 0x10eb1a 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 280)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eb22 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eb25 0x48 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eb29 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eb2c 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10eb2f 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eb33 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10eb36 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eb3b 0x48 0xd5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eb3e 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10eb41 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eb46 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10eb49 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (xor_r64_m64_effect_step 0x10eb4d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10eb55 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 288)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eb5d 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eb60 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 184)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eb68 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eb6b 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eb6f 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eb72 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eb76 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eb79 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eb7c 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eb7f 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eb83 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eb86 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf1503) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eb8d 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eb90 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eb93 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eb9b 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eba3 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part22Bytes : List UInt8 :=
  [0x49,0x31,0xf9,0x48,0x8b,0x7c,0x24,0x20,0x48,0x89,0xbc,0x24,0x0,0x1,0x0,0x0,0x48,0x89,0xbc,0x24,0x8,0x1,0x0,0x0,0x48,0x89,0xbc,0x24,0x10,0x1,0x0,0x0,0x4c,0x1,0xff,0x48,0x89,0x7c,0x24,0x20,0x4d,0x1,0xf9,0x4c,0x89,0x8c,0x24,0xc8,0x0,0x0,0x0,0x4c,0x89,0xff,0x48,0xc1,0xef,0x7,0x48,0x31,0xcf,0x4c,0x8b,0x44,0x24,0x18,0x4c,0x89,0x84,0x24,0xf0,0x0,0x0,0x0,0x4d,0x89,0xc7,0x4c,0x89,0x84,0x24,0xf8,0x0,0x0,0x0,0x4c,0x89,0xd1,0x4d,0x1,0xd0,0x4c,0x89,0x44,0x24,0x18,0x4c,0x1,0xd7,0x48,0x89,0xbc,0x24,0x88,0x0,0x0,0x0,0x48,0xc1,0xe9,0x7,0x48,0x31,0xc1,0x4c,0x8b,0x94,0x24,0xa8,0x0,0x0,0x0,0x4d,0x89,0xd3,0x4d,0x89,0xd1,0x4c,0x89,0xd3,0x4c,0x89,0xf0,0x4d,0x1,0xf2,0x4d,0x89,0xd6,0x48,0x1,0xc1,0x48,0x89,0x4c,0x24,0x60,0x48,0x89,0xc1,0x48,0xc1,0xe9,0x7,0x4c,0x31,0xe1,0x48,0x8b,0x44,0x24,0x28,0x48,0x1,0x4,0x24,0x48,0x1,0xc1,0x48,0x89,0x4c,0x24,0x58,0x48,0x89,0xc1,0x48,0xc1,0xe9,0x7,0x48,0x31,0xe9,0x48,0x8b,0x44,0x24,0x40,0x4c,0x8b,0x54,0x24,0x48,0x49,0x1,0xc2,0x48,0x1,0xc1,0x48,0x89,0x8c,0x24,0xa8,0x0,0x0,0x0,0x48,0xc1,0xe8,0x7,0x48,0x33,0x84,0x24,0xa0,0x0,0x0,0x0,0x48,0x8b,0x4c,0x24,0x10,0x48,0x1,0xc8,0x48,0x89,0x84,0x24,0xa0,0x0,0x0,0x0,0x48,0x89,0xc8,0x48,0xc1,0xe8,0x7,0x48,0x33,0x84,0x24,0x98,0x0,0x0,0x0,0x48,0x8b,0x4c,0x24,0x8,0x48,0x1,0xc8,0x48,0x89,0x84,0x24,0x98,0x0,0x0,0x0,0x48,0x89,0xc8,0x48,0xc1,0xe8,0x7,0x4c,0x31,0xe8,0x48,0x8b,0x6c,0x24,0x68,0x48,0x1,0xe8,0x48,0x89,0x84,0x24,0xc0,0x0,0x0,0x0,0x48,0xc1,0xed,0x7,0x4c,0x8b,0x44,0x24,0x70,0x4c,0x89,0xc1,0x48,0xd1,0xc9,0x48,0x33,0xac,0x24,0x18,0x1,0x0,0x0,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x38,0x48,0x31,0xc8,0x4c,0x89,0xc1,0x48,0xc1,0xe9,0x7,0x48,0x31,0xc1,0x48,0x3,0x6c,0x24,0x30,0x48,0x1,0xd5,0x48,0x1,0xd1,0x48,0x89,0x4c,0x24,0x10,0x48,0x89,0xd0,0x48,0xc1,0xe8,0x6,0x48,0x33,0x84,0x24,0xd0,0x0,0x0,0x0,0x4c,0x3,0x94,0x24,0x20,0x1,0x0,0x0,0x49,0x1,0xc2,0x48,0x8b,0x94,0x24,0xb8,0x0,0x0,0x0,0x48,0x89,0xd0,0x48,0xc1,0xc0,0x32,0x48,0x89,0xd1,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xd0,0x48,0x89,0xd7,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x3,0x15,0xf,0x0,0x4c,0x1,0xd1,0x48,0x1,0xf1,0x48,0x8b,0xb4,0x24,0x80,0x0,0x0,0x0,0x48,0x8b,0x94,0x24,0xd8,0x0,0x0,0x0,0x48,0x31,0xd6]

set_option maxRecDepth 4096 in
theorem part22_bytes [Bindings] : part22.flatMap CheckedInstruction.bytes = part22Bytes := by
  rfl

def part22Layout : List (BitVec 64 × Nat) :=
  [(0x10e9e5, 3), (0x10e9e8, 5), (0x10e9ed, 8), (0x10e9f5, 8), (0x10e9fd, 8), (0x10ea05, 3), (0x10ea08, 5), (0x10ea0d, 3), (0x10ea10, 8), (0x10ea18, 3), (0x10ea1b, 4), (0x10ea1f, 3), (0x10ea22, 5), (0x10ea27, 8), (0x10ea2f, 3), (0x10ea32, 8), (0x10ea3a, 3), (0x10ea3d, 3), (0x10ea40, 5), (0x10ea45, 3), (0x10ea48, 8), (0x10ea50, 4), (0x10ea54, 3), (0x10ea57, 8), (0x10ea5f, 3), (0x10ea62, 3), (0x10ea65, 3), (0x10ea68, 3), (0x10ea6b, 3), (0x10ea6e, 3), (0x10ea71, 3), (0x10ea74, 5), (0x10ea79, 3), (0x10ea7c, 4), (0x10ea80, 3), (0x10ea83, 5), (0x10ea88, 4), (0x10ea8c, 3), (0x10ea8f, 5), (0x10ea94, 3), (0x10ea97, 4), (0x10ea9b, 3), (0x10ea9e, 5), (0x10eaa3, 5), (0x10eaa8, 3), (0x10eaab, 3), (0x10eaae, 8), (0x10eab6, 4), (0x10eaba, 8), (0x10eac2, 5), (0x10eac7, 3), (0x10eaca, 8), (0x10ead2, 3), (0x10ead5, 4), (0x10ead9, 8), (0x10eae1, 5), (0x10eae6, 3), (0x10eae9, 8), (0x10eaf1, 3), (0x10eaf4, 4), (0x10eaf8, 3), (0x10eafb, 5), (0x10eb00, 3), (0x10eb03, 8), (0x10eb0b, 4), (0x10eb0f, 5), (0x10eb14, 3), (0x10eb17, 3), (0x10eb1a, 8), (0x10eb22, 3), (0x10eb25, 4), (0x10eb29, 3), (0x10eb2c, 3), (0x10eb2f, 4), (0x10eb33, 3), (0x10eb36, 5), (0x10eb3b, 3), (0x10eb3e, 3), (0x10eb41, 5), (0x10eb46, 3), (0x10eb49, 4), (0x10eb4d, 8), (0x10eb55, 8), (0x10eb5d, 3), (0x10eb60, 8), (0x10eb68, 3), (0x10eb6b, 4), (0x10eb6f, 3), (0x10eb72, 4), (0x10eb76, 3), (0x10eb79, 3), (0x10eb7c, 3), (0x10eb7f, 4), (0x10eb83, 3), (0x10eb86, 7), (0x10eb8d, 3), (0x10eb90, 3), (0x10eb93, 8), (0x10eb9b, 8), (0x10eba3, 3)]

theorem part22_layout [Bindings] : InstructionTrace.layout part22 = part22Layout := by
  rfl

theorem part22_ordered [Bindings] : InstructionTrace.ordered 0x10e9e5 part22 = true := by
  rw [InstructionTrace.ordered_eq_layout, part22_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part22_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe9e5 449 = part22Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
