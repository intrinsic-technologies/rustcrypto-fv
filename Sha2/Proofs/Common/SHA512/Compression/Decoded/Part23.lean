import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part22

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part23 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r64_r64_effect_step 0x10eba6 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eba9 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ebac 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ebaf 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ebb2 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d32 296)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ebba 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ebbd 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ebc1 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ebc4 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ebc8 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ebcb 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ebce 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ebd2 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ebd5 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ebda 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ebdd 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ebe2 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ebe5 0x49 0xd4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ebe8 0x4d 0xec (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ebeb 0x49 0xfc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ebee 0x49 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ebf1 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ebf6 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ebf9 0x49 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10ebfc 0x49 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ebff 0x49 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ec03 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec06 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ec09 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ec0d 0x48 0xeb 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec11 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ec14 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ec18 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec1b 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10ec1e 0x48 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ec21 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec24 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ec27 0x48 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ec2b 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec2e 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec31 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ec34 0x48 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ec38 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10ec3b 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 192)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ec43 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ec46 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec4b 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ec4e 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ec52 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec55 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec58 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ec5b 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ec5f 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ec63 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec66 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ec69 0x48 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ec6d 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec70 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ec73 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ec77 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ec7a 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ec7d 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf1414) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ec84 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10ec87 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ec8f 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d32 184)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ec97 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ec9a 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eca2 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10eca5 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10eca8 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ecad 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ecb0 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ecb3 0x48 0xc7 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ecb7 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ecba 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ecbd 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ecc1 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ecc4 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ecc7 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10eccb 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ecce 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ecd1 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ecd4 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ecd9 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ecdc 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ecdf 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ece2 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ece5 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ece8 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eceb 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ecf0 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ecf3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10ecfb 0x48 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ecfe 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ed01 0x49 0xc7 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed05 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ed08 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ed10 0x48 0xef 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed14 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ed17 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
  ]

def part23Bytes : List UInt8 :=
  [0x48,0x21,0xfe,0x48,0x31,0xd6,0x48,0x1,0xf1,0x48,0x1,0xc1,0x4c,0x8b,0xac,0x24,0x28,0x1,0x0,0x0,0x4c,0x89,0xe8,0x48,0xc1,0xc0,0x24,0x4c,0x89,0xee,0x48,0xc1,0xc6,0x1e,0x48,0x31,0xc6,0x4c,0x89,0xe8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xf0,0x4c,0x8b,0x64,0x24,0x78,0x4c,0x89,0xe7,0x48,0x8b,0x54,0x24,0x50,0x48,0x21,0xd7,0x49,0x31,0xd4,0x4d,0x21,0xec,0x49,0x31,0xfc,0x49,0x1,0xc4,0x48,0x8b,0x7c,0x24,0x38,0x48,0x1,0xcf,0x49,0x1,0xcc,0x49,0xd1,0xcb,0x49,0xc1,0xc1,0x38,0x4d,0x31,0xd9,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x2d,0x48,0xc1,0xeb,0x7,0x4c,0x89,0xc1,0x48,0xc1,0xc1,0x3,0x4c,0x31,0xcb,0x4c,0x89,0xd2,0x48,0xd1,0xca,0x48,0x31,0xc1,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x38,0x48,0x31,0xd0,0x4c,0x89,0xd2,0x4c,0x89,0xd6,0x48,0xc1,0xea,0x7,0x48,0x31,0xc2,0x4c,0x1,0x84,0x24,0xc0,0x0,0x0,0x0,0x4c,0x1,0xc2,0x48,0x89,0x54,0x24,0x8,0x4c,0x89,0xc0,0x48,0xc1,0xe8,0x6,0x48,0x31,0xc8,0x49,0x89,0xfa,0x48,0x89,0xf9,0x48,0xc1,0xc1,0x32,0x4c,0x8b,0x4,0x24,0x49,0x1,0xd8,0x48,0x89,0xfa,0x48,0xc1,0xc2,0x2e,0x49,0x1,0xc0,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xca,0x48,0x31,0xd0,0x48,0x8b,0xd,0x14,0x14,0xf,0x0,0x4c,0x1,0xc1,0x48,0x3,0x8c,0x24,0xd8,0x0,0x0,0x0,0x4c,0x8b,0x9c,0x24,0xb8,0x0,0x0,0x0,0x4c,0x89,0xda,0x48,0x8b,0xbc,0x24,0x80,0x0,0x0,0x0,0x48,0x31,0xfa,0x4c,0x21,0xd2,0x4c,0x89,0x54,0x24,0x38,0x48,0x31,0xfa,0x4c,0x89,0xe7,0x48,0xc1,0xc7,0x24,0x48,0x1,0xd1,0x4c,0x89,0xe2,0x48,0xc1,0xc2,0x1e,0x48,0x1,0xc1,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x19,0x48,0x31,0xfa,0x48,0x31,0xd0,0x4c,0x89,0xea,0x48,0x8b,0x7c,0x24,0x78,0x48,0x21,0xfa,0x4c,0x89,0xeb,0x48,0x31,0xfb,0x4c,0x21,0xe3,0x48,0x31,0xd3,0x48,0x1,0xc3,0x4c,0x8b,0x4c,0x24,0x50,0x49,0x1,0xc9,0x48,0x8b,0x84,0x24,0xf0,0x0,0x0,0x0,0x48,0xd1,0xc8,0x48,0x1,0xcb,0x49,0xc1,0xc7,0x38,0x49,0x31,0xc7,0x48,0x8b,0xbc,0x24,0xf8,0x0,0x0,0x0,0x48,0xc1,0xef,0x7,0x48,0x89,0xf1,0x48,0xc1,0xc1,0x2d]

set_option maxRecDepth 4096 in
theorem part23_bytes [Bindings] : part23.flatMap CheckedInstruction.bytes = part23Bytes := by
  rfl

def part23Layout : List (BitVec 64 × Nat) :=
  [(0x10eba6, 3), (0x10eba9, 3), (0x10ebac, 3), (0x10ebaf, 3), (0x10ebb2, 8), (0x10ebba, 3), (0x10ebbd, 4), (0x10ebc1, 3), (0x10ebc4, 4), (0x10ebc8, 3), (0x10ebcb, 3), (0x10ebce, 4), (0x10ebd2, 3), (0x10ebd5, 5), (0x10ebda, 3), (0x10ebdd, 5), (0x10ebe2, 3), (0x10ebe5, 3), (0x10ebe8, 3), (0x10ebeb, 3), (0x10ebee, 3), (0x10ebf1, 5), (0x10ebf6, 3), (0x10ebf9, 3), (0x10ebfc, 3), (0x10ebff, 4), (0x10ec03, 3), (0x10ec06, 3), (0x10ec09, 4), (0x10ec0d, 4), (0x10ec11, 3), (0x10ec14, 4), (0x10ec18, 3), (0x10ec1b, 3), (0x10ec1e, 3), (0x10ec21, 3), (0x10ec24, 3), (0x10ec27, 4), (0x10ec2b, 3), (0x10ec2e, 3), (0x10ec31, 3), (0x10ec34, 4), (0x10ec38, 3), (0x10ec3b, 8), (0x10ec43, 3), (0x10ec46, 5), (0x10ec4b, 3), (0x10ec4e, 4), (0x10ec52, 3), (0x10ec55, 3), (0x10ec58, 3), (0x10ec5b, 4), (0x10ec5f, 4), (0x10ec63, 3), (0x10ec66, 3), (0x10ec69, 4), (0x10ec6d, 3), (0x10ec70, 3), (0x10ec73, 4), (0x10ec77, 3), (0x10ec7a, 3), (0x10ec7d, 7), (0x10ec84, 3), (0x10ec87, 8), (0x10ec8f, 8), (0x10ec97, 3), (0x10ec9a, 8), (0x10eca2, 3), (0x10eca5, 3), (0x10eca8, 5), (0x10ecad, 3), (0x10ecb0, 3), (0x10ecb3, 4), (0x10ecb7, 3), (0x10ecba, 3), (0x10ecbd, 4), (0x10ecc1, 3), (0x10ecc4, 3), (0x10ecc7, 4), (0x10eccb, 3), (0x10ecce, 3), (0x10ecd1, 3), (0x10ecd4, 5), (0x10ecd9, 3), (0x10ecdc, 3), (0x10ecdf, 3), (0x10ece2, 3), (0x10ece5, 3), (0x10ece8, 3), (0x10eceb, 5), (0x10ecf0, 3), (0x10ecf3, 8), (0x10ecfb, 3), (0x10ecfe, 3), (0x10ed01, 4), (0x10ed05, 3), (0x10ed08, 8), (0x10ed10, 4), (0x10ed14, 3), (0x10ed17, 4)]

theorem part23_layout [Bindings] : InstructionTrace.layout part23 = part23Layout := by
  rfl

theorem part23_ordered [Bindings] : InstructionTrace.ordered 0x10eba6 part23 = true := by
  rw [InstructionTrace.ordered_eq_layout, part23_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part23_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xeba6 373 = part23Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
