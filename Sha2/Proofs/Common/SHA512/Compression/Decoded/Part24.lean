import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part23

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part24 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed1b 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed1e 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ed21 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed25 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed28 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10ed2b 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed2e 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ed31 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed35 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed38 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ed3b 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed3f 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10ed42 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ed4a 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ed4d 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed51 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ed54 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed58 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ed5b 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed5e 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ed61 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ed65 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed68 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ed6b 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed6f 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed72 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ed75 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed79 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ed7c 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf131d) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ed83 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (add_r64_m64_effect_step 0x10ed86 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed8e 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ed91 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ed94 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ed99 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ed9c 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ed9f 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10eda2 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10eda6 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10eda9 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10edac 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10edb0 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10edb3 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10edb6 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10edba 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10edbd 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10edc0 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10edc3 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10edc6 0x4c 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10edc9 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10edcc 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10edcf 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10edd2 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10edd7 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10edda 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10eddd 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10ede5 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ede8 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 264)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10edf0 0x48 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10edf4 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10edf7 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 272)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10edff 0x49 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee03 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee06 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ee09 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee0d 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ee10 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee14 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee17 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10ee1a 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee1d 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ee20 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee24 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee27 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ee2a 0x48 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee2e 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10ee31 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ee39 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ee3c 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee41 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ee44 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee48 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ee4b 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ee50 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ee53 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee56 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ee59 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee5d 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ee60 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee64 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ee67 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ee6a 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee6e 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ee71 0x48 (by simp [RexWPrefix]) 1 (.rip 0xf1230) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ee78 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ee7b 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ee7e 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee83 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ee86 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ee89 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part24Bytes : List UInt8 :=
  [0x4c,0x31,0xff,0x48,0x89,0xf0,0x48,0xc1,0xc0,0x3,0x48,0x31,0xc8,0x4c,0x89,0xc1,0x48,0xd1,0xc9,0x4c,0x89,0xc2,0x48,0xc1,0xc2,0x38,0x48,0x31,0xca,0x4c,0x89,0xc1,0x48,0xc1,0xe9,0x7,0x48,0x31,0xd1,0x48,0x1,0xb4,0x24,0x98,0x0,0x0,0x0,0x48,0x1,0xf1,0x48,0x89,0xc,0x24,0x48,0x89,0xf1,0x48,0xc1,0xe9,0x6,0x48,0x31,0xc1,0x49,0x1,0xfe,0x4c,0x89,0xc8,0x48,0xc1,0xc0,0x32,0x49,0x1,0xce,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x4c,0x89,0xc8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x1d,0x13,0xf,0x0,0x4c,0x1,0xf1,0x48,0x3,0x8c,0x24,0x80,0x0,0x0,0x0,0x4d,0x31,0xda,0x4d,0x21,0xca,0x4c,0x89,0x4c,0x24,0x50,0x4d,0x31,0xda,0x4c,0x1,0xd1,0x48,0x89,0xda,0x48,0xc1,0xc2,0x24,0x48,0x1,0xc1,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x1e,0x48,0x31,0xd0,0x48,0x89,0xda,0x48,0xc1,0xc2,0x19,0x48,0x31,0xc2,0x4c,0x89,0xe0,0x4c,0x21,0xe8,0x4c,0x89,0xe7,0x4c,0x31,0xef,0x48,0x21,0xdf,0x48,0x31,0xc7,0x48,0x1,0xd7,0x4c,0x8b,0x7c,0x24,0x78,0x49,0x1,0xcf,0x48,0x1,0xcf,0x48,0x8b,0x8c,0x24,0x0,0x1,0x0,0x0,0x48,0xd1,0xc9,0x48,0x8b,0x84,0x24,0x8,0x1,0x0,0x0,0x48,0xc1,0xc0,0x38,0x48,0x31,0xc8,0x4c,0x8b,0x94,0x24,0x10,0x1,0x0,0x0,0x49,0xc1,0xea,0x7,0x49,0x31,0xc2,0x4c,0x89,0xc1,0x48,0xc1,0xc1,0x2d,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x3,0x48,0x31,0xc8,0x4c,0x89,0xf1,0x48,0xd1,0xc9,0x4c,0x89,0xf2,0x48,0xc1,0xc2,0x38,0x48,0x31,0xca,0x4c,0x89,0xf1,0x48,0xc1,0xe9,0x7,0x48,0x31,0xd1,0x4c,0x1,0x84,0x24,0xa0,0x0,0x0,0x0,0x4c,0x1,0xc1,0x48,0x89,0x4c,0x24,0x48,0x4c,0x89,0xc1,0x48,0xc1,0xe9,0x6,0x48,0x31,0xc1,0x48,0x8b,0x74,0x24,0x18,0x4c,0x1,0xd6,0x48,0x1,0xce,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x32,0x4c,0x89,0xf9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x30,0x12,0xf,0x0,0x48,0x1,0xf1,0x4c,0x1,0xd9,0x4c,0x8b,0x44,0x24,0x38,0x4d,0x31,0xc1,0x4d,0x21,0xf9,0x4d,0x31,0xc1]

set_option maxRecDepth 4096 in
theorem part24_bytes [Bindings] : part24.flatMap CheckedInstruction.bytes = part24Bytes := by
  rfl

def part24Layout : List (BitVec 64 × Nat) :=
  [(0x10ed1b, 3), (0x10ed1e, 3), (0x10ed21, 4), (0x10ed25, 3), (0x10ed28, 3), (0x10ed2b, 3), (0x10ed2e, 3), (0x10ed31, 4), (0x10ed35, 3), (0x10ed38, 3), (0x10ed3b, 4), (0x10ed3f, 3), (0x10ed42, 8), (0x10ed4a, 3), (0x10ed4d, 4), (0x10ed51, 3), (0x10ed54, 4), (0x10ed58, 3), (0x10ed5b, 3), (0x10ed5e, 3), (0x10ed61, 4), (0x10ed65, 3), (0x10ed68, 3), (0x10ed6b, 4), (0x10ed6f, 3), (0x10ed72, 3), (0x10ed75, 4), (0x10ed79, 3), (0x10ed7c, 7), (0x10ed83, 3), (0x10ed86, 8), (0x10ed8e, 3), (0x10ed91, 3), (0x10ed94, 5), (0x10ed99, 3), (0x10ed9c, 3), (0x10ed9f, 3), (0x10eda2, 4), (0x10eda6, 3), (0x10eda9, 3), (0x10edac, 4), (0x10edb0, 3), (0x10edb3, 3), (0x10edb6, 4), (0x10edba, 3), (0x10edbd, 3), (0x10edc0, 3), (0x10edc3, 3), (0x10edc6, 3), (0x10edc9, 3), (0x10edcc, 3), (0x10edcf, 3), (0x10edd2, 5), (0x10edd7, 3), (0x10edda, 3), (0x10eddd, 8), (0x10ede5, 3), (0x10ede8, 8), (0x10edf0, 4), (0x10edf4, 3), (0x10edf7, 8), (0x10edff, 4), (0x10ee03, 3), (0x10ee06, 3), (0x10ee09, 4), (0x10ee0d, 3), (0x10ee10, 4), (0x10ee14, 3), (0x10ee17, 3), (0x10ee1a, 3), (0x10ee1d, 3), (0x10ee20, 4), (0x10ee24, 3), (0x10ee27, 3), (0x10ee2a, 4), (0x10ee2e, 3), (0x10ee31, 8), (0x10ee39, 3), (0x10ee3c, 5), (0x10ee41, 3), (0x10ee44, 4), (0x10ee48, 3), (0x10ee4b, 5), (0x10ee50, 3), (0x10ee53, 3), (0x10ee56, 3), (0x10ee59, 4), (0x10ee5d, 3), (0x10ee60, 4), (0x10ee64, 3), (0x10ee67, 3), (0x10ee6a, 4), (0x10ee6e, 3), (0x10ee71, 7), (0x10ee78, 3), (0x10ee7b, 3), (0x10ee7e, 5), (0x10ee83, 3), (0x10ee86, 3), (0x10ee89, 3)]

theorem part24_layout [Bindings] : InstructionTrace.layout part24 = part24Layout := by
  rfl

theorem part24_ordered [Bindings] : InstructionTrace.ordered 0x10ed1b part24 = true := by
  rw [InstructionTrace.ordered_eq_layout, part24_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part24_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xed1b 369 = part24Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
