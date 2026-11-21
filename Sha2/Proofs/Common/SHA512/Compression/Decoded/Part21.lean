import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part20
import Sha2.Proofs.Common.Instructions.MemoryAlu.Add

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part21 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e862 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e865 0x48 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e869 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e86c 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e86f 0x4d 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e872 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e877 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e87b 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e87e 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e882 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e885 0x48 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e888 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e88d 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e890 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e893 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e898 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e89b 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e89e 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e8a1 0x49 0xc6 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e8a5 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e8ad 0x4d 0xd4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e8b0 0x49 0xc4 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e8b4 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e8b7 0x49 0xc2 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e8bb 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10e8c3 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e8c6 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e8c9 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e8ce 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e8d1 0x49 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e8d4 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e8d7 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e8da 0x48 0xc2 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e8de 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e8e1 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e8e4 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e8e9 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e8ec 0x48 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e8ef 0x49 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e8f2 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d32 184)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e8fa 0x49 0xc5 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10e8fe 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e901 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 296)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e909 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e90e 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e911 0x48 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e914 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e917 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e91a 0x48 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e91e 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e921 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e926 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e929 0x48 0xcf (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10e92c 0x48 0xeb 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e930 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e933 0x49 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e937 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e93a 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d32 288)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e942 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e947 0x48 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e94a 0x48 0xcd (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.store (xor_m64_r64_effect_step 0x10e94d 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e955 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e958 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e95c 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e95f 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d32 280)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e967 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e96c 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e96f 0x49 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e972 0x49 0xd5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e975 0x49 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e978 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e97b 0x49 0xc4 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e97f 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e982 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 152)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e98a 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e98f 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e992 0x48 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e995 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10e998 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d32 160)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e9a0 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e9a3 0x48 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e9a7 0x48 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e9aa 0x48 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e9ad 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e9b0 0x48 0xcf (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e9b3 0x4d 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e9b6 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e9b9 0x48 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e9bd 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10e9c0 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e9c8 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10e9cb 0x48 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e9ce 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e9d1 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10e9d4 0x48 0xc7 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10e9d8 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e9db 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10e9de 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10e9e1 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
  ]

def part21Bytes : List UInt8 :=
  [0x4c,0x89,0xc1,0x48,0xc1,0xc1,0x1e,0x48,0x31,0xc1,0x4c,0x89,0xc0,0x4d,0x89,0xc5,0x4c,0x89,0x44,0x24,0x78,0x48,0xc1,0xc0,0x19,0x48,0x31,0xc8,0x48,0x8b,0x3c,0x24,0x48,0x89,0xf9,0x48,0xd1,0xc9,0x4c,0x89,0x4c,0x24,0x50,0x4c,0x89,0xca,0x4d,0x89,0xf0,0x4c,0x89,0x74,0x24,0x38,0x4c,0x21,0xf2,0x49,0x89,0xfe,0x48,0x89,0xfb,0x49,0xc1,0xc6,0x38,0x4c,0x89,0x94,0x24,0x90,0x0,0x0,0x0,0x4d,0x89,0xd4,0x49,0xc1,0xc4,0x2d,0x4d,0x31,0xc1,0x49,0xc1,0xc2,0x3,0x4c,0x89,0x94,0x24,0xd0,0x0,0x0,0x0,0x4d,0x21,0xe9,0x4d,0x89,0xc8,0x48,0x8b,0x7c,0x24,0x68,0x49,0x89,0xf9,0x49,0xd1,0xc9,0x49,0x31,0xd0,0x48,0x89,0xfa,0x48,0xc1,0xc2,0x38,0x49,0x89,0xd2,0x49,0x1,0xc0,0x4c,0x8b,0x6c,0x24,0x8,0x4c,0x89,0xea,0x48,0xd1,0xca,0x49,0x1,0xeb,0x4c,0x89,0x9c,0x24,0xb8,0x0,0x0,0x0,0x49,0xc1,0xc5,0x38,0x49,0x1,0xe8,0x4c,0x89,0x84,0x24,0x28,0x1,0x0,0x0,0x48,0x8b,0x7c,0x24,0x10,0x48,0x89,0xf8,0x48,0xd1,0xc8,0x49,0x31,0xce,0x48,0x89,0xf9,0x48,0xc1,0xc1,0x38,0x49,0x89,0xc8,0x48,0x8b,0x4c,0x24,0x40,0x48,0x89,0xcf,0x48,0xd1,0xcf,0x48,0xc1,0xeb,0x7,0x49,0x89,0xcb,0x49,0xc1,0xc3,0x38,0x4c,0x31,0xf3,0x48,0x89,0x9c,0x24,0x20,0x1,0x0,0x0,0x48,0x8b,0x4c,0x24,0x28,0x48,0x89,0xcd,0x48,0xd1,0xcd,0x4c,0x31,0xa4,0x24,0xd0,0x0,0x0,0x0,0x48,0x89,0xcb,0x48,0xc1,0xc3,0x38,0x4d,0x31,0xca,0x4c,0x89,0x94,0x24,0x18,0x1,0x0,0x0,0x48,0x8b,0x4c,0x24,0x58,0x49,0x89,0xc9,0x49,0xd1,0xc9,0x49,0x31,0xd5,0x49,0x89,0xcc,0x49,0x89,0xce,0x49,0xc1,0xc4,0x38,0x49,0x31,0xc0,0x4c,0x89,0x84,0x24,0x98,0x0,0x0,0x0,0x4c,0x8b,0x54,0x24,0x60,0x4c,0x89,0xd2,0x48,0xd1,0xca,0x49,0x31,0xfb,0x4c,0x89,0x9c,0x24,0xa0,0x0,0x0,0x0,0x4c,0x89,0xd0,0x48,0xc1,0xc0,0x38,0x48,0x31,0xeb,0x48,0x89,0xdd,0x4c,0x89,0xff,0x48,0xd1,0xcf,0x4d,0x31,0xcc,0x4c,0x89,0xf9,0x48,0xc1,0xc1,0x38,0x48,0x31,0xd0,0x4c,0x8b,0x84,0x24,0x90,0x0,0x0,0x0,0x4c,0x89,0xc2,0x48,0xd1,0xca,0x48,0x31,0xf9,0x4c,0x89,0xc7,0x48,0xc1,0xc7,0x38,0x48,0x31,0xd7,0x4d,0x89,0xc1,0x4c,0x89,0xc2,0x49,0xc1,0xe9,0x7]

set_option maxRecDepth 4096 in
theorem part21_bytes [Bindings] : part21.flatMap CheckedInstruction.bytes = part21Bytes := by
  rfl

def part21Layout : List (BitVec 64 × Nat) :=
  [(0x10e862, 3), (0x10e865, 4), (0x10e869, 3), (0x10e86c, 3), (0x10e86f, 3), (0x10e872, 5), (0x10e877, 4), (0x10e87b, 3), (0x10e87e, 4), (0x10e882, 3), (0x10e885, 3), (0x10e888, 5), (0x10e88d, 3), (0x10e890, 3), (0x10e893, 5), (0x10e898, 3), (0x10e89b, 3), (0x10e89e, 3), (0x10e8a1, 4), (0x10e8a5, 8), (0x10e8ad, 3), (0x10e8b0, 4), (0x10e8b4, 3), (0x10e8b7, 4), (0x10e8bb, 8), (0x10e8c3, 3), (0x10e8c6, 3), (0x10e8c9, 5), (0x10e8ce, 3), (0x10e8d1, 3), (0x10e8d4, 3), (0x10e8d7, 3), (0x10e8da, 4), (0x10e8de, 3), (0x10e8e1, 3), (0x10e8e4, 5), (0x10e8e9, 3), (0x10e8ec, 3), (0x10e8ef, 3), (0x10e8f2, 8), (0x10e8fa, 4), (0x10e8fe, 3), (0x10e901, 8), (0x10e909, 5), (0x10e90e, 3), (0x10e911, 3), (0x10e914, 3), (0x10e917, 3), (0x10e91a, 4), (0x10e91e, 3), (0x10e921, 5), (0x10e926, 3), (0x10e929, 3), (0x10e92c, 4), (0x10e930, 3), (0x10e933, 4), (0x10e937, 3), (0x10e93a, 8), (0x10e942, 5), (0x10e947, 3), (0x10e94a, 3), (0x10e94d, 8), (0x10e955, 3), (0x10e958, 4), (0x10e95c, 3), (0x10e95f, 8), (0x10e967, 5), (0x10e96c, 3), (0x10e96f, 3), (0x10e972, 3), (0x10e975, 3), (0x10e978, 3), (0x10e97b, 4), (0x10e97f, 3), (0x10e982, 8), (0x10e98a, 5), (0x10e98f, 3), (0x10e992, 3), (0x10e995, 3), (0x10e998, 8), (0x10e9a0, 3), (0x10e9a3, 4), (0x10e9a7, 3), (0x10e9aa, 3), (0x10e9ad, 3), (0x10e9b0, 3), (0x10e9b3, 3), (0x10e9b6, 3), (0x10e9b9, 4), (0x10e9bd, 3), (0x10e9c0, 8), (0x10e9c8, 3), (0x10e9cb, 3), (0x10e9ce, 3), (0x10e9d1, 3), (0x10e9d4, 4), (0x10e9d8, 3), (0x10e9db, 3), (0x10e9de, 3), (0x10e9e1, 4)]

theorem part21_layout [Bindings] : InstructionTrace.layout part21 = part21Layout := by
  rfl

theorem part21_ordered [Bindings] : InstructionTrace.ordered 0x10e862 part21 = true := by
  rw [InstructionTrace.ordered_eq_layout, part21_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part21_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xe862 387 = part21Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
