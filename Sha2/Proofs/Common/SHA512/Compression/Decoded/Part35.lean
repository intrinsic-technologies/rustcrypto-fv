import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part34

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part35 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fbe8 0x48 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fbeb 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fbee 0x4d 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fbf1 0x48 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fbf4 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fbf7 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fbfa 0x48 0xc3 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fbfe 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc01 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fc04 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc08 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc0b 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fc0e 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc12 0x4c 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc15 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fc18 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc1b 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc1e 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fc21 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc24 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fc27 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fc2a 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc2d 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc30 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fc33 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fc37 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc3a 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fc3d 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc41 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc44 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc47 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10fc4a 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc4d 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fc50 0x49 0xc6 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc54 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fc57 0x49 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc5b 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10fc5e 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fc63 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10fc66 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc6a 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fc6d 0x48 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc71 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fc74 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fc79 0x49 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc7c 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fc7f 0x49 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc83 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fc86 0x48 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc8a 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fc8d 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fc90 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fc94 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fc97 0x48 (by simp [RexWPrefix]) 3 (.rip 0xf04a2) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fc9e 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fca1 0x48 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fca4 0x4d 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fca7 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fcaa 0x49 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fcad 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fcb0 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fcb3 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fcb6 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fcb9 0x49 0xc3 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fcbd 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fcc0 0x49 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fcc4 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fcc7 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fcca 0x49 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fcce 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fcd1 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fcd4 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fcd7 0x48 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fcda 0x4c 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fcdd 0x4c 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fce0 0x4c 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fce3 0x4c 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fce6 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fce9 0x48 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fcec 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fcef 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fcf2 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fcf6 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fcf9 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fcfd 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd00 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd03 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10fd06 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd09 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fd0c 0x49 0xc6 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd10 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fd13 0x49 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd17 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10fd1a 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fd1f 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10fd22 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fd27 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fd2a 0x48 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fd2e 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fd31 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
  ]

def part35Bytes : List UInt8 :=
  [0x48,0x31,0xeb,0x4c,0x21,0xcb,0x4d,0x89,0xcd,0x48,0x31,0xeb,0x49,0x1,0xdb,0x48,0x89,0xfb,0x48,0xc1,0xc3,0x24,0x4d,0x1,0xc3,0x49,0x89,0xf8,0x49,0xc1,0xc0,0x1e,0x49,0x31,0xd8,0x48,0x89,0xfb,0x48,0xc1,0xc3,0x19,0x4c,0x31,0xc3,0x4d,0x89,0xfe,0x49,0x21,0xf6,0x4d,0x89,0xf8,0x49,0x31,0xf0,0x49,0x21,0xf8,0x4d,0x31,0xf0,0x49,0x1,0xd8,0x4c,0x1,0xda,0x49,0x89,0xc1,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x2d,0x4d,0x1,0xd8,0x49,0x89,0xc3,0x49,0xc1,0xc3,0x3,0x49,0x31,0xdb,0x4c,0x89,0xd0,0x4c,0x89,0xd3,0x48,0xd1,0xcb,0x4d,0x89,0xd6,0x49,0xc1,0xc6,0x38,0x49,0x31,0xde,0x49,0xc1,0xea,0x7,0x4d,0x31,0xf2,0x4c,0x1,0x4c,0x24,0x60,0x4d,0x1,0xca,0x4c,0x89,0x14,0x24,0x4c,0x89,0xcb,0x48,0xc1,0xeb,0x6,0x4c,0x31,0xdb,0x4c,0x8b,0x54,0x24,0x68,0x49,0x1,0xda,0x49,0x89,0xd3,0x49,0xc1,0xc3,0x32,0x48,0x89,0xd3,0x48,0xc1,0xc3,0x2e,0x4c,0x31,0xdb,0x49,0x89,0xd3,0x49,0xc1,0xc3,0x17,0x49,0x31,0xdb,0x48,0x8b,0x1d,0xa2,0x4,0xf,0x0,0x4c,0x1,0xd3,0x48,0x1,0xeb,0x4d,0x89,0xee,0x49,0x31,0xce,0x49,0x21,0xd6,0x49,0x31,0xce,0x4c,0x1,0xf3,0x4c,0x1,0xdb,0x4d,0x89,0xc3,0x49,0xc1,0xc3,0x24,0x4d,0x89,0xc6,0x49,0xc1,0xc6,0x1e,0x4d,0x31,0xde,0x4d,0x89,0xc3,0x49,0xc1,0xc3,0x19,0x4d,0x31,0xf3,0x49,0x89,0xfe,0x4d,0x21,0xfe,0x48,0x89,0xfd,0x4c,0x31,0xfd,0x4c,0x21,0xc5,0x4c,0x31,0xf5,0x4c,0x1,0xdd,0x48,0x1,0xde,0x48,0x1,0xdd,0x49,0x89,0xc1,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x2d,0x49,0x89,0xc3,0x49,0xc1,0xc3,0x3,0x49,0x31,0xdb,0x4c,0x89,0xd0,0x4c,0x89,0xd3,0x48,0xd1,0xcb,0x4d,0x89,0xd6,0x49,0xc1,0xc6,0x38,0x49,0x31,0xde,0x49,0xc1,0xea,0x7,0x4d,0x31,0xf2,0x4c,0x1,0x4c,0x24,0x30,0x4d,0x1,0xca,0x4c,0x89,0x54,0x24,0x38,0x4c,0x89,0xcb,0x48,0xc1,0xeb,0x6,0x4c,0x31,0xdb,0x4c,0x8b,0x64,0x24,0x70]

set_option maxRecDepth 4096 in
theorem part35_bytes [Bindings] : part35.flatMap CheckedInstruction.bytes = part35Bytes := by
  rfl

def part35Layout : List (BitVec 64 × Nat) :=
  [(0x10fbe8, 3), (0x10fbeb, 3), (0x10fbee, 3), (0x10fbf1, 3), (0x10fbf4, 3), (0x10fbf7, 3), (0x10fbfa, 4), (0x10fbfe, 3), (0x10fc01, 3), (0x10fc04, 4), (0x10fc08, 3), (0x10fc0b, 3), (0x10fc0e, 4), (0x10fc12, 3), (0x10fc15, 3), (0x10fc18, 3), (0x10fc1b, 3), (0x10fc1e, 3), (0x10fc21, 3), (0x10fc24, 3), (0x10fc27, 3), (0x10fc2a, 3), (0x10fc2d, 3), (0x10fc30, 3), (0x10fc33, 4), (0x10fc37, 3), (0x10fc3a, 3), (0x10fc3d, 4), (0x10fc41, 3), (0x10fc44, 3), (0x10fc47, 3), (0x10fc4a, 3), (0x10fc4d, 3), (0x10fc50, 4), (0x10fc54, 3), (0x10fc57, 4), (0x10fc5b, 3), (0x10fc5e, 5), (0x10fc63, 3), (0x10fc66, 4), (0x10fc6a, 3), (0x10fc6d, 4), (0x10fc71, 3), (0x10fc74, 5), (0x10fc79, 3), (0x10fc7c, 3), (0x10fc7f, 4), (0x10fc83, 3), (0x10fc86, 4), (0x10fc8a, 3), (0x10fc8d, 3), (0x10fc90, 4), (0x10fc94, 3), (0x10fc97, 7), (0x10fc9e, 3), (0x10fca1, 3), (0x10fca4, 3), (0x10fca7, 3), (0x10fcaa, 3), (0x10fcad, 3), (0x10fcb0, 3), (0x10fcb3, 3), (0x10fcb6, 3), (0x10fcb9, 4), (0x10fcbd, 3), (0x10fcc0, 4), (0x10fcc4, 3), (0x10fcc7, 3), (0x10fcca, 4), (0x10fcce, 3), (0x10fcd1, 3), (0x10fcd4, 3), (0x10fcd7, 3), (0x10fcda, 3), (0x10fcdd, 3), (0x10fce0, 3), (0x10fce3, 3), (0x10fce6, 3), (0x10fce9, 3), (0x10fcec, 3), (0x10fcef, 3), (0x10fcf2, 4), (0x10fcf6, 3), (0x10fcf9, 4), (0x10fcfd, 3), (0x10fd00, 3), (0x10fd03, 3), (0x10fd06, 3), (0x10fd09, 3), (0x10fd0c, 4), (0x10fd10, 3), (0x10fd13, 4), (0x10fd17, 3), (0x10fd1a, 5), (0x10fd1f, 3), (0x10fd22, 5), (0x10fd27, 3), (0x10fd2a, 4), (0x10fd2e, 3), (0x10fd31, 5)]

theorem part35_layout [Bindings] : InstructionTrace.layout part35 = part35Layout := by
  rfl

theorem part35_ordered [Bindings] : InstructionTrace.ordered 0x10fbe8 part35 = true := by
  rw [InstructionTrace.ordered_eq_layout, part35_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part35_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xfbe8 334 = part35Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
