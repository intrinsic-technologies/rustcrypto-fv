import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part32

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part33 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f938 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f93c 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f93f 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f942 0x48 0xcf (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f945 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f948 0x49 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f94c 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f94f 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f952 0x48 0xef 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f956 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f959 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f95e 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f961 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f966 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f969 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f96d 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f970 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f975 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f978 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f97b 0x48 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f97f 0x4c 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f982 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f986 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f989 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f98c 0x48 0xc6 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f990 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f993 0x48 (by simp [RexWPrefix]) 7 (.rip 0xf0786) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f99a 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f99d 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9a0 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f9a3 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f9a6 0x4d 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f9a9 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f9ac 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f9af 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9b2 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f9b5 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9b9 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f9bc 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f9c0 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9c3 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f9c6 0x49 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f9ca 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9cd 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f9d0 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9d3 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9d6 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f9d9 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f9dc 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f9df 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f9e2 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f9e5 0x48 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f9e8 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9eb 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f9ee 0x49 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9f2 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f9f5 0x48 0xc7 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f9f9 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f9fc 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f9ff 0x49 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa02 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fa05 0x49 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa09 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa0c 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fa0f 0x48 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa13 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10fa16 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fa1b 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10fa1e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa23 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fa26 0x49 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa2a 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fa2d 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fa32 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa35 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fa38 0x48 0xc7 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa3c 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fa3f 0x49 0xc0 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa43 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa46 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fa49 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa4d 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fa50 0x4c (by simp [RexWPrefix]) 8 (.rip 0xf06d1) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fa57 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fa5a 0x4d 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa5d 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa60 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fa63 0x49 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa66 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fa69 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fa6c 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa6f 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fa72 0x48 0xc7 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa76 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fa79 0x49 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa7d 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa80 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fa83 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fa87 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fa8a 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part33Bytes : List UInt8 :=
  [0x48,0xc1,0xc6,0x3,0x4c,0x31,0xc6,0x4c,0x89,0xcf,0x48,0xd1,0xcf,0x4d,0x89,0xc8,0x49,0xc1,0xc0,0x38,0x49,0x31,0xf8,0x4c,0x89,0xcf,0x48,0xc1,0xef,0x7,0x4c,0x31,0xc7,0x4c,0x1,0x54,0x24,0x70,0x4c,0x1,0xd7,0x48,0x89,0x7c,0x24,0x8,0x4c,0x89,0xd7,0x48,0xc1,0xef,0x6,0x48,0x31,0xf7,0x4c,0x8b,0x74,0x24,0x28,0x49,0x1,0xfe,0x4c,0x89,0xee,0x48,0xc1,0xc6,0x32,0x4c,0x89,0xef,0x48,0xc1,0xc7,0x2e,0x48,0x31,0xf7,0x4c,0x89,0xee,0x48,0xc1,0xc6,0x17,0x48,0x31,0xfe,0x48,0x8b,0x3d,0x86,0x7,0xf,0x0,0x4c,0x1,0xf7,0x48,0x1,0xdf,0x4d,0x89,0xe0,0x4d,0x31,0xf8,0x4d,0x21,0xe8,0x4d,0x31,0xf8,0x4c,0x1,0xc7,0x48,0x1,0xf7,0x48,0x89,0xd6,0x48,0xc1,0xc6,0x24,0x49,0x89,0xd0,0x49,0xc1,0xc0,0x1e,0x49,0x31,0xf0,0x49,0x89,0xd2,0x49,0xc1,0xc2,0x19,0x4d,0x31,0xc2,0x49,0x89,0xc0,0x49,0x21,0xc8,0x48,0x89,0xc6,0x48,0x89,0xc3,0x48,0x31,0xce,0x48,0x21,0xd6,0x4c,0x31,0xc6,0x4c,0x1,0xd6,0x48,0x1,0xfd,0x48,0x1,0xfe,0x4d,0x89,0xc8,0x49,0xc1,0xc0,0x2d,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x3,0x4c,0x31,0xc7,0x4d,0x89,0xf0,0x49,0xd1,0xc8,0x4d,0x89,0xf3,0x49,0xc1,0xc3,0x38,0x4d,0x31,0xc3,0x4c,0x89,0xf0,0x48,0xc1,0xe8,0x7,0x4c,0x31,0xd8,0x4c,0x1,0x4c,0x24,0x18,0x4c,0x1,0xc8,0x48,0x89,0x44,0x24,0x28,0x4d,0x89,0xc8,0x49,0xc1,0xe8,0x6,0x49,0x31,0xf8,0x4c,0x8b,0x54,0x24,0x40,0x4d,0x1,0xc2,0x48,0x89,0xef,0x48,0xc1,0xc7,0x32,0x49,0x89,0xe8,0x49,0xc1,0xc0,0x2e,0x49,0x31,0xf8,0x48,0x89,0xef,0x48,0xc1,0xc7,0x17,0x4c,0x31,0xc7,0x4c,0x8b,0x5,0xd1,0x6,0xf,0x0,0x4d,0x1,0xd0,0x4d,0x1,0xf8,0x4d,0x89,0xeb,0x4d,0x31,0xe3,0x49,0x21,0xeb,0x4d,0x31,0xe3,0x4d,0x1,0xd8,0x49,0x1,0xf8,0x48,0x89,0xf7,0x48,0xc1,0xc7,0x24,0x49,0x89,0xf3,0x49,0xc1,0xc3,0x1e,0x49,0x31,0xfb,0x48,0x89,0xf7,0x48,0xc1,0xc7,0x19,0x4c,0x31,0xdf,0x49,0x89,0xd3]

set_option maxRecDepth 4096 in
theorem part33_bytes [Bindings] : part33.flatMap CheckedInstruction.bytes = part33Bytes := by
  rfl

def part33Layout : List (BitVec 64 × Nat) :=
  [(0x10f938, 4), (0x10f93c, 3), (0x10f93f, 3), (0x10f942, 3), (0x10f945, 3), (0x10f948, 4), (0x10f94c, 3), (0x10f94f, 3), (0x10f952, 4), (0x10f956, 3), (0x10f959, 5), (0x10f95e, 3), (0x10f961, 5), (0x10f966, 3), (0x10f969, 4), (0x10f96d, 3), (0x10f970, 5), (0x10f975, 3), (0x10f978, 3), (0x10f97b, 4), (0x10f97f, 3), (0x10f982, 4), (0x10f986, 3), (0x10f989, 3), (0x10f98c, 4), (0x10f990, 3), (0x10f993, 7), (0x10f99a, 3), (0x10f99d, 3), (0x10f9a0, 3), (0x10f9a3, 3), (0x10f9a6, 3), (0x10f9a9, 3), (0x10f9ac, 3), (0x10f9af, 3), (0x10f9b2, 3), (0x10f9b5, 4), (0x10f9b9, 3), (0x10f9bc, 4), (0x10f9c0, 3), (0x10f9c3, 3), (0x10f9c6, 4), (0x10f9ca, 3), (0x10f9cd, 3), (0x10f9d0, 3), (0x10f9d3, 3), (0x10f9d6, 3), (0x10f9d9, 3), (0x10f9dc, 3), (0x10f9df, 3), (0x10f9e2, 3), (0x10f9e5, 3), (0x10f9e8, 3), (0x10f9eb, 3), (0x10f9ee, 4), (0x10f9f2, 3), (0x10f9f5, 4), (0x10f9f9, 3), (0x10f9fc, 3), (0x10f9ff, 3), (0x10fa02, 3), (0x10fa05, 4), (0x10fa09, 3), (0x10fa0c, 3), (0x10fa0f, 4), (0x10fa13, 3), (0x10fa16, 5), (0x10fa1b, 3), (0x10fa1e, 5), (0x10fa23, 3), (0x10fa26, 4), (0x10fa2a, 3), (0x10fa2d, 5), (0x10fa32, 3), (0x10fa35, 3), (0x10fa38, 4), (0x10fa3c, 3), (0x10fa3f, 4), (0x10fa43, 3), (0x10fa46, 3), (0x10fa49, 4), (0x10fa4d, 3), (0x10fa50, 7), (0x10fa57, 3), (0x10fa5a, 3), (0x10fa5d, 3), (0x10fa60, 3), (0x10fa63, 3), (0x10fa66, 3), (0x10fa69, 3), (0x10fa6c, 3), (0x10fa6f, 3), (0x10fa72, 4), (0x10fa76, 3), (0x10fa79, 4), (0x10fa7d, 3), (0x10fa80, 3), (0x10fa83, 4), (0x10fa87, 3), (0x10fa8a, 3)]

theorem part33_layout [Bindings] : InstructionTrace.layout part33 = part33Layout := by
  rfl

theorem part33_ordered [Bindings] : InstructionTrace.ordered 0x10f938 part33 = true := by
  rw [InstructionTrace.ordered_eq_layout, part33_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part33_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xf938 341 = part33Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
