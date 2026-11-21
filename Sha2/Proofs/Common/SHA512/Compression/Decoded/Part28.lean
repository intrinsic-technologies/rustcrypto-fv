import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part27

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part28 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f294 0x4c 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f297 0x48 0xc6 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f29b 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f29e 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f2a1 0x48 0xc2 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f2a5 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f2a8 0x49 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f2ab 0x49 0xce (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f2ae 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f2b1 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f2b4 0x48 0xc6 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f2b8 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f2bb 0x49 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f2be 0x49 0xee 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f2c2 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f2c5 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f2ca 0x4d 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f2cd 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f2d2 0x49 0xed 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f2d6 0x49 0xd5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f2d9 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f2dc 0x48 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f2e0 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 168)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f2e8 0x4d 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f2eb 0x4c 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f2ee 0x48 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f2f2 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f2f5 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f2f8 0x48 0xc2 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f2fc 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f2ff 0x48 (by simp [RexWPrefix]) 6 (.rip 0xf0dd2) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f306 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f309 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f30c 0x4c 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f30f 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f312 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f315 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f318 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f31b 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f31e 0x48 0xc3 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f322 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f325 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f328 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f32c 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f32f 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f332 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f336 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f339 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f33c 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f33f 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f342 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f345 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f348 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f34b 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f34e 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f351 0x48 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f354 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f358 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f35b 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f35e 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f362 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f365 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f368 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f36b 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f36e 0x49 0xc6 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f372 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f375 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f378 0x48 0xeb 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f37c 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f37f 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f384 0x48 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f387 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f38c 0x48 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f38f 0x48 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f393 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f396 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f39b 0x49 0xdc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f39e 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f3a1 0x48 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f3a5 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f3a8 0x48 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f3ac 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f3af 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f3b2 0x48 0xc6 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f3b6 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f3b9 0x4c (by simp [RexWPrefix]) 14 (.rip 0xf0d20) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f3c0 0x4d 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f3c3 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f3c6 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f3c9 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f3cc 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f3cf 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f3d2 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f3d5 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f3d8 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f3db 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f3df 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f3e2 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f3e6 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f3e9 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part28Bytes : List UInt8 :=
  [0x4c,0x89,0xee,0x48,0xc1,0xc6,0x2d,0x4d,0x1,0xf9,0x4c,0x89,0xea,0x48,0xc1,0xc2,0x3,0x4c,0x1,0xf8,0x49,0x89,0xee,0x49,0xd1,0xce,0x48,0x31,0xf2,0x48,0x89,0xee,0x48,0xc1,0xc6,0x38,0x4c,0x31,0xf6,0x49,0x89,0xee,0x49,0xc1,0xee,0x7,0x49,0x31,0xf6,0x4c,0x1,0x6c,0x24,0x10,0x4d,0x1,0xee,0x4c,0x89,0x74,0x24,0x70,0x49,0xc1,0xed,0x6,0x49,0x31,0xd5,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x32,0x4c,0x8b,0xbc,0x24,0xa8,0x0,0x0,0x0,0x4d,0x1,0xef,0x4c,0x89,0xce,0x48,0xc1,0xc6,0x2e,0x48,0x31,0xd6,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x17,0x48,0x31,0xf2,0x48,0x8b,0x35,0xd2,0xd,0xf,0x0,0x4c,0x1,0xfe,0x48,0x1,0xde,0x4c,0x89,0xc3,0x48,0x31,0xfb,0x4c,0x21,0xcb,0x48,0x31,0xfb,0x48,0x1,0xde,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x24,0x48,0x1,0xd6,0x48,0x89,0xc2,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xda,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x19,0x48,0x31,0xd3,0x49,0x89,0xce,0x4d,0x21,0xde,0x48,0x89,0xca,0x4c,0x31,0xda,0x48,0x21,0xc2,0x4c,0x31,0xf2,0x48,0x1,0xda,0x49,0x1,0xf2,0x48,0x89,0xeb,0x48,0xc1,0xc3,0x2d,0x48,0x1,0xf2,0x48,0x89,0xee,0x48,0xc1,0xc6,0x3,0x48,0x31,0xde,0x4c,0x89,0xfb,0x48,0xd1,0xcb,0x4d,0x89,0xfe,0x49,0xc1,0xc6,0x38,0x49,0x31,0xde,0x4c,0x89,0xfb,0x48,0xc1,0xeb,0x7,0x4c,0x31,0xf3,0x48,0x1,0x6c,0x24,0x8,0x48,0x1,0xeb,0x48,0x89,0x5c,0x24,0x18,0x48,0x89,0xeb,0x48,0xc1,0xeb,0x6,0x48,0x31,0xf3,0x4c,0x8b,0x64,0x24,0x58,0x49,0x1,0xdc,0x4c,0x89,0xd6,0x48,0xc1,0xc6,0x32,0x4c,0x89,0xd3,0x48,0xc1,0xc3,0x2e,0x48,0x31,0xf3,0x4c,0x89,0xd6,0x48,0xc1,0xc6,0x17,0x48,0x31,0xde,0x4c,0x8b,0x35,0x20,0xd,0xf,0x0,0x4d,0x1,0xe6,0x49,0x1,0xfe,0x4c,0x89,0xcf,0x4c,0x31,0xc7,0x4c,0x21,0xd7,0x4c,0x31,0xc7,0x49,0x1,0xfe,0x49,0x1,0xf6,0x48,0x89,0xd6,0x48,0xc1,0xc6,0x24,0x48,0x89,0xd7,0x48,0xc1,0xc7,0x1e,0x48,0x31,0xf7,0x48,0x89,0xd6]

set_option maxRecDepth 4096 in
theorem part28_bytes [Bindings] : part28.flatMap CheckedInstruction.bytes = part28Bytes := by
  rfl

def part28Layout : List (BitVec 64 × Nat) :=
  [(0x10f294, 3), (0x10f297, 4), (0x10f29b, 3), (0x10f29e, 3), (0x10f2a1, 4), (0x10f2a5, 3), (0x10f2a8, 3), (0x10f2ab, 3), (0x10f2ae, 3), (0x10f2b1, 3), (0x10f2b4, 4), (0x10f2b8, 3), (0x10f2bb, 3), (0x10f2be, 4), (0x10f2c2, 3), (0x10f2c5, 5), (0x10f2ca, 3), (0x10f2cd, 5), (0x10f2d2, 4), (0x10f2d6, 3), (0x10f2d9, 3), (0x10f2dc, 4), (0x10f2e0, 8), (0x10f2e8, 3), (0x10f2eb, 3), (0x10f2ee, 4), (0x10f2f2, 3), (0x10f2f5, 3), (0x10f2f8, 4), (0x10f2fc, 3), (0x10f2ff, 7), (0x10f306, 3), (0x10f309, 3), (0x10f30c, 3), (0x10f30f, 3), (0x10f312, 3), (0x10f315, 3), (0x10f318, 3), (0x10f31b, 3), (0x10f31e, 4), (0x10f322, 3), (0x10f325, 3), (0x10f328, 4), (0x10f32c, 3), (0x10f32f, 3), (0x10f332, 4), (0x10f336, 3), (0x10f339, 3), (0x10f33c, 3), (0x10f33f, 3), (0x10f342, 3), (0x10f345, 3), (0x10f348, 3), (0x10f34b, 3), (0x10f34e, 3), (0x10f351, 3), (0x10f354, 4), (0x10f358, 3), (0x10f35b, 3), (0x10f35e, 4), (0x10f362, 3), (0x10f365, 3), (0x10f368, 3), (0x10f36b, 3), (0x10f36e, 4), (0x10f372, 3), (0x10f375, 3), (0x10f378, 4), (0x10f37c, 3), (0x10f37f, 5), (0x10f384, 3), (0x10f387, 5), (0x10f38c, 3), (0x10f38f, 4), (0x10f393, 3), (0x10f396, 5), (0x10f39b, 3), (0x10f39e, 3), (0x10f3a1, 4), (0x10f3a5, 3), (0x10f3a8, 4), (0x10f3ac, 3), (0x10f3af, 3), (0x10f3b2, 4), (0x10f3b6, 3), (0x10f3b9, 7), (0x10f3c0, 3), (0x10f3c3, 3), (0x10f3c6, 3), (0x10f3c9, 3), (0x10f3cc, 3), (0x10f3cf, 3), (0x10f3d2, 3), (0x10f3d5, 3), (0x10f3d8, 3), (0x10f3db, 4), (0x10f3df, 3), (0x10f3e2, 4), (0x10f3e6, 3), (0x10f3e9, 3)]

theorem part28_layout [Bindings] : InstructionTrace.layout part28 = part28Layout := by
  rfl

theorem part28_ordered [Bindings] : InstructionTrace.ordered 0x10f294 part28 = true := by
  rw [InstructionTrace.ordered_eq_layout, part28_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part28_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xf294 344 = part28Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
