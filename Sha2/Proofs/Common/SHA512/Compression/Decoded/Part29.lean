import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part28

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part29 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f3ec 0x48 0xc6 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f3f0 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f3f3 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f3f6 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f3f9 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f3fc 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f3ff 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f402 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f405 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f408 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f40b 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f40e 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f411 0x48 0xc7 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f415 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f418 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f41c 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f41f 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f422 0x48 0xcf (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f425 0x4d 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f428 0x49 0xc6 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f42c 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f42f 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f432 0x48 0xef 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f436 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f439 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f43d 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f440 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f445 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f448 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f44c 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f44f 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f454 0x48 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f457 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f45a 0x48 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f45e 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f461 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f465 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f468 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f46b 0x48 0xc6 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f46f 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f472 0x48 (by simp [RexWPrefix]) 7 (.rip 0xf0c6f) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f479 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f47c 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f47f 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f482 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f485 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f488 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f48b 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f48e 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f491 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f494 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f498 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f49b 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f49f 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4a2 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f4a5 0x48 0xc6 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f4a9 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4ac 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f4af 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4b2 0x49 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f4b5 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f4b8 0x49 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f4bb 0x4d 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4be 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f4c1 0x49 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f4c5 0x49 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4c8 0x4c 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f4cb 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f4cf 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4d2 0x49 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f4d5 0x49 0xce (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f4d8 0x49 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4db 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f4de 0x48 0xc7 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f4e2 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f4e5 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4e8 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f4eb 0x49 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f4ef 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f4f2 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f4f7 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f4fa 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f4ff 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f502 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f506 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f509 0x49 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f50d 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f510 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f513 0x48 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f517 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f51f 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f522 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f525 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f529 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f52c 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f52f 0x4c (by simp [RexWPrefix]) 8 (.rip 0xf0bba) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f536 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f539 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f53c 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f53f 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part29Bytes : List UInt8 :=
  [0x48,0xc1,0xc6,0x19,0x48,0x31,0xfe,0x48,0x89,0xc7,0x48,0x21,0xcf,0x48,0x89,0xc3,0x48,0x31,0xcb,0x48,0x21,0xd3,0x48,0x31,0xfb,0x48,0x1,0xf3,0x4d,0x1,0xf3,0x4c,0x1,0xf3,0x4c,0x89,0xff,0x48,0xc1,0xc7,0x2d,0x4c,0x89,0xfe,0x48,0xc1,0xc6,0x3,0x48,0x31,0xfe,0x4c,0x89,0xe7,0x48,0xd1,0xcf,0x4d,0x89,0xe6,0x49,0xc1,0xc6,0x38,0x49,0x31,0xfe,0x4c,0x89,0xe7,0x48,0xc1,0xef,0x7,0x4c,0x31,0xf7,0x4c,0x1,0x3c,0x24,0x4c,0x1,0xff,0x48,0x89,0x7c,0x24,0x50,0x4c,0x89,0xff,0x48,0xc1,0xef,0x6,0x48,0x31,0xf7,0x48,0x8b,0x6c,0x24,0x60,0x48,0x1,0xfd,0x4c,0x89,0xde,0x48,0xc1,0xc6,0x32,0x4c,0x89,0xdf,0x48,0xc1,0xc7,0x2e,0x48,0x31,0xf7,0x4c,0x89,0xde,0x48,0xc1,0xc6,0x17,0x48,0x31,0xfe,0x48,0x8b,0x3d,0x6f,0xc,0xf,0x0,0x48,0x1,0xef,0x4c,0x1,0xc7,0x4d,0x89,0xd0,0x4d,0x31,0xc8,0x4d,0x21,0xd8,0x4d,0x31,0xc8,0x4c,0x1,0xc7,0x48,0x1,0xf7,0x48,0x89,0xde,0x48,0xc1,0xc6,0x24,0x49,0x89,0xd8,0x49,0xc1,0xc0,0x1e,0x49,0x31,0xf0,0x48,0x89,0xde,0x48,0xc1,0xc6,0x19,0x4c,0x31,0xc6,0x49,0x89,0xd0,0x49,0x21,0xc0,0x49,0x89,0xd7,0x49,0x31,0xc7,0x49,0x21,0xdf,0x4d,0x31,0xc7,0x4d,0x89,0xe0,0x49,0xc1,0xc0,0x2d,0x49,0x1,0xf7,0x4c,0x89,0xe6,0x48,0xc1,0xc6,0x3,0x48,0x1,0xf9,0x49,0x89,0xee,0x49,0xd1,0xce,0x49,0x1,0xff,0x48,0x89,0xef,0x48,0xc1,0xc7,0x38,0x4c,0x31,0xc6,0x4c,0x31,0xf7,0x49,0x89,0xe8,0x49,0xc1,0xe8,0x7,0x49,0x31,0xf8,0x4c,0x1,0x64,0x24,0x48,0x4d,0x1,0xe0,0x4c,0x89,0x44,0x24,0x78,0x4c,0x89,0xe7,0x48,0xc1,0xef,0x6,0x49,0x89,0xc8,0x49,0xc1,0xc0,0x32,0x48,0x31,0xf7,0x48,0x89,0xce,0x48,0xc1,0xc6,0x2e,0x4c,0x8b,0xb4,0x24,0x88,0x0,0x0,0x0,0x49,0x1,0xfe,0x48,0x89,0xcf,0x48,0xc1,0xc7,0x17,0x4c,0x31,0xc6,0x48,0x31,0xf7,0x4c,0x8b,0x5,0xba,0xb,0xf,0x0,0x4d,0x1,0xf0,0x4d,0x1,0xc8,0x4c,0x89,0xde,0x4c,0x31,0xd6]

set_option maxRecDepth 4096 in
theorem part29_bytes [Bindings] : part29.flatMap CheckedInstruction.bytes = part29Bytes := by
  rfl

def part29Layout : List (BitVec 64 × Nat) :=
  [(0x10f3ec, 4), (0x10f3f0, 3), (0x10f3f3, 3), (0x10f3f6, 3), (0x10f3f9, 3), (0x10f3fc, 3), (0x10f3ff, 3), (0x10f402, 3), (0x10f405, 3), (0x10f408, 3), (0x10f40b, 3), (0x10f40e, 3), (0x10f411, 4), (0x10f415, 3), (0x10f418, 4), (0x10f41c, 3), (0x10f41f, 3), (0x10f422, 3), (0x10f425, 3), (0x10f428, 4), (0x10f42c, 3), (0x10f42f, 3), (0x10f432, 4), (0x10f436, 3), (0x10f439, 4), (0x10f43d, 3), (0x10f440, 5), (0x10f445, 3), (0x10f448, 4), (0x10f44c, 3), (0x10f44f, 5), (0x10f454, 3), (0x10f457, 3), (0x10f45a, 4), (0x10f45e, 3), (0x10f461, 4), (0x10f465, 3), (0x10f468, 3), (0x10f46b, 4), (0x10f46f, 3), (0x10f472, 7), (0x10f479, 3), (0x10f47c, 3), (0x10f47f, 3), (0x10f482, 3), (0x10f485, 3), (0x10f488, 3), (0x10f48b, 3), (0x10f48e, 3), (0x10f491, 3), (0x10f494, 4), (0x10f498, 3), (0x10f49b, 4), (0x10f49f, 3), (0x10f4a2, 3), (0x10f4a5, 4), (0x10f4a9, 3), (0x10f4ac, 3), (0x10f4af, 3), (0x10f4b2, 3), (0x10f4b5, 3), (0x10f4b8, 3), (0x10f4bb, 3), (0x10f4be, 3), (0x10f4c1, 4), (0x10f4c5, 3), (0x10f4c8, 3), (0x10f4cb, 4), (0x10f4cf, 3), (0x10f4d2, 3), (0x10f4d5, 3), (0x10f4d8, 3), (0x10f4db, 3), (0x10f4de, 4), (0x10f4e2, 3), (0x10f4e5, 3), (0x10f4e8, 3), (0x10f4eb, 4), (0x10f4ef, 3), (0x10f4f2, 5), (0x10f4f7, 3), (0x10f4fa, 5), (0x10f4ff, 3), (0x10f502, 4), (0x10f506, 3), (0x10f509, 4), (0x10f50d, 3), (0x10f510, 3), (0x10f513, 4), (0x10f517, 8), (0x10f51f, 3), (0x10f522, 3), (0x10f525, 4), (0x10f529, 3), (0x10f52c, 3), (0x10f52f, 7), (0x10f536, 3), (0x10f539, 3), (0x10f53c, 3), (0x10f53f, 3)]

theorem part29_layout [Bindings] : InstructionTrace.layout part29 = part29Layout := by
  rfl

theorem part29_ordered [Bindings] : InstructionTrace.ordered 0x10f3ec part29 = true := by
  rw [InstructionTrace.ordered_eq_layout, part29_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part29_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xf3ec 342 = part29Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
