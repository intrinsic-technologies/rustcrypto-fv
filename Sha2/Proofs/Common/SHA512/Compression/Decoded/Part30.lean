import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part29

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part30 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f542 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f545 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f548 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f54b 0x49 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f54f 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f552 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f555 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f559 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f55c 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f55f 0x48 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f563 0x4c 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f566 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f569 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f56c 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f56f 0x49 0xdc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f572 0x49 0xd4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f575 0x4d 0xfc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f578 0x49 0xf4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f57b 0x49 0xfc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f57e 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f581 0x48 0xc7 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f585 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f588 0x48 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f58b 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f58f 0x4d 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f592 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f595 0x49 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f598 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f59b 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f59e 0x48 0xc7 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f5a2 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f5a5 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f5a8 0x49 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f5ac 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f5af 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f5b4 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f5b7 0x4c (by simp [RexWPrefix]) 8 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f5bc 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f5bf 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f5c3 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f5c6 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f5c9 0x48 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f5cd 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d32 200)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f5d5 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f5d8 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f5db 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f5df 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f5e2 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f5e5 0x48 0xc6 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f5e9 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f5ec 0x48 (by simp [RexWPrefix]) 7 (.rip 0xf0b05) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f5f3 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f5f6 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f5f9 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f5fc 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f5ff 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f602 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f605 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f608 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f60b 0x49 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f60f 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f612 0x4c 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f615 0x48 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f619 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f61c 0x4d 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f61f 0x49 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f623 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f626 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f629 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f62c 0x4d 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f62f 0x49 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10f632 0x4d 0xe5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f635 0x49 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f638 0x4d 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f63b 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f63e 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f641 0x49 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f645 0x49 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f648 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f64b 0x48 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f64f 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f652 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10f655 0x48 0xcf (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f658 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f65b 0x49 0xc0 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f65f 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f662 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f665 0x48 0xef 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f669 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10f66c 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f671 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10f674 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f679 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10f67c 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10f680 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10f683 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10f688 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f68b 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10f68e 0x48 0xc6 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10f692 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part30Bytes : List UInt8 :=
  [0x48,0x21,0xce,0x4c,0x31,0xd6,0x4d,0x89,0xf9,0x49,0xc1,0xc1,0x24,0x49,0x1,0xf0,0x4c,0x89,0xfe,0x48,0xc1,0xc6,0x1e,0x49,0x1,0xf8,0x4c,0x89,0xff,0x48,0xc1,0xc7,0x19,0x4c,0x31,0xce,0x48,0x31,0xf7,0x48,0x89,0xde,0x48,0x21,0xd6,0x49,0x89,0xdc,0x49,0x31,0xd4,0x4d,0x21,0xfc,0x49,0x31,0xf4,0x49,0x1,0xfc,0x48,0x89,0xef,0x48,0xc1,0xc7,0x2d,0x4c,0x1,0xc0,0x48,0x89,0xee,0x48,0xc1,0xc6,0x3,0x4d,0x1,0xc4,0x4d,0x89,0xf0,0x49,0xd1,0xc8,0x48,0x31,0xfe,0x4c,0x89,0xf7,0x48,0xc1,0xc7,0x38,0x4c,0x31,0xc7,0x4d,0x89,0xf0,0x49,0xc1,0xe8,0x7,0x49,0x31,0xf8,0x48,0x1,0x6c,0x24,0x28,0x49,0x1,0xe8,0x4c,0x89,0x44,0x24,0x60,0x48,0x89,0xef,0x48,0xc1,0xef,0x6,0x48,0x31,0xf7,0x48,0x89,0xc6,0x48,0xc1,0xc6,0x32,0x4c,0x8b,0x8c,0x24,0xc8,0x0,0x0,0x0,0x49,0x1,0xf9,0x48,0x89,0xc7,0x48,0xc1,0xc7,0x2e,0x48,0x31,0xf7,0x48,0x89,0xc6,0x48,0xc1,0xc6,0x17,0x48,0x31,0xfe,0x48,0x8b,0x3d,0x5,0xb,0xf,0x0,0x4c,0x1,0xcf,0x4c,0x1,0xd7,0x49,0x89,0xc8,0x4d,0x31,0xd8,0x49,0x21,0xc0,0x4d,0x31,0xd8,0x4c,0x1,0xc7,0x4d,0x89,0xe0,0x49,0xc1,0xc0,0x24,0x48,0x1,0xf7,0x4c,0x89,0xe6,0x48,0xc1,0xc6,0x1e,0x4c,0x31,0xc6,0x4d,0x89,0xe0,0x49,0xc1,0xc0,0x19,0x49,0x31,0xf0,0x4c,0x89,0xfe,0x48,0x21,0xde,0x4d,0x89,0xfd,0x49,0x31,0xdd,0x4d,0x21,0xe5,0x49,0x31,0xf5,0x4d,0x1,0xc5,0x48,0x1,0xfa,0x4d,0x89,0xf0,0x49,0xc1,0xc0,0x2d,0x49,0x1,0xfd,0x4c,0x89,0xf6,0x48,0xc1,0xc6,0x3,0x4c,0x31,0xc6,0x4c,0x89,0xcf,0x48,0xd1,0xcf,0x4d,0x89,0xc8,0x49,0xc1,0xc0,0x38,0x49,0x31,0xf8,0x4c,0x89,0xcf,0x48,0xc1,0xef,0x7,0x4c,0x31,0xc7,0x4c,0x1,0x74,0x24,0x40,0x4c,0x1,0xf7,0x48,0x89,0x7c,0x24,0x30,0x4c,0x89,0xf7,0x48,0xc1,0xef,0x6,0x48,0x31,0xf7,0x4c,0x8b,0x54,0x24,0x10,0x49,0x1,0xfa,0x48,0x89,0xd6,0x48,0xc1,0xc6,0x32,0x48,0x89,0xd7]

set_option maxRecDepth 4096 in
theorem part30_bytes [Bindings] : part30.flatMap CheckedInstruction.bytes = part30Bytes := by
  rfl

def part30Layout : List (BitVec 64 × Nat) :=
  [(0x10f542, 3), (0x10f545, 3), (0x10f548, 3), (0x10f54b, 4), (0x10f54f, 3), (0x10f552, 3), (0x10f555, 4), (0x10f559, 3), (0x10f55c, 3), (0x10f55f, 4), (0x10f563, 3), (0x10f566, 3), (0x10f569, 3), (0x10f56c, 3), (0x10f56f, 3), (0x10f572, 3), (0x10f575, 3), (0x10f578, 3), (0x10f57b, 3), (0x10f57e, 3), (0x10f581, 4), (0x10f585, 3), (0x10f588, 3), (0x10f58b, 4), (0x10f58f, 3), (0x10f592, 3), (0x10f595, 3), (0x10f598, 3), (0x10f59b, 3), (0x10f59e, 4), (0x10f5a2, 3), (0x10f5a5, 3), (0x10f5a8, 4), (0x10f5ac, 3), (0x10f5af, 5), (0x10f5b4, 3), (0x10f5b7, 5), (0x10f5bc, 3), (0x10f5bf, 4), (0x10f5c3, 3), (0x10f5c6, 3), (0x10f5c9, 4), (0x10f5cd, 8), (0x10f5d5, 3), (0x10f5d8, 3), (0x10f5db, 4), (0x10f5df, 3), (0x10f5e2, 3), (0x10f5e5, 4), (0x10f5e9, 3), (0x10f5ec, 7), (0x10f5f3, 3), (0x10f5f6, 3), (0x10f5f9, 3), (0x10f5fc, 3), (0x10f5ff, 3), (0x10f602, 3), (0x10f605, 3), (0x10f608, 3), (0x10f60b, 4), (0x10f60f, 3), (0x10f612, 3), (0x10f615, 4), (0x10f619, 3), (0x10f61c, 3), (0x10f61f, 4), (0x10f623, 3), (0x10f626, 3), (0x10f629, 3), (0x10f62c, 3), (0x10f62f, 3), (0x10f632, 3), (0x10f635, 3), (0x10f638, 3), (0x10f63b, 3), (0x10f63e, 3), (0x10f641, 4), (0x10f645, 3), (0x10f648, 3), (0x10f64b, 4), (0x10f64f, 3), (0x10f652, 3), (0x10f655, 3), (0x10f658, 3), (0x10f65b, 4), (0x10f65f, 3), (0x10f662, 3), (0x10f665, 4), (0x10f669, 3), (0x10f66c, 5), (0x10f671, 3), (0x10f674, 5), (0x10f679, 3), (0x10f67c, 4), (0x10f680, 3), (0x10f683, 5), (0x10f688, 3), (0x10f68b, 3), (0x10f68e, 4), (0x10f692, 3)]

theorem part30_layout [Bindings] : InstructionTrace.layout part30 = part30Layout := by
  rfl

theorem part30_ordered [Bindings] : InstructionTrace.ordered 0x10f542 part30 = true := by
  rw [InstructionTrace.ordered_eq_layout, part30_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part30_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xf542 339 = part30Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
