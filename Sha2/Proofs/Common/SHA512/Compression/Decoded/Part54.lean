import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part53

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part54 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111534 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111537 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11153a 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11153d 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111540 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111543 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111547 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11154a 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11154d 0x48 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111551 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111554 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111557 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11155b 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11155e 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111561 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111564 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111567 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11156a 0x4d 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11156d 0x4d 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111570 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111573 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111576 0x4c 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111579 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11157c 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111580 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111583 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111586 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11158a 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11158d 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111590 0x48 0xea 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111594 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111597 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11159c 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11159f 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115a4 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1115a7 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115ab 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1115ae 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1115b2 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115b5 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1115b8 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1115bc 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1115bf 0x49 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1115c2 0x4d 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115c5 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1115c8 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1115cb 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1115ce 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1115d1 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1115d4 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115d7 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1115da 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115de 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1115e1 0x48 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1115e5 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115e8 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1115eb 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1115ef 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115f2 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1115f5 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1115f8 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1115fb 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1115fe 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111601 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111604 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111607 0x4d 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11160a 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11160d 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111610 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111613 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111617 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11161a 0x48 0xc2 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11161e 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111621 0x48 0xee 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111625 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111628 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11162b 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11162f 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111634 0x49 0xf4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111637 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11163a 0x48 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11163e 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111641 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111644 0x48 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111648 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11164b 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111650 0x4d 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111653 0x49 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111656 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111659 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11165c 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11165f 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111662 0x49 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111665 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111668 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11166b 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11166f 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111672 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111676 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111679 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part54Bytes : List UInt8 :=
  [0x48,0x89,0xd9,0x4c,0x31,0xd9,0x48,0x21,0xe9,0x4c,0x31,0xd9,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x24,0x48,0x1,0xce,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x1e,0x48,0x1,0xc6,0x4c,0x89,0xc8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xd1,0x48,0x31,0xc8,0x4c,0x89,0xc1,0x4c,0x21,0xe9,0x4d,0x89,0xc6,0x4d,0x31,0xee,0x4d,0x21,0xce,0x49,0x31,0xce,0x49,0x1,0xc6,0x4c,0x89,0xe2,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x2d,0x48,0x1,0xf7,0x4c,0x89,0xe1,0x48,0xc1,0xc1,0x3,0x49,0x1,0xf6,0x48,0x31,0xc1,0x48,0xc1,0xea,0x6,0x48,0x31,0xca,0x48,0x8b,0x74,0x24,0x30,0x48,0x1,0xd6,0x48,0x89,0x74,0x24,0x30,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x32,0x48,0x89,0xf9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x49,0x1,0xf7,0x4d,0x1,0xdf,0x48,0x89,0xe9,0x48,0x31,0xd9,0x48,0x21,0xf9,0x48,0x31,0xd9,0x49,0x1,0xcf,0x49,0x1,0xc7,0x4c,0x89,0xf0,0x48,0xc1,0xc0,0x24,0x4c,0x89,0xf1,0x48,0xc1,0xc1,0x1e,0x48,0x31,0xc1,0x4c,0x89,0xf2,0x48,0xc1,0xc2,0x19,0x48,0x31,0xca,0x4c,0x89,0xc9,0x4c,0x21,0xc1,0x4c,0x89,0xc8,0x4c,0x31,0xc0,0x4c,0x21,0xf0,0x48,0x31,0xc8,0x48,0x1,0xd0,0x4d,0x1,0xfd,0x4c,0x1,0xf8,0x4c,0x89,0xd6,0x4c,0x89,0xd1,0x48,0xc1,0xc1,0x2d,0x4c,0x89,0xd2,0x48,0xc1,0xc2,0x3,0x48,0x31,0xca,0x48,0xc1,0xee,0x6,0x48,0x31,0xd6,0x4c,0x89,0xe9,0x48,0xc1,0xc1,0x32,0x4c,0x8b,0x64,0x24,0x40,0x49,0x1,0xf4,0x4c,0x89,0xea,0x48,0xc1,0xc2,0x2e,0x48,0x31,0xca,0x4c,0x89,0xe9,0x48,0xc1,0xc1,0x17,0x48,0x31,0xd1,0x4c,0x8b,0x7c,0x24,0x28,0x4d,0x1,0xe7,0x49,0x1,0xdf,0x48,0x89,0xfa,0x48,0x31,0xea,0x4c,0x21,0xea,0x48,0x31,0xea,0x49,0x1,0xd7,0x49,0x1,0xcf,0x48,0x89,0xc1,0x48,0xc1,0xc1,0x24,0x48,0x89,0xc2,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xca,0x48,0x89,0xc3]

set_option maxRecDepth 4096 in
theorem part54_bytes [Bindings] : part54.flatMap CheckedInstruction.bytes = part54Bytes := by
  rfl

def part54Layout : List (BitVec 64 × Nat) :=
  [(0x111534, 3), (0x111537, 3), (0x11153a, 3), (0x11153d, 3), (0x111540, 3), (0x111543, 4), (0x111547, 3), (0x11154a, 3), (0x11154d, 4), (0x111551, 3), (0x111554, 3), (0x111557, 4), (0x11155b, 3), (0x11155e, 3), (0x111561, 3), (0x111564, 3), (0x111567, 3), (0x11156a, 3), (0x11156d, 3), (0x111570, 3), (0x111573, 3), (0x111576, 3), (0x111579, 3), (0x11157c, 4), (0x111580, 3), (0x111583, 3), (0x111586, 4), (0x11158a, 3), (0x11158d, 3), (0x111590, 4), (0x111594, 3), (0x111597, 5), (0x11159c, 3), (0x11159f, 5), (0x1115a4, 3), (0x1115a7, 4), (0x1115ab, 3), (0x1115ae, 4), (0x1115b2, 3), (0x1115b5, 3), (0x1115b8, 4), (0x1115bc, 3), (0x1115bf, 3), (0x1115c2, 3), (0x1115c5, 3), (0x1115c8, 3), (0x1115cb, 3), (0x1115ce, 3), (0x1115d1, 3), (0x1115d4, 3), (0x1115d7, 3), (0x1115da, 4), (0x1115de, 3), (0x1115e1, 4), (0x1115e5, 3), (0x1115e8, 3), (0x1115eb, 4), (0x1115ef, 3), (0x1115f2, 3), (0x1115f5, 3), (0x1115f8, 3), (0x1115fb, 3), (0x1115fe, 3), (0x111601, 3), (0x111604, 3), (0x111607, 3), (0x11160a, 3), (0x11160d, 3), (0x111610, 3), (0x111613, 4), (0x111617, 3), (0x11161a, 4), (0x11161e, 3), (0x111621, 4), (0x111625, 3), (0x111628, 3), (0x11162b, 4), (0x11162f, 5), (0x111634, 3), (0x111637, 3), (0x11163a, 4), (0x11163e, 3), (0x111641, 3), (0x111644, 4), (0x111648, 3), (0x11164b, 5), (0x111650, 3), (0x111653, 3), (0x111656, 3), (0x111659, 3), (0x11165c, 3), (0x11165f, 3), (0x111662, 3), (0x111665, 3), (0x111668, 3), (0x11166b, 4), (0x11166f, 3), (0x111672, 4), (0x111676, 3), (0x111679, 3)]

theorem part54_layout [Bindings] : InstructionTrace.layout part54 = part54Layout := by
  rfl

theorem part54_ordered [Bindings] : InstructionTrace.ordered 0x111534 part54 = true := by
  rw [InstructionTrace.ordered_eq_layout, part54_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part54_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x11534 328 = part54Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
