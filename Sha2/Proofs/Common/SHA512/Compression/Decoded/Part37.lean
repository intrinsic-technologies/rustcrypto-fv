import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part36

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part37 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fe84 0x4d 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fe87 0x49 0xee 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fe8b 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10fe8e 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fe96 0x4d 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10fe99 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fe9e 0x49 0xec 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fea2 0x4d 0xdc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fea5 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fea8 0x49 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10feac 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10feb1 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10feb4 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10feb7 0x48 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10febb 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10febe 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fec1 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fec5 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10fec8 0x48 (by simp [RexWPrefix]) 3 (.rip 0xf0289) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fecf 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fed2 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fed5 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fed8 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10fedb 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fede 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10fee1 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fee4 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fee7 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10feeb 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10feee 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fef1 0x49 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fef5 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fef8 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fefb 0x49 0xc6 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10feff 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff02 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ff05 0x49 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff08 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff0b 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ff0e 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff11 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff14 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff17 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff1a 0x4d 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ff1d 0x49 0xc6 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff21 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff24 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ff27 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff2b 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff2e 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10ff31 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff34 0x49 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ff37 0x49 0xc6 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff3b 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff3e 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ff41 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff45 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x10ff48 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff4d 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x10ff50 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10ff55 0x49 0xed 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff59 0x4d 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ff5c 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff61 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff64 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ff67 0x49 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff6b 0x4c 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ff6e 0x48 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff72 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff75 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ff78 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff7c 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x10ff7f 0x48 (by simp [RexWPrefix]) 3 (.rip 0xf01da) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff86 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff89 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff8c 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff8f 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ff92 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ff95 0x4c 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff98 0x48 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ff9b 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ff9e 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ffa1 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffa5 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ffa8 0x49 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ffac 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffaf 0x49 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ffb2 0x49 0xc6 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ffb6 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffb9 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ffbc 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffbf 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ffc2 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x10ffc5 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ffc8 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ffcb 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ffce 0x48 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x10ffd1 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffd4 0x49 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffd7 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part37Bytes : List UInt8 :=
  [0x4d,0x89,0xee,0x49,0xc1,0xee,0x7,0x49,0x31,0xde,0x4c,0x1,0xa4,0x24,0x80,0x0,0x0,0x0,0x4d,0x1,0xe6,0x4c,0x89,0x74,0x24,0x40,0x49,0xc1,0xec,0x6,0x4d,0x31,0xdc,0x49,0x89,0xfb,0x49,0xc1,0xc3,0x32,0x48,0x8b,0x44,0x24,0x50,0x4c,0x1,0xe0,0x48,0x89,0xfb,0x48,0xc1,0xc3,0x2e,0x4c,0x31,0xdb,0x49,0x89,0xfb,0x49,0xc1,0xc3,0x17,0x49,0x31,0xdb,0x48,0x8b,0x1d,0x89,0x2,0xf,0x0,0x48,0x1,0xc3,0x48,0x1,0xd3,0x4c,0x89,0xfa,0x48,0x31,0xf2,0x48,0x21,0xfa,0x48,0x31,0xf2,0x48,0x1,0xd3,0x4c,0x89,0xd2,0x48,0xc1,0xc2,0x24,0x4c,0x1,0xdb,0x4d,0x89,0xd3,0x49,0xc1,0xc3,0x1e,0x49,0x31,0xd3,0x4d,0x89,0xd6,0x49,0xc1,0xc6,0x19,0x4d,0x31,0xde,0x49,0x89,0xcb,0x49,0x21,0xeb,0x48,0x89,0xca,0x48,0x31,0xea,0x4c,0x21,0xd2,0x4c,0x31,0xda,0x4c,0x1,0xf2,0x49,0x1,0xd8,0x4d,0x89,0xee,0x49,0xc1,0xc6,0x2d,0x48,0x1,0xda,0x4d,0x89,0xeb,0x49,0xc1,0xc3,0x3,0x4d,0x31,0xf3,0x48,0x89,0xc3,0x48,0xd1,0xcb,0x49,0x89,0xc6,0x49,0xc1,0xc6,0x38,0x49,0x31,0xde,0x49,0x89,0xc1,0x49,0xc1,0xe9,0x7,0x4d,0x31,0xf1,0x4c,0x1,0x6c,0x24,0x58,0x4d,0x1,0xe9,0x4c,0x89,0x4c,0x24,0x50,0x49,0xc1,0xed,0x6,0x4d,0x31,0xdd,0x4c,0x8b,0x4c,0x24,0x78,0x4d,0x1,0xe9,0x4d,0x89,0xc3,0x49,0xc1,0xc3,0x32,0x4c,0x89,0xc3,0x48,0xc1,0xc3,0x2e,0x4c,0x31,0xdb,0x4d,0x89,0xc3,0x49,0xc1,0xc3,0x17,0x49,0x31,0xdb,0x48,0x8b,0x1d,0xda,0x1,0xf,0x0,0x4c,0x1,0xcb,0x48,0x1,0xf3,0x48,0x89,0xfe,0x4c,0x31,0xfe,0x4c,0x21,0xc6,0x4c,0x31,0xfe,0x48,0x1,0xf3,0x4c,0x1,0xdb,0x48,0x89,0xd6,0x48,0xc1,0xc6,0x24,0x49,0x89,0xd3,0x49,0xc1,0xc3,0x1e,0x49,0x31,0xf3,0x49,0x89,0xd6,0x49,0xc1,0xc6,0x19,0x4d,0x31,0xde,0x4d,0x89,0xd3,0x49,0x21,0xcb,0x4c,0x89,0xd6,0x48,0x31,0xce,0x48,0x21,0xd6,0x4c,0x31,0xde,0x4c,0x1,0xf6,0x48,0x1,0xdd,0x48,0x1,0xde,0x49,0x89,0xc5,0x48,0x89,0xc3]

set_option maxRecDepth 4096 in
theorem part37_bytes [Bindings] : part37.flatMap CheckedInstruction.bytes = part37Bytes := by
  rfl

def part37Layout : List (BitVec 64 × Nat) :=
  [(0x10fe84, 3), (0x10fe87, 4), (0x10fe8b, 3), (0x10fe8e, 8), (0x10fe96, 3), (0x10fe99, 5), (0x10fe9e, 4), (0x10fea2, 3), (0x10fea5, 3), (0x10fea8, 4), (0x10feac, 5), (0x10feb1, 3), (0x10feb4, 3), (0x10feb7, 4), (0x10febb, 3), (0x10febe, 3), (0x10fec1, 4), (0x10fec5, 3), (0x10fec8, 7), (0x10fecf, 3), (0x10fed2, 3), (0x10fed5, 3), (0x10fed8, 3), (0x10fedb, 3), (0x10fede, 3), (0x10fee1, 3), (0x10fee4, 3), (0x10fee7, 4), (0x10feeb, 3), (0x10feee, 3), (0x10fef1, 4), (0x10fef5, 3), (0x10fef8, 3), (0x10fefb, 4), (0x10feff, 3), (0x10ff02, 3), (0x10ff05, 3), (0x10ff08, 3), (0x10ff0b, 3), (0x10ff0e, 3), (0x10ff11, 3), (0x10ff14, 3), (0x10ff17, 3), (0x10ff1a, 3), (0x10ff1d, 4), (0x10ff21, 3), (0x10ff24, 3), (0x10ff27, 4), (0x10ff2b, 3), (0x10ff2e, 3), (0x10ff31, 3), (0x10ff34, 3), (0x10ff37, 4), (0x10ff3b, 3), (0x10ff3e, 3), (0x10ff41, 4), (0x10ff45, 3), (0x10ff48, 5), (0x10ff4d, 3), (0x10ff50, 5), (0x10ff55, 4), (0x10ff59, 3), (0x10ff5c, 5), (0x10ff61, 3), (0x10ff64, 3), (0x10ff67, 4), (0x10ff6b, 3), (0x10ff6e, 4), (0x10ff72, 3), (0x10ff75, 3), (0x10ff78, 4), (0x10ff7c, 3), (0x10ff7f, 7), (0x10ff86, 3), (0x10ff89, 3), (0x10ff8c, 3), (0x10ff8f, 3), (0x10ff92, 3), (0x10ff95, 3), (0x10ff98, 3), (0x10ff9b, 3), (0x10ff9e, 3), (0x10ffa1, 4), (0x10ffa5, 3), (0x10ffa8, 4), (0x10ffac, 3), (0x10ffaf, 3), (0x10ffb2, 4), (0x10ffb6, 3), (0x10ffb9, 3), (0x10ffbc, 3), (0x10ffbf, 3), (0x10ffc2, 3), (0x10ffc5, 3), (0x10ffc8, 3), (0x10ffcb, 3), (0x10ffce, 3), (0x10ffd1, 3), (0x10ffd4, 3), (0x10ffd7, 3)]

theorem part37_layout [Bindings] : InstructionTrace.layout part37 = part37Layout := by
  rfl

theorem part37_ordered [Bindings] : InstructionTrace.ordered 0x10fe84 part37 = true := by
  rw [InstructionTrace.ordered_eq_layout, part37_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part37_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xfe84 342 = part37Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
