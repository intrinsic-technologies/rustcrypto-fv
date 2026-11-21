import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part37

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part38 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ffda 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffde 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10ffe1 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ffe5 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffe8 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10ffeb 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x10ffee 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x10fff1 0x4d 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x10fff4 0x49 0xc6 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10fff8 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x10fffb 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x10ffff 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110002 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110007 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11000a 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11000f 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110012 0x48 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110016 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110019 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11001e 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110021 0x49 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110024 0x49 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110028 0x48 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11002b 0x48 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11002f 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110032 0x49 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110035 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110039 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11003c 0x48 (by simp [RexWPrefix]) 3 (.rip 0xf0125) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110043 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110046 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110049 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11004c 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11004f 0x49 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110052 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110055 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110058 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11005b 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11005e 0x49 0xc3 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110062 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110065 0x49 0xc6 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110069 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11006c 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11006f 0x49 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110073 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110076 0x49 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110079 0x4d 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11007c 0x49 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11007f 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110082 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110085 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110088 0x49 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11008b 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11008e 0x49 0xc7 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110092 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110095 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110098 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11009c 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11009f 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x1100a2 0x49 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1100a5 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1100a8 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1100ab 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1100af 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1100b2 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1100b5 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1100b8 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1100bc 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x1100bf 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1100c4 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1100c7 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1100cc 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1100cf 0x49 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1100d3 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1100d6 0x48 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1100da 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1100dd 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1100e0 0x49 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1100e4 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1100e9 0x4d 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1100ec 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1100ef 0x49 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1100f3 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1100f6 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1100f9 0x4c (by simp [RexWPrefix]) 15 (.rip 0xf0070) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110100 0x4d 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110103 0x49 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110106 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110109 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11010c 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11010f 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110112 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110115 0x49 0xc3 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110119 0x49 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11011c 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11011f 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110123 0x4d 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110126 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110129 0x49 0xc1 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11012d 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part38Bytes : List UInt8 :=
  [0x48,0xc1,0xc3,0x2d,0x49,0x89,0xc3,0x49,0xc1,0xc3,0x3,0x49,0x31,0xdb,0x4c,0x89,0xc8,0x4c,0x89,0xcb,0x48,0xd1,0xcb,0x4d,0x89,0xce,0x49,0xc1,0xc6,0x38,0x49,0x31,0xde,0x49,0xc1,0xe9,0x7,0x4d,0x31,0xf1,0x4c,0x1,0x6c,0x24,0x8,0x4d,0x1,0xe9,0x4c,0x89,0x4c,0x24,0x48,0x4c,0x89,0xeb,0x48,0xc1,0xeb,0x6,0x4c,0x31,0xdb,0x4c,0x8b,0x4c,0x24,0x60,0x49,0x1,0xd9,0x49,0x89,0xeb,0x49,0xc1,0xc3,0x32,0x48,0x89,0xeb,0x48,0xc1,0xc3,0x2e,0x4c,0x31,0xdb,0x49,0x89,0xeb,0x49,0xc1,0xc3,0x17,0x49,0x31,0xdb,0x48,0x8b,0x1d,0x25,0x1,0xf,0x0,0x4c,0x1,0xcb,0x4c,0x1,0xfb,0x4d,0x89,0xc6,0x49,0x31,0xfe,0x49,0x21,0xee,0x49,0x31,0xfe,0x4c,0x1,0xf3,0x4c,0x1,0xdb,0x49,0x89,0xf3,0x49,0xc1,0xc3,0x24,0x49,0x89,0xf6,0x49,0xc1,0xc6,0x1e,0x4d,0x31,0xde,0x49,0x89,0xf3,0x49,0xc1,0xc3,0x19,0x4d,0x31,0xf3,0x49,0x89,0xd7,0x4d,0x21,0xd7,0x49,0x89,0xd6,0x4d,0x31,0xd6,0x49,0x21,0xf6,0x4d,0x31,0xfe,0x49,0x89,0xc5,0x49,0x89,0xc7,0x49,0xc1,0xc7,0x2d,0x4d,0x1,0xde,0x49,0x89,0xc3,0x49,0xc1,0xc3,0x3,0x48,0x1,0xd9,0x4c,0x89,0xc8,0x49,0xd1,0xc9,0x49,0x1,0xde,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x38,0x4d,0x31,0xfb,0x4c,0x31,0xcb,0x49,0x89,0xc1,0x49,0xc1,0xe9,0x7,0x49,0x31,0xd9,0x4c,0x1,0x6c,0x24,0x28,0x4d,0x1,0xe9,0x4c,0x89,0x4c,0x24,0x68,0x4d,0x89,0xe9,0x49,0xc1,0xe9,0x6,0x48,0x89,0xcb,0x48,0xc1,0xc3,0x32,0x4d,0x31,0xd9,0x49,0x89,0xcb,0x49,0xc1,0xc3,0x2e,0x4c,0x8b,0x64,0x24,0x30,0x4d,0x1,0xcc,0x49,0x89,0xc9,0x49,0xc1,0xc1,0x17,0x49,0x31,0xdb,0x4d,0x31,0xd9,0x4c,0x8b,0x3d,0x70,0x0,0xf,0x0,0x4d,0x1,0xe7,0x49,0x1,0xff,0x48,0x89,0xef,0x4c,0x31,0xc7,0x48,0x21,0xcf,0x4c,0x31,0xc7,0x4d,0x89,0xf3,0x49,0xc1,0xc3,0x24,0x49,0x1,0xff,0x4c,0x89,0xf7,0x48,0xc1,0xc7,0x1e,0x4d,0x1,0xcf,0x4d,0x89,0xf1,0x49,0xc1,0xc1,0x19,0x4c,0x31,0xdf]

set_option maxRecDepth 4096 in
theorem part38_bytes [Bindings] : part38.flatMap CheckedInstruction.bytes = part38Bytes := by
  rfl

def part38Layout : List (BitVec 64 × Nat) :=
  [(0x10ffda, 4), (0x10ffde, 3), (0x10ffe1, 4), (0x10ffe5, 3), (0x10ffe8, 3), (0x10ffeb, 3), (0x10ffee, 3), (0x10fff1, 3), (0x10fff4, 4), (0x10fff8, 3), (0x10fffb, 4), (0x10ffff, 3), (0x110002, 5), (0x110007, 3), (0x11000a, 5), (0x11000f, 3), (0x110012, 4), (0x110016, 3), (0x110019, 5), (0x11001e, 3), (0x110021, 3), (0x110024, 4), (0x110028, 3), (0x11002b, 4), (0x11002f, 3), (0x110032, 3), (0x110035, 4), (0x110039, 3), (0x11003c, 7), (0x110043, 3), (0x110046, 3), (0x110049, 3), (0x11004c, 3), (0x11004f, 3), (0x110052, 3), (0x110055, 3), (0x110058, 3), (0x11005b, 3), (0x11005e, 4), (0x110062, 3), (0x110065, 4), (0x110069, 3), (0x11006c, 3), (0x11006f, 4), (0x110073, 3), (0x110076, 3), (0x110079, 3), (0x11007c, 3), (0x11007f, 3), (0x110082, 3), (0x110085, 3), (0x110088, 3), (0x11008b, 3), (0x11008e, 4), (0x110092, 3), (0x110095, 3), (0x110098, 4), (0x11009c, 3), (0x11009f, 3), (0x1100a2, 3), (0x1100a5, 3), (0x1100a8, 3), (0x1100ab, 4), (0x1100af, 3), (0x1100b2, 3), (0x1100b5, 3), (0x1100b8, 4), (0x1100bc, 3), (0x1100bf, 5), (0x1100c4, 3), (0x1100c7, 5), (0x1100cc, 3), (0x1100cf, 4), (0x1100d3, 3), (0x1100d6, 4), (0x1100da, 3), (0x1100dd, 3), (0x1100e0, 4), (0x1100e4, 5), (0x1100e9, 3), (0x1100ec, 3), (0x1100ef, 4), (0x1100f3, 3), (0x1100f6, 3), (0x1100f9, 7), (0x110100, 3), (0x110103, 3), (0x110106, 3), (0x110109, 3), (0x11010c, 3), (0x11010f, 3), (0x110112, 3), (0x110115, 4), (0x110119, 3), (0x11011c, 3), (0x11011f, 4), (0x110123, 3), (0x110126, 3), (0x110129, 4), (0x11012d, 3)]

theorem part38_layout [Bindings] : InstructionTrace.layout part38 = part38Layout := by
  rfl

theorem part38_ordered [Bindings] : InstructionTrace.ordered 0x10ffda part38 = true := by
  rw [InstructionTrace.ordered_eq_layout, part38_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part38_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0xffda 342 = part38Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
