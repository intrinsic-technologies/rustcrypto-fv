import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part47

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part48 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d1e 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d21 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110d24 0x48 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d28 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d2b 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110d2e 0x48 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d32 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110d35 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d3a 0x4c 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110d3d 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d42 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110d45 0x48 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d49 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d4c 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110d4f 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110d53 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d58 0x49 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d5b 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110d5e 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d62 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d65 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110d68 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d6c 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110d6f 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef482) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d76 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d79 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d7c 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d7f 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110d82 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d85 0x4c 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d88 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d8b 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110d8e 0x48 0xc2 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110d92 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d95 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110d98 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110d9c 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110d9f 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110da2 0x48 0xc2 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110da6 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110da9 0x4c 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110dac 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110daf 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110db2 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110db5 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110db8 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110dbb 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110dbe 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110dc1 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110dc6 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110dc9 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110dcd 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110dd0 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110dd3 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110dd7 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110dda 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110ddd 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110de1 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110de4 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110de9 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110dec 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110def 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110df3 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110df6 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110dfa 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110dfd 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e00 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e04 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110e07 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef3f2) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110e0e 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110e11 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e14 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e17 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110e1a 0x48 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e1d 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110e20 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110e23 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e26 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e29 0x48 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e2d 0x4c 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e30 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e34 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e37 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e3a 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e3e 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e41 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110e44 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e47 0x49 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e4a 0x4d 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110e4d 0x4d 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e50 0x49 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110e53 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110e56 0x48 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110e59 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110e5c 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e61 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e64 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110e68 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110e6b 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110e6f 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part48Bytes : List UInt8 :=
  [0x48,0x31,0xc8,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x38,0x48,0x31,0xd1,0x4c,0x89,0xca,0x48,0xc1,0xea,0x7,0x48,0x31,0xca,0x4c,0x1,0x6c,0x24,0x58,0x4c,0x1,0xea,0x48,0x89,0x54,0x24,0x40,0x4c,0x89,0xe9,0x48,0xc1,0xe9,0x6,0x48,0x31,0xc1,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x32,0x4c,0x8b,0x64,0x24,0x18,0x49,0x1,0xcc,0x48,0x89,0xf9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xf8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x82,0xf4,0xe,0x0,0x4c,0x1,0xe1,0x4c,0x1,0xc1,0x4c,0x89,0xf2,0x4c,0x31,0xda,0x48,0x21,0xfa,0x4c,0x31,0xda,0x48,0x1,0xd1,0x48,0x89,0xf2,0x48,0xc1,0xc2,0x24,0x48,0x1,0xc1,0x48,0x89,0xf0,0x48,0xc1,0xc0,0x1e,0x48,0x31,0xd0,0x48,0x89,0xf2,0x48,0xc1,0xc2,0x19,0x48,0x31,0xc2,0x4c,0x89,0xd0,0x48,0x21,0xe8,0x4d,0x89,0xd0,0x49,0x31,0xe8,0x49,0x21,0xf0,0x49,0x31,0xc0,0x49,0x1,0xd0,0x48,0x1,0xcb,0x4c,0x89,0x4c,0x24,0x20,0x4c,0x89,0xc8,0x48,0xc1,0xc0,0x2d,0x49,0x1,0xc8,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x3,0x48,0x31,0xc1,0x4c,0x89,0xc8,0x48,0xc1,0xe8,0x6,0x48,0x31,0xc8,0x4c,0x8b,0x4c,0x24,0x10,0x49,0x1,0xc1,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x32,0x48,0x89,0xd9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0xf2,0xf3,0xe,0x0,0x4c,0x1,0xc9,0x4c,0x1,0xd9,0x48,0x89,0xfa,0x4c,0x31,0xf2,0x48,0x21,0xda,0x4c,0x31,0xf2,0x48,0x1,0xd1,0x48,0x1,0xc1,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x24,0x4c,0x89,0xc2,0x48,0xc1,0xc2,0x1e,0x48,0x31,0xc2,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x19,0x48,0x31,0xd0,0x48,0x89,0xf2,0x4c,0x21,0xd2,0x49,0x89,0xf7,0x4d,0x31,0xd7,0x4d,0x21,0xc7,0x49,0x31,0xd7,0x49,0x1,0xc7,0x48,0x1,0xcd,0x49,0x1,0xcf,0x4c,0x89,0x64,0x24,0x18,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x2d,0x4c,0x89,0xe1,0x48,0xc1,0xc1,0x3,0x48,0x31,0xc1]

set_option maxRecDepth 4096 in
theorem part48_bytes [Bindings] : part48.flatMap CheckedInstruction.bytes = part48Bytes := by
  rfl

def part48Layout : List (BitVec 64 × Nat) :=
  [(0x110d1e, 3), (0x110d21, 3), (0x110d24, 4), (0x110d28, 3), (0x110d2b, 3), (0x110d2e, 4), (0x110d32, 3), (0x110d35, 5), (0x110d3a, 3), (0x110d3d, 5), (0x110d42, 3), (0x110d45, 4), (0x110d49, 3), (0x110d4c, 3), (0x110d4f, 4), (0x110d53, 5), (0x110d58, 3), (0x110d5b, 3), (0x110d5e, 4), (0x110d62, 3), (0x110d65, 3), (0x110d68, 4), (0x110d6c, 3), (0x110d6f, 7), (0x110d76, 3), (0x110d79, 3), (0x110d7c, 3), (0x110d7f, 3), (0x110d82, 3), (0x110d85, 3), (0x110d88, 3), (0x110d8b, 3), (0x110d8e, 4), (0x110d92, 3), (0x110d95, 3), (0x110d98, 4), (0x110d9c, 3), (0x110d9f, 3), (0x110da2, 4), (0x110da6, 3), (0x110da9, 3), (0x110dac, 3), (0x110daf, 3), (0x110db2, 3), (0x110db5, 3), (0x110db8, 3), (0x110dbb, 3), (0x110dbe, 3), (0x110dc1, 5), (0x110dc6, 3), (0x110dc9, 4), (0x110dcd, 3), (0x110dd0, 3), (0x110dd3, 4), (0x110dd7, 3), (0x110dda, 3), (0x110ddd, 4), (0x110de1, 3), (0x110de4, 5), (0x110de9, 3), (0x110dec, 3), (0x110def, 4), (0x110df3, 3), (0x110df6, 4), (0x110dfa, 3), (0x110dfd, 3), (0x110e00, 4), (0x110e04, 3), (0x110e07, 7), (0x110e0e, 3), (0x110e11, 3), (0x110e14, 3), (0x110e17, 3), (0x110e1a, 3), (0x110e1d, 3), (0x110e20, 3), (0x110e23, 3), (0x110e26, 3), (0x110e29, 4), (0x110e2d, 3), (0x110e30, 4), (0x110e34, 3), (0x110e37, 3), (0x110e3a, 4), (0x110e3e, 3), (0x110e41, 3), (0x110e44, 3), (0x110e47, 3), (0x110e4a, 3), (0x110e4d, 3), (0x110e50, 3), (0x110e53, 3), (0x110e56, 3), (0x110e59, 3), (0x110e5c, 5), (0x110e61, 3), (0x110e64, 4), (0x110e68, 3), (0x110e6b, 4), (0x110e6f, 3)]

theorem part48_layout [Bindings] : InstructionTrace.layout part48 = part48Layout := by
  rfl

theorem part48_ordered [Bindings] : InstructionTrace.ordered 0x110d1e part48 = true := by
  rw [InstructionTrace.ordered_eq_layout, part48_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part48_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x10d1e 340 = part48Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
