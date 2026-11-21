import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part49

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part50 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110fc8 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110fcc 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110fcf 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110fd2 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef23f) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110fd9 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110fdc 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110fdf 0x4c 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110fe2 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110fe5 0x48 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110fe8 0x48 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110feb 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110fee 0x48 0xc7 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ff2 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110ff5 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110ff8 0x48 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110ffc 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110fff 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111002 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111006 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111009 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11100c 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11100f 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111012 0x4c 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111015 0x4c 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111018 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11101b 0x48 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11101e 0x48 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111021 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111024 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111028 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11102b 0x4c 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11102e 0x48 0xc7 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111032 0x48 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111035 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x111038 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11103c 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11103f 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111043 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111046 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11104a 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11104d 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111050 0x48 0xc7 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111054 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111059 0x49 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11105c 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11105f 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111063 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111066 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111069 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef1b0) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111070 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111073 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111076 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111079 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11107c 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11107f 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111082 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111085 0x49 0xc3 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111089 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11108c 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11108f 0x48 0xc7 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111093 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111096 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111099 0x48 0xc0 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11109d 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1110a0 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110a3 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1110a6 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110a9 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1110ac 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1110af 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1110b2 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1110b5 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110b8 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1110bb 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1110bf 0x49 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110c2 0x4c 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1110c5 0x48 0xc7 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1110c9 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1110cc 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x1110cf 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110d4 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1110d7 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1110db 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1110de 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x1110e3 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1110e8 0x48 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110eb 0x49 0xed (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110ee 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1110f1 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110f5 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1110f8 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1110fc 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1110ff 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111102 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111106 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111109 0x48 (by simp [RexWPrefix]) 1 (.rip 0xef118) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111110 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111113 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111116 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111119 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part50Bytes : List UInt8 :=
  [0x48,0xc1,0xc0,0x17,0x48,0x31,0xca,0x48,0x31,0xd0,0x48,0x8b,0xd,0x3f,0xf2,0xe,0x0,0x4c,0x1,0xe9,0x48,0x1,0xd9,0x4c,0x89,0xd2,0x48,0x31,0xea,0x48,0x21,0xf2,0x48,0x31,0xea,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x24,0x48,0x1,0xd1,0x4c,0x89,0xca,0x48,0xc1,0xc2,0x1e,0x48,0x1,0xc1,0x4c,0x89,0xc8,0x48,0xc1,0xc0,0x19,0x48,0x31,0xfa,0x48,0x31,0xd0,0x4c,0x89,0xf7,0x4c,0x21,0xff,0x4c,0x89,0xf2,0x4c,0x31,0xfa,0x4c,0x21,0xca,0x48,0x31,0xfa,0x48,0x1,0xc2,0x4c,0x89,0xe0,0x48,0xc1,0xc0,0x2d,0x49,0x1,0xc8,0x4c,0x89,0xe7,0x48,0xc1,0xc7,0x3,0x48,0x1,0xca,0x48,0x31,0xc7,0x4c,0x1,0x24,0x24,0x4c,0x89,0xe0,0x48,0xc1,0xe8,0x6,0x4c,0x89,0xc1,0x48,0xc1,0xc1,0x32,0x48,0x31,0xf8,0x4c,0x89,0xc7,0x48,0xc1,0xc7,0x2e,0x4c,0x8b,0x64,0x24,0x58,0x49,0x1,0xc4,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x17,0x48,0x31,0xcf,0x48,0x31,0xf8,0x48,0x8b,0xd,0xb0,0xf1,0xe,0x0,0x4c,0x1,0xe1,0x48,0x1,0xe9,0x48,0x89,0xf7,0x4c,0x31,0xd7,0x4c,0x21,0xc7,0x4c,0x31,0xd7,0x49,0x89,0xd3,0x49,0xc1,0xc3,0x24,0x48,0x1,0xf9,0x48,0x89,0xd7,0x48,0xc1,0xc7,0x1e,0x48,0x1,0xc1,0x48,0x89,0xd0,0x48,0xc1,0xc0,0x19,0x4c,0x31,0xdf,0x48,0x31,0xf8,0x4c,0x89,0xcf,0x4c,0x21,0xf7,0x4d,0x89,0xcb,0x4d,0x31,0xf3,0x49,0x21,0xd3,0x49,0x31,0xfb,0x49,0x1,0xc3,0x4c,0x89,0xe8,0x48,0xc1,0xc0,0x2d,0x49,0x1,0xcf,0x4c,0x89,0xef,0x48,0xc1,0xc7,0x3,0x49,0x1,0xcb,0x48,0x31,0xc7,0x4c,0x1,0x6c,0x24,0x50,0x4c,0x89,0xe8,0x48,0xc1,0xe8,0x6,0x48,0x31,0xf8,0x48,0x8b,0x6c,0x24,0x60,0x48,0x3,0x6c,0x24,0x20,0x48,0x1,0xc5,0x49,0x89,0xed,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x32,0x4c,0x89,0xf9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x48,0x8b,0xd,0x18,0xf1,0xe,0x0,0x48,0x1,0xe9,0x4c,0x1,0xd1,0x4c,0x89,0xc7,0x48,0x31,0xf7]

set_option maxRecDepth 4096 in
theorem part50_bytes [Bindings] : part50.flatMap CheckedInstruction.bytes = part50Bytes := by
  rfl

def part50Layout : List (BitVec 64 × Nat) :=
  [(0x110fc8, 4), (0x110fcc, 3), (0x110fcf, 3), (0x110fd2, 7), (0x110fd9, 3), (0x110fdc, 3), (0x110fdf, 3), (0x110fe2, 3), (0x110fe5, 3), (0x110fe8, 3), (0x110feb, 3), (0x110fee, 4), (0x110ff2, 3), (0x110ff5, 3), (0x110ff8, 4), (0x110ffc, 3), (0x110fff, 3), (0x111002, 4), (0x111006, 3), (0x111009, 3), (0x11100c, 3), (0x11100f, 3), (0x111012, 3), (0x111015, 3), (0x111018, 3), (0x11101b, 3), (0x11101e, 3), (0x111021, 3), (0x111024, 4), (0x111028, 3), (0x11102b, 3), (0x11102e, 4), (0x111032, 3), (0x111035, 3), (0x111038, 4), (0x11103c, 3), (0x11103f, 4), (0x111043, 3), (0x111046, 4), (0x11104a, 3), (0x11104d, 3), (0x111050, 4), (0x111054, 5), (0x111059, 3), (0x11105c, 3), (0x11105f, 4), (0x111063, 3), (0x111066, 3), (0x111069, 7), (0x111070, 3), (0x111073, 3), (0x111076, 3), (0x111079, 3), (0x11107c, 3), (0x11107f, 3), (0x111082, 3), (0x111085, 4), (0x111089, 3), (0x11108c, 3), (0x11108f, 4), (0x111093, 3), (0x111096, 3), (0x111099, 4), (0x11109d, 3), (0x1110a0, 3), (0x1110a3, 3), (0x1110a6, 3), (0x1110a9, 3), (0x1110ac, 3), (0x1110af, 3), (0x1110b2, 3), (0x1110b5, 3), (0x1110b8, 3), (0x1110bb, 4), (0x1110bf, 3), (0x1110c2, 3), (0x1110c5, 4), (0x1110c9, 3), (0x1110cc, 3), (0x1110cf, 5), (0x1110d4, 3), (0x1110d7, 4), (0x1110db, 3), (0x1110de, 5), (0x1110e3, 5), (0x1110e8, 3), (0x1110eb, 3), (0x1110ee, 3), (0x1110f1, 4), (0x1110f5, 3), (0x1110f8, 4), (0x1110fc, 3), (0x1110ff, 3), (0x111102, 4), (0x111106, 3), (0x111109, 7), (0x111110, 3), (0x111113, 3), (0x111116, 3), (0x111119, 3)]

theorem part50_layout [Bindings] : InstructionTrace.layout part50 = part50Layout := by
  rfl

theorem part50_ordered [Bindings] : InstructionTrace.ordered 0x110fc8 part50 = true := by
  rw [InstructionTrace.ordered_eq_layout, part50_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part50_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x10fc8 340 = part50Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
