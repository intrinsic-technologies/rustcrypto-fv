import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part38

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part39 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110130 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110133 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110136 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110139 0x48 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11013c 0x48 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11013f 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110142 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110145 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110148 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11014b 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11014f 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110152 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110155 0x49 0xc3 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110159 0x4c 0xff (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11015c 0x4d 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11015f 0x4d 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110162 0x49 0xc9 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110165 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110168 0x4c 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11016b 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11016f 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110172 0x4d 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110175 0x49 0xe9 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110179 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11017c 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d32 136)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110184 0x49 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110187 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11018a 0x4c (by simp [RexWPrefix]) 9 (.sib 4 none 0 (.d8 48)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11018f 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110192 0x49 0xe9 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110196 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110199 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11019c 0x49 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1101a0 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1101a5 0x4d 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1101a8 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1101ab 0x49 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1101af 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1101b2 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1101b5 0x49 0xc3 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1101b9 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1101bc 0x4c (by simp [RexWPrefix]) 9 (.rip 0xeffb5) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1101c3 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1101c6 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1101c9 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1101cc 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1101cf 0x4d 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1101d2 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1101d5 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1101d8 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1101db 0x49 0xc0 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1101df 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1101e2 0x49 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1101e5 0x49 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1101e9 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1101ec 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1101ef 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1101f3 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1101f6 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1101f9 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1101fc 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1101ff 0x49 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110202 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110205 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110208 0x49 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11020b 0x4c 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11020e 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110211 0x49 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110215 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110218 0x4d 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11021b 0x49 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11021f 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110222 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110225 0x49 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110228 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11022b 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11022f 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110232 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110235 0x48 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110239 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x11023c 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110244 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110247 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11024c 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11024f 0x49 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110253 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110256 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 128)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11025e 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110261 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110264 0x49 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110268 0x49 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11026b 0x49 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11026f 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110272 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110275 0x49 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110279 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11027c 0x4c (by simp [RexWPrefix]) 11 (.rip 0xefefd) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110283 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110286 0x49 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110289 0x4c 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part39Bytes : List UInt8 :=
  [0x49,0x31,0xf9,0x49,0x89,0xf3,0x49,0x21,0xd3,0x48,0x89,0xf7,0x48,0x31,0xd7,0x4c,0x21,0xf7,0x4c,0x31,0xdf,0x4c,0x1,0xcf,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x2d,0x4d,0x1,0xfa,0x49,0x89,0xc3,0x49,0xc1,0xc3,0x3,0x4c,0x1,0xff,0x4d,0x89,0xe7,0x4d,0x89,0xe1,0x49,0xd1,0xc9,0x49,0x31,0xdb,0x4c,0x89,0xe3,0x48,0xc1,0xc3,0x38,0x4c,0x31,0xcb,0x4d,0x89,0xe1,0x49,0xc1,0xe9,0x7,0x49,0x31,0xd9,0x4c,0x8b,0xa4,0x24,0x88,0x0,0x0,0x0,0x49,0x1,0xc4,0x49,0x1,0xc1,0x4c,0x89,0x4c,0x24,0x30,0x49,0x89,0xc1,0x49,0xc1,0xe9,0x6,0x4d,0x31,0xd9,0x4d,0x89,0xd3,0x49,0xc1,0xc3,0x32,0x4c,0x8b,0x6c,0x24,0x10,0x4d,0x1,0xcd,0x4d,0x89,0xd1,0x49,0xc1,0xc1,0x2e,0x4d,0x31,0xd9,0x4d,0x89,0xd3,0x49,0xc1,0xc3,0x17,0x4d,0x31,0xcb,0x4c,0x8b,0xd,0xb5,0xff,0xe,0x0,0x4d,0x1,0xe9,0x4d,0x1,0xc1,0x49,0x89,0xc8,0x49,0x31,0xe8,0x4d,0x21,0xd0,0x49,0x31,0xe8,0x4d,0x1,0xc1,0x49,0x89,0xf8,0x49,0xc1,0xc0,0x24,0x4d,0x1,0xd9,0x49,0x89,0xfb,0x49,0xc1,0xc3,0x1e,0x4d,0x31,0xc3,0x48,0x89,0xfb,0x48,0xc1,0xc3,0x19,0x4c,0x31,0xdb,0x4d,0x89,0xf3,0x49,0x21,0xf3,0x4d,0x89,0xf0,0x49,0x31,0xf0,0x49,0x21,0xf8,0x4d,0x31,0xd8,0x49,0x1,0xd8,0x4c,0x1,0xca,0x4d,0x89,0xfb,0x49,0xc1,0xc3,0x2d,0x4d,0x1,0xc8,0x4d,0x89,0xf9,0x49,0xc1,0xc1,0x3,0x4d,0x31,0xd9,0x4d,0x89,0xeb,0x49,0xd1,0xcb,0x4c,0x89,0xeb,0x48,0xc1,0xc3,0x38,0x4c,0x31,0xdb,0x4c,0x89,0xe8,0x48,0xc1,0xe8,0x7,0x48,0x31,0xd8,0x4c,0x1,0xbc,0x24,0x90,0x0,0x0,0x0,0x4c,0x1,0xf8,0x48,0x89,0x44,0x24,0x20,0x4d,0x89,0xfb,0x49,0xc1,0xeb,0x6,0x4d,0x31,0xcb,0x48,0x8b,0x84,0x24,0x80,0x0,0x0,0x0,0x4c,0x1,0xd8,0x49,0x89,0xd1,0x49,0xc1,0xc1,0x32,0x49,0x89,0xd3,0x49,0xc1,0xc3,0x2e,0x4d,0x31,0xcb,0x49,0x89,0xd1,0x49,0xc1,0xc1,0x17,0x4d,0x31,0xd9,0x4c,0x8b,0x1d,0xfd,0xfe,0xe,0x0,0x49,0x1,0xc3,0x49,0x1,0xeb,0x4c,0x89,0xd3]

set_option maxRecDepth 4096 in
theorem part39_bytes [Bindings] : part39.flatMap CheckedInstruction.bytes = part39Bytes := by
  rfl

def part39Layout : List (BitVec 64 × Nat) :=
  [(0x110130, 3), (0x110133, 3), (0x110136, 3), (0x110139, 3), (0x11013c, 3), (0x11013f, 3), (0x110142, 3), (0x110145, 3), (0x110148, 3), (0x11014b, 4), (0x11014f, 3), (0x110152, 3), (0x110155, 4), (0x110159, 3), (0x11015c, 3), (0x11015f, 3), (0x110162, 3), (0x110165, 3), (0x110168, 3), (0x11016b, 4), (0x11016f, 3), (0x110172, 3), (0x110175, 4), (0x110179, 3), (0x11017c, 8), (0x110184, 3), (0x110187, 3), (0x11018a, 5), (0x11018f, 3), (0x110192, 4), (0x110196, 3), (0x110199, 3), (0x11019c, 4), (0x1101a0, 5), (0x1101a5, 3), (0x1101a8, 3), (0x1101ab, 4), (0x1101af, 3), (0x1101b2, 3), (0x1101b5, 4), (0x1101b9, 3), (0x1101bc, 7), (0x1101c3, 3), (0x1101c6, 3), (0x1101c9, 3), (0x1101cc, 3), (0x1101cf, 3), (0x1101d2, 3), (0x1101d5, 3), (0x1101d8, 3), (0x1101db, 4), (0x1101df, 3), (0x1101e2, 3), (0x1101e5, 4), (0x1101e9, 3), (0x1101ec, 3), (0x1101ef, 4), (0x1101f3, 3), (0x1101f6, 3), (0x1101f9, 3), (0x1101fc, 3), (0x1101ff, 3), (0x110202, 3), (0x110205, 3), (0x110208, 3), (0x11020b, 3), (0x11020e, 3), (0x110211, 4), (0x110215, 3), (0x110218, 3), (0x11021b, 4), (0x11021f, 3), (0x110222, 3), (0x110225, 3), (0x110228, 3), (0x11022b, 4), (0x11022f, 3), (0x110232, 3), (0x110235, 4), (0x110239, 3), (0x11023c, 8), (0x110244, 3), (0x110247, 5), (0x11024c, 3), (0x11024f, 4), (0x110253, 3), (0x110256, 8), (0x11025e, 3), (0x110261, 3), (0x110264, 4), (0x110268, 3), (0x11026b, 4), (0x11026f, 3), (0x110272, 3), (0x110275, 4), (0x110279, 3), (0x11027c, 7), (0x110283, 3), (0x110286, 3), (0x110289, 3)]

theorem part39_layout [Bindings] : InstructionTrace.layout part39 = part39Layout := by
  rfl

theorem part39_ordered [Bindings] : InstructionTrace.ordered 0x110130 part39 = true := by
  rw [InstructionTrace.ordered_eq_layout, part39_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part39_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x10130 348 = part39Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
