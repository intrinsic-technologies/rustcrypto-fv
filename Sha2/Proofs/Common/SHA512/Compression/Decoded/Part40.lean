import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part39

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part40 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11028c 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11028f 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110292 0x48 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110295 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110298 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11029b 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11029e 0x49 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102a2 0x4c 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1102a5 0x48 0xc3 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1102a9 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102ac 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1102af 0x49 0xc1 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1102b3 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102b6 0x48 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1102b9 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102bc 0x48 0xfd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1102bf 0x4c 0xf5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1102c2 0x4c 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1102c5 0x48 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1102c8 0x4c 0xcd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1102cb 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1102ce 0x4c 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102d1 0x4d 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102d4 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1102d7 0x49 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102db 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1102de 0x49 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1102e2 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102e5 0x49 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102e8 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x1102eb 0x49 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1102ee 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1102f1 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1102f5 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1102f8 0x48 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1102fc 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x1102ff 0x4c (by simp [RexWPrefix]) 15 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110303 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110306 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11030b 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11030e 0x49 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110312 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110315 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11031a 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11031d 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110320 0x49 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110324 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110327 0x49 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11032b 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11032e 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110331 0x49 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110335 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110338 0x4c (by simp [RexWPrefix]) 11 (.rip 0xefe49) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11033f 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110342 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110345 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110348 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11034b 0x48 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11034e 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110351 0x49 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110354 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110357 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11035a 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11035e 0x49 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110361 0x49 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110365 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110368 0x49 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11036b 0x49 0xc7 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11036f 0x4d 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110372 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110375 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110378 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11037b 0x48 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11037e 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110381 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110384 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110387 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11038b 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11038e 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110391 0x49 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110395 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110398 0x49 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x11039b 0x48 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11039e 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1103a1 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1103a4 0x49 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1103a8 0x49 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1103ab 0x49 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1103ae 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1103b1 0x48 0xe8 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1103b5 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x1103b8 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 56)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1103bd 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1103c0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1103c5 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1103c8 0x49 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1103cc 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1103cf 0x48 0xc3 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1103d3 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1103d6 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part40Bytes : List UInt8 :=
  [0x48,0x31,0xcb,0x48,0x21,0xd3,0x48,0x31,0xcb,0x49,0x1,0xdb,0x4d,0x1,0xcb,0x4d,0x89,0xc1,0x49,0xc1,0xc1,0x24,0x4c,0x89,0xc3,0x48,0xc1,0xc3,0x1e,0x4c,0x31,0xcb,0x4d,0x89,0xc1,0x49,0xc1,0xc1,0x19,0x49,0x31,0xd9,0x48,0x89,0xfb,0x4c,0x21,0xf3,0x48,0x89,0xfd,0x4c,0x31,0xf5,0x4c,0x21,0xc5,0x48,0x31,0xdd,0x4c,0x1,0xcd,0x4c,0x1,0xde,0x4c,0x1,0xdd,0x4d,0x89,0xef,0x4d,0x89,0xeb,0x49,0xc1,0xc3,0x2d,0x4d,0x89,0xe9,0x49,0xc1,0xc1,0x3,0x4d,0x31,0xd9,0x49,0x89,0xc5,0x49,0x89,0xc3,0x49,0xd1,0xcb,0x48,0x89,0xc3,0x48,0xc1,0xc3,0x38,0x4c,0x31,0xdb,0x48,0xc1,0xe8,0x7,0x48,0x31,0xd8,0x4c,0x1,0x3c,0x24,0x4c,0x1,0xf8,0x48,0x89,0x44,0x24,0x18,0x4d,0x89,0xfb,0x49,0xc1,0xeb,0x6,0x4d,0x31,0xcb,0x48,0x8b,0x44,0x24,0x58,0x4c,0x1,0xd8,0x49,0x89,0xf1,0x49,0xc1,0xc1,0x32,0x49,0x89,0xf3,0x49,0xc1,0xc3,0x2e,0x4d,0x31,0xcb,0x49,0x89,0xf1,0x49,0xc1,0xc1,0x17,0x4d,0x31,0xd9,0x4c,0x8b,0x1d,0x49,0xfe,0xe,0x0,0x49,0x1,0xc3,0x49,0x1,0xcb,0x48,0x89,0xd1,0x4c,0x31,0xd1,0x48,0x21,0xf1,0x4c,0x31,0xd1,0x49,0x1,0xcb,0x4d,0x1,0xcb,0x48,0x89,0xe9,0x48,0xc1,0xc1,0x24,0x49,0x89,0xe9,0x49,0xc1,0xc1,0x1e,0x49,0x31,0xc9,0x49,0x89,0xef,0x49,0xc1,0xc7,0x19,0x4d,0x31,0xcf,0x4d,0x89,0xc1,0x49,0x21,0xf9,0x4c,0x89,0xc1,0x48,0x31,0xf9,0x48,0x21,0xe9,0x4c,0x31,0xc9,0x4c,0x89,0xeb,0x48,0xc1,0xc3,0x2d,0x4c,0x1,0xf9,0x4d,0x89,0xe9,0x49,0xc1,0xc1,0x3,0x4d,0x1,0xde,0x49,0x89,0xc7,0x48,0xd1,0xc8,0x4c,0x1,0xd9,0x4d,0x89,0xfb,0x49,0xc1,0xc3,0x38,0x49,0x31,0xd9,0x49,0x31,0xc3,0x4c,0x89,0xf8,0x48,0xc1,0xe8,0x7,0x4c,0x31,0xd8,0x4c,0x1,0x6c,0x24,0x38,0x4c,0x1,0xe8,0x48,0x89,0x44,0x24,0x10,0x4d,0x89,0xeb,0x49,0xc1,0xeb,0x6,0x4c,0x89,0xf3,0x48,0xc1,0xc3,0x32,0x4d,0x31,0xcb,0x4d,0x89,0xf1]

set_option maxRecDepth 4096 in
theorem part40_bytes [Bindings] : part40.flatMap CheckedInstruction.bytes = part40Bytes := by
  rfl

def part40Layout : List (BitVec 64 × Nat) :=
  [(0x11028c, 3), (0x11028f, 3), (0x110292, 3), (0x110295, 3), (0x110298, 3), (0x11029b, 3), (0x11029e, 4), (0x1102a2, 3), (0x1102a5, 4), (0x1102a9, 3), (0x1102ac, 3), (0x1102af, 4), (0x1102b3, 3), (0x1102b6, 3), (0x1102b9, 3), (0x1102bc, 3), (0x1102bf, 3), (0x1102c2, 3), (0x1102c5, 3), (0x1102c8, 3), (0x1102cb, 3), (0x1102ce, 3), (0x1102d1, 3), (0x1102d4, 3), (0x1102d7, 4), (0x1102db, 3), (0x1102de, 4), (0x1102e2, 3), (0x1102e5, 3), (0x1102e8, 3), (0x1102eb, 3), (0x1102ee, 3), (0x1102f1, 4), (0x1102f5, 3), (0x1102f8, 4), (0x1102fc, 3), (0x1102ff, 4), (0x110303, 3), (0x110306, 5), (0x11030b, 3), (0x11030e, 4), (0x110312, 3), (0x110315, 5), (0x11031a, 3), (0x11031d, 3), (0x110320, 4), (0x110324, 3), (0x110327, 4), (0x11032b, 3), (0x11032e, 3), (0x110331, 4), (0x110335, 3), (0x110338, 7), (0x11033f, 3), (0x110342, 3), (0x110345, 3), (0x110348, 3), (0x11034b, 3), (0x11034e, 3), (0x110351, 3), (0x110354, 3), (0x110357, 3), (0x11035a, 4), (0x11035e, 3), (0x110361, 4), (0x110365, 3), (0x110368, 3), (0x11036b, 4), (0x11036f, 3), (0x110372, 3), (0x110375, 3), (0x110378, 3), (0x11037b, 3), (0x11037e, 3), (0x110381, 3), (0x110384, 3), (0x110387, 4), (0x11038b, 3), (0x11038e, 3), (0x110391, 4), (0x110395, 3), (0x110398, 3), (0x11039b, 3), (0x11039e, 3), (0x1103a1, 3), (0x1103a4, 4), (0x1103a8, 3), (0x1103ab, 3), (0x1103ae, 3), (0x1103b1, 4), (0x1103b5, 3), (0x1103b8, 5), (0x1103bd, 3), (0x1103c0, 5), (0x1103c5, 3), (0x1103c8, 4), (0x1103cc, 3), (0x1103cf, 4), (0x1103d3, 3), (0x1103d6, 3)]

theorem part40_layout [Bindings] : InstructionTrace.layout part40 = part40Layout := by
  rfl

theorem part40_ordered [Bindings] : InstructionTrace.ordered 0x11028c part40 = true := by
  rw [InstructionTrace.ordered_eq_layout, part40_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part40_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x1028c 333 = part40Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
