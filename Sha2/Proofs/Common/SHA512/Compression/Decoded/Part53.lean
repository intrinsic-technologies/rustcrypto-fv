import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part52

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part53 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1113e1 0x49 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1113e4 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1113e7 0x4d 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1113ea 0x4d 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1113ed 0x4d 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1113f0 0x49 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1113f4 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1113f7 0x4d 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1113fa 0x49 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1113fe 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111401 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111404 0x48 0xc1 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111408 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11140b 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11140e 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x111411 0x49 0xee (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111414 0x49 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111417 0x49 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11141a 0x4d 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11141d 0x4d 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111420 0x49 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111423 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111428 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11142b 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11142f 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111432 0x49 0xc6 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111436 0x49 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111439 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11143e 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x111441 0x48 0xc8 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111444 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111447 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11144a 0x48 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11144e 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111451 0x49 0xec 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111455 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.load (add_r64_m64_effect_step 0x11145a 0x48 (by simp [RexWPrefix]) 0 (.rip 0xeee17) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111461 0x49 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111464 0x4c 0xe0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x111467 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11146c 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x11146f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111474 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111477 0x48 0xe8 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11147b 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11147e 0x48 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111482 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111485 0x49 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111488 0x49 0xc6 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11148c 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111491 0x49 0xc4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111494 0x48 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111497 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11149b 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11149e 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1114a1 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1114a4 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1114a7 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1114aa 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1114ad 0x48 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1114b0 0x48 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1114b3 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1114b6 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1114b9 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1114bd 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1114c0 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1114c3 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1114c7 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1114ca 0x4c 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1114cd 0x48 0xc1 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1114d1 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1114d4 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1114d7 0x48 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1114da 0x4d 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1114dd 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1114e0 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1114e3 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1114e6 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1114e9 0x4c 0xd5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1114ec 0x4c (by simp [RexWPrefix]) 14 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1114f0 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1114f3 0x48 0xc0 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1114f7 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1114fa 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1114fd 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111501 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x111504 0x49 0xee 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111508 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11150b 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111510 0x4d 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111513 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111516 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11151a 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11151d 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x111521 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x111524 0x48 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x111527 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11152b 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11152e 0x4c 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x111531 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part53Bytes : List UInt8 :=
  [0x49,0x89,0xd0,0x4d,0x31,0xc8,0x4d,0x21,0xd8,0x4d,0x31,0xc8,0x4d,0x89,0xee,0x49,0xc1,0xc6,0x24,0x4c,0x1,0xc0,0x4d,0x89,0xe8,0x49,0xc1,0xc0,0x1e,0x48,0x1,0xc8,0x4c,0x89,0xe9,0x48,0xc1,0xc1,0x19,0x4d,0x31,0xf0,0x4c,0x31,0xc1,0x49,0x89,0xfe,0x49,0x21,0xee,0x49,0x89,0xf8,0x49,0x31,0xe8,0x4d,0x21,0xe8,0x4d,0x31,0xf0,0x49,0x1,0xc8,0x4c,0x8b,0x74,0x24,0x8,0x4c,0x89,0xf1,0x48,0xc1,0xc1,0x2d,0x48,0x1,0xc3,0x49,0xc1,0xc6,0x3,0x49,0x1,0xc0,0x4c,0x8b,0x64,0x24,0x10,0x4c,0x89,0xe0,0x48,0xd1,0xc8,0x49,0x31,0xce,0x4c,0x89,0xe1,0x48,0xc1,0xc1,0x38,0x48,0x31,0xc1,0x49,0xc1,0xec,0x7,0x48,0x8b,0x44,0x24,0x18,0x48,0x3,0x5,0x17,0xee,0xe,0x0,0x49,0x31,0xcc,0x4c,0x1,0xe0,0x48,0x8b,0x4c,0x24,0x8,0x48,0x1,0xc8,0x48,0x89,0x44,0x24,0x18,0x48,0x89,0xc8,0x48,0xc1,0xe8,0x6,0x48,0x89,0xd9,0x48,0xc1,0xc1,0x32,0x4c,0x31,0xf0,0x49,0x89,0xde,0x49,0xc1,0xc6,0x2e,0x4c,0x8b,0x64,0x24,0x50,0x49,0x1,0xc4,0x48,0x89,0xd8,0x48,0xc1,0xc0,0x17,0x49,0x31,0xce,0x4c,0x31,0xf0,0x4d,0x1,0xe2,0x4d,0x1,0xca,0x4c,0x89,0xd9,0x48,0x31,0xd1,0x48,0x21,0xd9,0x48,0x31,0xd1,0x49,0x1,0xca,0x4c,0x89,0xc1,0x48,0xc1,0xc1,0x24,0x49,0x1,0xc2,0x4c,0x89,0xc0,0x48,0xc1,0xc0,0x1e,0x48,0x31,0xc8,0x4c,0x89,0xc1,0x48,0xc1,0xc1,0x19,0x48,0x31,0xc1,0x4c,0x89,0xe8,0x48,0x21,0xf8,0x4d,0x89,0xe9,0x49,0x31,0xf9,0x4d,0x21,0xc1,0x49,0x31,0xc1,0x49,0x1,0xc9,0x4c,0x1,0xd5,0x4c,0x8b,0x34,0x24,0x4c,0x89,0xf0,0x48,0xc1,0xc0,0x2d,0x4d,0x1,0xd1,0x4c,0x89,0xf1,0x48,0xc1,0xc1,0x3,0x48,0x31,0xc1,0x49,0xc1,0xee,0x6,0x49,0x31,0xce,0x4c,0x8b,0x54,0x24,0x48,0x4d,0x1,0xf2,0x48,0x89,0xe8,0x48,0xc1,0xc0,0x32,0x48,0x89,0xe9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x48,0x89,0xe8,0x48,0xc1,0xc0,0x17,0x48,0x31,0xc8,0x4c,0x1,0xd6,0x48,0x1,0xd6]

set_option maxRecDepth 4096 in
theorem part53_bytes [Bindings] : part53.flatMap CheckedInstruction.bytes = part53Bytes := by
  rfl

def part53Layout : List (BitVec 64 × Nat) :=
  [(0x1113e1, 3), (0x1113e4, 3), (0x1113e7, 3), (0x1113ea, 3), (0x1113ed, 3), (0x1113f0, 4), (0x1113f4, 3), (0x1113f7, 3), (0x1113fa, 4), (0x1113fe, 3), (0x111401, 3), (0x111404, 4), (0x111408, 3), (0x11140b, 3), (0x11140e, 3), (0x111411, 3), (0x111414, 3), (0x111417, 3), (0x11141a, 3), (0x11141d, 3), (0x111420, 3), (0x111423, 5), (0x111428, 3), (0x11142b, 4), (0x11142f, 3), (0x111432, 4), (0x111436, 3), (0x111439, 5), (0x11143e, 3), (0x111441, 3), (0x111444, 3), (0x111447, 3), (0x11144a, 4), (0x11144e, 3), (0x111451, 4), (0x111455, 5), (0x11145a, 7), (0x111461, 3), (0x111464, 3), (0x111467, 5), (0x11146c, 3), (0x11146f, 5), (0x111474, 3), (0x111477, 4), (0x11147b, 3), (0x11147e, 4), (0x111482, 3), (0x111485, 3), (0x111488, 4), (0x11148c, 5), (0x111491, 3), (0x111494, 3), (0x111497, 4), (0x11149b, 3), (0x11149e, 3), (0x1114a1, 3), (0x1114a4, 3), (0x1114a7, 3), (0x1114aa, 3), (0x1114ad, 3), (0x1114b0, 3), (0x1114b3, 3), (0x1114b6, 3), (0x1114b9, 4), (0x1114bd, 3), (0x1114c0, 3), (0x1114c3, 4), (0x1114c7, 3), (0x1114ca, 3), (0x1114cd, 4), (0x1114d1, 3), (0x1114d4, 3), (0x1114d7, 3), (0x1114da, 3), (0x1114dd, 3), (0x1114e0, 3), (0x1114e3, 3), (0x1114e6, 3), (0x1114e9, 3), (0x1114ec, 4), (0x1114f0, 3), (0x1114f3, 4), (0x1114f7, 3), (0x1114fa, 3), (0x1114fd, 4), (0x111501, 3), (0x111504, 4), (0x111508, 3), (0x11150b, 5), (0x111510, 3), (0x111513, 3), (0x111516, 4), (0x11151a, 3), (0x11151d, 4), (0x111521, 3), (0x111524, 3), (0x111527, 4), (0x11152b, 3), (0x11152e, 3), (0x111531, 3)]

theorem part53_layout [Bindings] : InstructionTrace.layout part53 = part53Layout := by
  rfl

theorem part53_ordered [Bindings] : InstructionTrace.ordered 0x1113e1 part53 = true := by
  rw [InstructionTrace.ordered_eq_layout, part53_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part53_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x113e1 339 = part53Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
