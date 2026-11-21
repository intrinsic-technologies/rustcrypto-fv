import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part44

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part45 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.register (add_r64_r64_effect_step 0x11092a 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11092d 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110930 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110934 0x4d 0xda (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110937 0x49 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11093b 0x49 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11093e 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110941 0x48 0xc1 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110945 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110948 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11094b 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11094e 0x4d 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110951 0x4d 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110954 0x4d 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110957 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11095a 0x49 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11095d 0x49 0xc2 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110961 0x49 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110964 0x48 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110967 0x48 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11096b 0x49 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11096e 0x4c 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110971 0x48 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110974 0x49 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110977 0x4c 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11097a 0x48 0xc7 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11097e 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110981 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110984 0x4d 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110987 0x49 0xea 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11098b 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x11098e 0x48 (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110993 0x49 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110996 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 8)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11099b 0x48 0xef (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11099e 0x48 0xef 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1109a2 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1109a5 0x49 0xc2 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1109a9 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1109ac 0x4c 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1109af 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1109b3 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1109b8 0x49 0xfc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1109bb 0x4c 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1109be 0x48 0xc7 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1109c2 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1109c5 0x48 0xcf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1109c8 0x4c (by simp [RexWPrefix]) 10 (.rip 0xef801) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1109cf 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1109d2 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1109d5 0x48 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1109d8 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1109db 0x4c 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1109de 0x48 0xd0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1109e1 0x4c 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1109e4 0x48 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1109e8 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1109eb 0x4c 0xf0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1109ee 0x48 0xc0 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1109f2 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1109f5 0x4c 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1109f8 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1109fc 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1109ff 0x48 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a02 0x4c 0xd8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110a05 0x4c 0xc0 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a08 0x4c 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a0b 0x4c 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110a0e 0x4c 0xf7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a11 0x48 0xc7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110a14 0x48 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a17 0x4c 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110a1a 0x48 0xc1 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110a1e 0x4d 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a21 0x4c 0xe8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110a24 0x48 0xc0 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110a28 0x4c 0xd7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a2b 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x110a2e 0x49 0xca (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a31 0x48 0xc8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a34 0x4c 0xe1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110a37 0x48 0xc1 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a3b 0x4c 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a3e 0x4d 0xe2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110a41 0x49 0xec 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a45 0x49 0xcc (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x110a48 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110a4d 0x4d 0xec (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110a50 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 .none) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x110a54 0x49 0xed 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a58 0x49 0xc5 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a5b 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110a5e 0x48 0xc0 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110a62 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d8 72)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110a67 0x4d 0xec (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a6a 0x4c 0xf9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110a6d 0x48 0xc1 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110a71 0x48 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110a74 0x4c 0xf8 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110a77 0x48 0xc0 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
  ]

def part45Bytes : List UInt8 :=
  [0x48,0x1,0xdf,0x4c,0x89,0xd9,0x48,0xc1,0xc1,0x24,0x4d,0x89,0xda,0x49,0xc1,0xc2,0x1e,0x49,0x31,0xca,0x4c,0x89,0xd9,0x48,0xc1,0xc1,0x19,0x4c,0x31,0xd1,0x4d,0x89,0xc2,0x4d,0x21,0xfa,0x4d,0x89,0xc6,0x4d,0x31,0xfe,0x4d,0x21,0xde,0x4d,0x31,0xd6,0x49,0x89,0xea,0x49,0xc1,0xc2,0x2d,0x49,0x1,0xce,0x48,0x89,0xe9,0x48,0xc1,0xc1,0x3,0x49,0x1,0xf9,0x4c,0x89,0xeb,0x48,0xd1,0xcb,0x49,0x1,0xfe,0x4c,0x89,0xef,0x48,0xc1,0xc7,0x38,0x4c,0x31,0xd1,0x48,0x31,0xdf,0x4d,0x89,0xea,0x49,0xc1,0xea,0x7,0x49,0x31,0xfa,0x48,0x1,0x6c,0x24,0x18,0x49,0x1,0xea,0x4c,0x89,0x54,0x24,0x8,0x48,0x89,0xef,0x48,0xc1,0xef,0x6,0x4d,0x89,0xca,0x49,0xc1,0xc2,0x32,0x48,0x31,0xcf,0x4c,0x89,0xc9,0x48,0xc1,0xc1,0x2e,0x4c,0x8b,0x64,0x24,0x50,0x49,0x1,0xfc,0x4c,0x89,0xcf,0x48,0xc1,0xc7,0x17,0x4c,0x31,0xd1,0x48,0x31,0xcf,0x4c,0x8b,0x15,0x1,0xf8,0xe,0x0,0x4d,0x1,0xe2,0x49,0x1,0xc2,0x48,0x89,0xf0,0x48,0x31,0xd0,0x4c,0x21,0xc8,0x48,0x31,0xd0,0x4c,0x89,0xf1,0x48,0xc1,0xc1,0x24,0x49,0x1,0xc2,0x4c,0x89,0xf0,0x48,0xc1,0xc0,0x1e,0x49,0x1,0xfa,0x4c,0x89,0xf3,0x48,0xc1,0xc3,0x19,0x48,0x31,0xc8,0x48,0x31,0xc3,0x4c,0x89,0xd8,0x4c,0x21,0xc0,0x4c,0x89,0xdf,0x4c,0x31,0xc7,0x4c,0x21,0xf7,0x48,0x31,0xc7,0x48,0x1,0xdf,0x4c,0x89,0xe9,0x48,0xc1,0xc1,0x2d,0x4d,0x1,0xd7,0x4c,0x89,0xe8,0x48,0xc1,0xc0,0x3,0x4c,0x1,0xd7,0x4d,0x89,0xe2,0x49,0xd1,0xca,0x48,0x31,0xc8,0x4c,0x89,0xe1,0x48,0xc1,0xc1,0x38,0x4c,0x31,0xd1,0x4d,0x89,0xe2,0x49,0xc1,0xec,0x7,0x49,0x31,0xcc,0x4c,0x1,0x6c,0x24,0x10,0x4d,0x1,0xec,0x4c,0x89,0x24,0x24,0x49,0xc1,0xed,0x6,0x49,0x31,0xc5,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x32,0x4c,0x8b,0x64,0x24,0x48,0x4d,0x1,0xec,0x4c,0x89,0xf9,0x48,0xc1,0xc1,0x2e,0x48,0x31,0xc1,0x4c,0x89,0xf8,0x48,0xc1,0xc0,0x17]

set_option maxRecDepth 4096 in
theorem part45_bytes [Bindings] : part45.flatMap CheckedInstruction.bytes = part45Bytes := by
  rfl

def part45Layout : List (BitVec 64 × Nat) :=
  [(0x11092a, 3), (0x11092d, 3), (0x110930, 4), (0x110934, 3), (0x110937, 4), (0x11093b, 3), (0x11093e, 3), (0x110941, 4), (0x110945, 3), (0x110948, 3), (0x11094b, 3), (0x11094e, 3), (0x110951, 3), (0x110954, 3), (0x110957, 3), (0x11095a, 3), (0x11095d, 4), (0x110961, 3), (0x110964, 3), (0x110967, 4), (0x11096b, 3), (0x11096e, 3), (0x110971, 3), (0x110974, 3), (0x110977, 3), (0x11097a, 4), (0x11097e, 3), (0x110981, 3), (0x110984, 3), (0x110987, 4), (0x11098b, 3), (0x11098e, 5), (0x110993, 3), (0x110996, 5), (0x11099b, 3), (0x11099e, 4), (0x1109a2, 3), (0x1109a5, 4), (0x1109a9, 3), (0x1109ac, 3), (0x1109af, 4), (0x1109b3, 5), (0x1109b8, 3), (0x1109bb, 3), (0x1109be, 4), (0x1109c2, 3), (0x1109c5, 3), (0x1109c8, 7), (0x1109cf, 3), (0x1109d2, 3), (0x1109d5, 3), (0x1109d8, 3), (0x1109db, 3), (0x1109de, 3), (0x1109e1, 3), (0x1109e4, 4), (0x1109e8, 3), (0x1109eb, 3), (0x1109ee, 4), (0x1109f2, 3), (0x1109f5, 3), (0x1109f8, 4), (0x1109fc, 3), (0x1109ff, 3), (0x110a02, 3), (0x110a05, 3), (0x110a08, 3), (0x110a0b, 3), (0x110a0e, 3), (0x110a11, 3), (0x110a14, 3), (0x110a17, 3), (0x110a1a, 4), (0x110a1e, 3), (0x110a21, 3), (0x110a24, 4), (0x110a28, 3), (0x110a2b, 3), (0x110a2e, 3), (0x110a31, 3), (0x110a34, 3), (0x110a37, 4), (0x110a3b, 3), (0x110a3e, 3), (0x110a41, 4), (0x110a45, 3), (0x110a48, 5), (0x110a4d, 3), (0x110a50, 4), (0x110a54, 4), (0x110a58, 3), (0x110a5b, 3), (0x110a5e, 4), (0x110a62, 5), (0x110a67, 3), (0x110a6a, 3), (0x110a6d, 4), (0x110a71, 3), (0x110a74, 3), (0x110a77, 4)]

theorem part45_layout [Bindings] : InstructionTrace.layout part45 = part45Layout := by
  rfl

theorem part45_ordered [Bindings] : InstructionTrace.ordered 0x11092a part45 = true := by
  rw [InstructionTrace.ordered_eq_layout, part45_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part45_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x1092a 337 = part45Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
