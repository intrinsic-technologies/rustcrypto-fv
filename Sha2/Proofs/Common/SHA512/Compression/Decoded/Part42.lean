import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Common.SHA512.Compression.Layout
import Sha2.Proofs.Common.SHA512.Compression.Decoded.Part41

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA512.Compression.Decoded

open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.MemoryAlu

def part42 [Bindings] : List CheckedInstruction :=
  [
    CheckedInstruction.store (add_m64_r64_effect_step 0x11052c 0x4c (by simp [RexWPrefix]) 13 (.sib 4 none 0 (.d8 64)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110531 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x110534 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110539 0x4d 0xeb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x11053c 0x49 0xeb 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110540 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110543 0x4d 0xe7 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110546 0x4d 0xdf (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110549 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11054c 0x49 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110550 0x4d 0xc3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110553 0x49 0xc3 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110557 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11055a 0x4d 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11055d 0x49 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110561 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x110564 0x4c (by simp [RexWPrefix]) 11 (.rip 0xefc35) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11056b 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11056e 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110571 0x48 0xfe (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110574 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110577 0x4c 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11057a 0x4c 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11057d 0x49 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110580 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110583 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110586 0x48 0xc6 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11058a 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11058d 0x49 0xc1 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110591 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110594 0x48 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110597 0x48 0xc3 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11059b 0x4c 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11059e 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1105a1 0x49 0xc9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1105a4 0x48 0xc6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1105a7 0x48 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x1105aa 0x48 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1105ad 0x4c 0xce (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1105b0 0x48 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1105b3 0x4c 0xdd (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1105b6 0x4c 0xde (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1105b9 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1105bc 0x49 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1105c0 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1105c3 0x49 0xc1 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1105c7 0x4d 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1105ca 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (ror_r64_one_effect_step 0x1105cd 0x49 0xcb (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1105d0 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x1105d3 0x48 0xc3 0x38 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1105d7 0x4c 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x1105da 0x4d 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1105dd 0x49 0xeb 0x7 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1105e1 0x49 0xdb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (add_m64_r64_effect_step 0x1105e4 0x4c (by simp [RexWPrefix]) 10 (.sib 4 none 0 (.d8 80)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x1105e9 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.store (mov_m64_r64_effect_step 0x1105ec 0x4c (by simp [RexWPrefix]) 11 (.sib 4 none 0 (.d8 120)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (shr_r64_imm8_effect_step 0x1105f1 0x49 0xea 0x6 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x1105f5 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x1105f8 0x4c (by simp [RexWPrefix]) 12 (.sib 4 none 0 (.d32 144)) (by simp [AddrMode.Valid, regLow]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110600 0x4d 0xd4 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110603 0x49 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110606 0x49 0xc1 0x32 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11060a 0x49 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11060d 0x49 0xc2 0x2e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110611 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110614 0x49 0xe9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110617 0x49 0xc1 0x17 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11061b 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.load (mov_r64_m64_effect_step 0x11061e 0x4c (by simp [RexWPrefix]) 11 (.rip 0xefb83) (by simp [AddrMode.Valid]) rfl rfl) (by x86_local) (fun _ _ h => AddrMode.addr_obs h _ _),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110625 0x4d 0xe3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110628 0x4d 0xf3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11062b 0x4d 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11062e 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110631 0x49 0xea (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110634 0x49 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110637 0x4d 0xd3 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11063a 0x4d 0xcb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11063d 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110640 0x49 0xc1 0x24 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110644 0x49 0xf2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110647 0x49 0xc2 0x1e (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x11064b 0x4d 0xca (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11064e 0x49 0xf6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110651 0x49 0xc6 0x19 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110655 0x4d 0xd6 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110658 0x49 0xd2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x11065b 0x49 0xc2 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11065e 0x49 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110661 0x49 0xc1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (and_r64_r64_effect_step 0x110664 0x49 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (xor_r64_r64_effect_step 0x110667 0x4d 0xd1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11066a 0x4c 0xfb (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x11066d 0x48 0xc3 0x2d (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x110671 0x4d 0xf1 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x110674 0x4d 0xfa (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (rol_r64_imm8_effect_step 0x110677 0x49 0xc2 0x3 (by simp [RexWPrefix]) rfl rfl) (by x86_local),
    CheckedInstruction.register (add_r64_r64_effect_step 0x11067b 0x4c 0xd9 (by simp [RexWPrefix]) rfl) (by x86_local),
    CheckedInstruction.register (mov_r64_r64_effect_step 0x11067e 0x4d 0xe6 (by simp [RexWPrefix]) rfl) (by x86_local),
  ]

def part42Bytes : List UInt8 :=
  [0x4c,0x1,0x6c,0x24,0x40,0x4d,0x1,0xeb,0x4c,0x89,0x5c,0x24,0x28,0x4d,0x89,0xeb,0x49,0xc1,0xeb,0x6,0x4d,0x31,0xcb,0x4d,0x89,0xe7,0x4d,0x1,0xdf,0x4d,0x89,0xc1,0x49,0xc1,0xc1,0x32,0x4d,0x89,0xc3,0x49,0xc1,0xc3,0x2e,0x4d,0x31,0xcb,0x4d,0x89,0xc1,0x49,0xc1,0xc1,0x17,0x4d,0x31,0xd9,0x4c,0x8b,0x1d,0x35,0xfc,0xe,0x0,0x4d,0x1,0xfb,0x49,0x1,0xf3,0x48,0x89,0xfe,0x4c,0x31,0xf6,0x4c,0x21,0xc6,0x4c,0x31,0xf6,0x49,0x1,0xf3,0x4d,0x1,0xcb,0x48,0x89,0xd6,0x48,0xc1,0xc6,0x24,0x49,0x89,0xd1,0x49,0xc1,0xc1,0x1e,0x49,0x31,0xf1,0x48,0x89,0xd3,0x48,0xc1,0xc3,0x19,0x4c,0x31,0xcb,0x49,0x89,0xc1,0x49,0x21,0xc9,0x48,0x89,0xc6,0x48,0x31,0xce,0x48,0x21,0xd6,0x4c,0x31,0xce,0x48,0x1,0xde,0x4c,0x1,0xdd,0x4c,0x1,0xde,0x4d,0x89,0xd3,0x49,0xc1,0xc3,0x2d,0x4d,0x89,0xd1,0x49,0xc1,0xc1,0x3,0x4d,0x31,0xd9,0x4d,0x89,0xfb,0x49,0xd1,0xcb,0x4c,0x89,0xfb,0x48,0xc1,0xc3,0x38,0x4c,0x31,0xdb,0x4d,0x89,0xfb,0x49,0xc1,0xeb,0x7,0x49,0x31,0xdb,0x4c,0x1,0x54,0x24,0x50,0x4d,0x1,0xd3,0x4c,0x89,0x5c,0x24,0x78,0x49,0xc1,0xea,0x6,0x4d,0x31,0xca,0x4c,0x8b,0xa4,0x24,0x90,0x0,0x0,0x0,0x4d,0x1,0xd4,0x49,0x89,0xe9,0x49,0xc1,0xc1,0x32,0x49,0x89,0xea,0x49,0xc1,0xc2,0x2e,0x4d,0x31,0xca,0x49,0x89,0xe9,0x49,0xc1,0xc1,0x17,0x4d,0x31,0xd1,0x4c,0x8b,0x1d,0x83,0xfb,0xe,0x0,0x4d,0x1,0xe3,0x4d,0x1,0xf3,0x4d,0x89,0xc2,0x49,0x31,0xfa,0x49,0x21,0xea,0x49,0x31,0xfa,0x4d,0x1,0xd3,0x4d,0x1,0xcb,0x49,0x89,0xf1,0x49,0xc1,0xc1,0x24,0x49,0x89,0xf2,0x49,0xc1,0xc2,0x1e,0x4d,0x31,0xca,0x49,0x89,0xf6,0x49,0xc1,0xc6,0x19,0x4d,0x31,0xd6,0x49,0x89,0xd2,0x49,0x21,0xc2,0x49,0x89,0xd1,0x49,0x31,0xc1,0x49,0x21,0xf1,0x4d,0x31,0xd1,0x4c,0x89,0xfb,0x48,0xc1,0xc3,0x2d,0x4d,0x1,0xf1,0x4d,0x89,0xfa,0x49,0xc1,0xc2,0x3,0x4c,0x1,0xd9,0x4d,0x89,0xe6]

set_option maxRecDepth 4096 in
theorem part42_bytes [Bindings] : part42.flatMap CheckedInstruction.bytes = part42Bytes := by
  rfl

def part42Layout : List (BitVec 64 × Nat) :=
  [(0x11052c, 5), (0x110531, 3), (0x110534, 5), (0x110539, 3), (0x11053c, 4), (0x110540, 3), (0x110543, 3), (0x110546, 3), (0x110549, 3), (0x11054c, 4), (0x110550, 3), (0x110553, 4), (0x110557, 3), (0x11055a, 3), (0x11055d, 4), (0x110561, 3), (0x110564, 7), (0x11056b, 3), (0x11056e, 3), (0x110571, 3), (0x110574, 3), (0x110577, 3), (0x11057a, 3), (0x11057d, 3), (0x110580, 3), (0x110583, 3), (0x110586, 4), (0x11058a, 3), (0x11058d, 4), (0x110591, 3), (0x110594, 3), (0x110597, 4), (0x11059b, 3), (0x11059e, 3), (0x1105a1, 3), (0x1105a4, 3), (0x1105a7, 3), (0x1105aa, 3), (0x1105ad, 3), (0x1105b0, 3), (0x1105b3, 3), (0x1105b6, 3), (0x1105b9, 3), (0x1105bc, 4), (0x1105c0, 3), (0x1105c3, 4), (0x1105c7, 3), (0x1105ca, 3), (0x1105cd, 3), (0x1105d0, 3), (0x1105d3, 4), (0x1105d7, 3), (0x1105da, 3), (0x1105dd, 4), (0x1105e1, 3), (0x1105e4, 5), (0x1105e9, 3), (0x1105ec, 5), (0x1105f1, 4), (0x1105f5, 3), (0x1105f8, 8), (0x110600, 3), (0x110603, 3), (0x110606, 4), (0x11060a, 3), (0x11060d, 4), (0x110611, 3), (0x110614, 3), (0x110617, 4), (0x11061b, 3), (0x11061e, 7), (0x110625, 3), (0x110628, 3), (0x11062b, 3), (0x11062e, 3), (0x110631, 3), (0x110634, 3), (0x110637, 3), (0x11063a, 3), (0x11063d, 3), (0x110640, 4), (0x110644, 3), (0x110647, 4), (0x11064b, 3), (0x11064e, 3), (0x110651, 4), (0x110655, 3), (0x110658, 3), (0x11065b, 3), (0x11065e, 3), (0x110661, 3), (0x110664, 3), (0x110667, 3), (0x11066a, 3), (0x11066d, 4), (0x110671, 3), (0x110674, 3), (0x110677, 4), (0x11067b, 3), (0x11067e, 3)]

theorem part42_layout [Bindings] : InstructionTrace.layout part42 = part42Layout := by
  rfl

theorem part42_ordered [Bindings] : InstructionTrace.ordered 0x11052c part42 = true := by
  rw [InstructionTrace.ordered_eq_layout, part42_layout]
  decide +kernel

set_option maxRecDepth 4096 in
theorem part42_source : Sha2.Spec.Program.Extracted.textBytes.toListFrom 0x1052c 341 = part42Bytes := by
  rfl

end Sha2.Proofs.Common.SHA512.Compression.Decoded
